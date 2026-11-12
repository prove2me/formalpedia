-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:18:07.794401+00:00
-- url     : https://prove2.me/submissions/283131ca-42c5-4a01-947e-a42ccca880c7

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P011
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_groundFairPreparationOrbit
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_dense_mixture_equalities
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralFairPreparation_supported_lower_bound

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

theorem eval_rename (t : Presentation Q) (f : P → Q) (H : Set Q) (τ : Name s) :
    eval H (rename t f τ) = eval {p | f p ∈ H} τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro x
    rw [mem_eval, mem_eval]
    constructor
    · rintro ⟨ν, q, h, hq, eq⟩
      obtain ⟨σ, p, hp, rfl, rfl⟩ := (entry_rename t f τ ν q).1 h
      exact ⟨σ, p, hp, hq, (ih σ p hp).symm.trans eq⟩
    · rintro ⟨σ, p, hp, hq, eq⟩
      exact ⟨rename t f σ, f p,
        (entry_rename t f τ _ _).2 ⟨σ, p, hp, rfl, rfl⟩,
        hq, (ih σ p hp).trans eq⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem stabilizer_conjugation (g : G) (τ : Name s) :
    a.stabilizer s (a.act s g τ) = (a.stabilizer s τ).map (conjugateHom g) := by
  apply Subgroup.ext
  intro h
  constructor
  · intro fixed
    let k := g⁻¹ * h * g
    have eq : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
    refine Subgroup.mem_map.2 ⟨k, ?_, eq⟩
    change a.act s (g⁻¹ * h * g) τ = τ
    rw [a.act_mul, a.act_mul]
    change a.act s h (a.act s g τ) = a.act s g τ at fixed
    rw [fixed, a.act_inv_left]
  · intro member
    obtain ⟨k, fixed, rfl⟩ := Subgroup.mem_map.1 member
    change a.act s (g * k * g⁻¹) (a.act s g τ) = a.act s g τ
    change a.act s k τ = τ at fixed
    rw [a.act_mul, a.act_mul, a.act_inv_left, fixed]

end PosetAction
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u v w
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

namespace HereditarilySymmetric
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem translated {τ : Name s} (h : HereditarilySymmetric a s F τ) (g : G) :
    HereditarilySymmetric a s F (a.act s g τ) := by
  induction τ using Name.inductionOn with
  | step τ ih =>
    refine HereditarilySymmetric.mk ?_ ?_
    · rw [a.stabilizer_conjugation]
      exact F.conjugate g h.symmetric
    · intro ν p entry
      change Name.Entry ν (Name.rename s (a.iso g) τ) p at entry
      obtain ⟨σ, q, hσ, rfl, _⟩ := (Name.entry_rename s (a.iso g) τ ν p).1 entry
      exact ih σ q hσ (h.member hσ)

end HereditarilySymmetric
end PartitionPilot.Forcing


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameMixingRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

theorem entry_nameRank_lt {σ τ : Name s} {p : P} (h : Entry σ τ p) :
    nameRank σ < nameRank τ :=
  ZFSet.rank_lt_of_mem ((mem_eval Set.univ τ _).2 ⟨σ, p, h, Set.mem_univ _, rfl⟩)

theorem nameRank_rename (t : Presentation Q) (f : P → Q) (τ : Name s) :
    nameRank (rename t f τ) = nameRank τ := by
  unfold nameRank
  rw [eval_rename]
  rfl

theorem rank_eval_le (H : Set P) (τ : Name s) : ZFSet.rank (eval H τ) ≤ nameRank τ := by
  induction τ using inductionOn with
  | step τ ih =>
    rw [ZFSet.rank_le_iff]
    intro x hx
    obtain ⟨σ, p, entry, _, rfl⟩ := (mem_eval H τ x).1 hx
    exact (ih σ p entry).trans_lt (entry_nameRank_lt entry)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] [Small.{u} G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem entry_mix (K : Subgroup G) (p : P) (τ σ : Name s) (q : P) :
    Name.Entry σ (a.mix s K p τ) q ↔
      ∃ g ∈ K, ∃ ν r, Name.Entry ν τ r ∧ a.act s g ν = σ ∧
        q ≤ a.iso g p ∧ q ≤ a.iso g r := by
  rw [mix, Name.entry_assemble]
  constructor
  · rintro ⟨z, eq, rfl⟩
    exact ⟨z.val.1.val, z.val.1.property, z.val.2.1.val.1, z.val.2.1.val.2,
      z.val.2.1.property, eq, z.property⟩
  · rintro ⟨g, hg, ν, r, entry, eq, lower⟩
    exact ⟨⟨(⟨g, hg⟩, ⟨(ν, r), entry⟩, q), lower⟩, eq, rfl⟩

theorem mix_entry_translated (K : Subgroup G) (p : P) (τ : Name s)
    {σ : Name s} {q : P} (entry : Name.Entry σ (a.mix s K p τ) q)
    {h : G} (hh : h ∈ K) :
    Name.Entry (a.act s h σ) (a.mix s K p τ) (a.iso h q) := by
  obtain ⟨g, hg, ν, r, old, eq, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
  apply (a.entry_mix s K p τ _ _).2
  refine ⟨h * g, K.mul_mem hh hg, ν, r, old, ?_, ?_, ?_⟩
  · rw [a.act_mul, eq]
  · rw [a.mul]
    exact (a.iso h).monotone qp
  · rw [a.mul]
    exact (a.iso h).monotone qr

theorem mix_fixed (K : Subgroup G) (p : P) (τ : Name s) {g : G} (hg : g ∈ K) :
    a.act s g (a.mix s K p τ) = a.mix s K p τ := by
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename s (a.iso g) (a.mix s K p τ)) q ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, r, entry, eq, hr⟩
    change a.act s g ν = σ at eq
    have h := a.mix_entry_translated s K p τ entry hg
    simpa only [eq, hr] using h
  · intro entry
    have moved := a.mix_entry_translated s K p τ entry (K.inv_mem hg)
    refine ⟨a.act s g⁻¹ σ, a.iso g⁻¹ q, moved, a.act_inv_right s g σ, ?_⟩
    rw [← a.mul, mul_inv_cancel, a.one]

end PartitionPilot.Forcing.PosetAction


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem nameRank_act (g : G) (τ : Name s) :
    Name.nameRank (a.act s g τ) = Name.nameRank τ :=
  Name.nameRank_rename s (a.iso g) τ

end PartitionPilot.Forcing.PosetAction

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameOrbitBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_orbitCodes (D : Name.NameDomain s) (W y : ZFSet.{u}) :
    y ∈ a.orbitCodes s D W ↔ ∃ g σ, σ ∈ D.names ∧ σ.val ∈ W ∧ y = (a.act s g σ).val := by
  rw [orbitCodes, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨g, σ⟩, eq⟩
    exact ⟨g, σ.val.val, σ.val.property, σ.property, eq.symm⟩
  · rintro ⟨g, σ, hσ, hW, eq⟩
    exact ⟨(g, ⟨⟨σ, hσ⟩, hW⟩), eq.symm⟩

end PartitionPilot.Forcing.PosetAction

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundContainmentOrders
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem decoded_order_mem {Q R : ZFSet.{u}} (h : PartialOrderCode Q R) (hR : R ∈ M.sets) :
    letI _decodedOrder := h.toPartialOrder
    (SetMembers.presentation Q).conditionOrder ∈ M.sets := by
  let decodedOrder := h.toPartialOrder
  rw [h.conditionOrder_eq]
  exact hR

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundGraphValueDescendantWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem mem_immediateChildCodes (τ : Name s) (y : ZFSet.{u}) :
    y ∈ immediateChildCodes τ ↔ ∃ σ : Name s, ∃ p, Entry σ τ p ∧ y = σ.val := by
  rw [immediateChildCodes, mem_relationImage]
  constructor
  · rintro ⟨_, q, _, entry⟩
    have raw := ((pair_mem_relationConverse _ _ _ y q).1 entry).2.2
    obtain ⟨σ, p, shape⟩ := entries_cover τ raw
    refine ⟨σ, p, ?_, (ZFSet.pair_inj.1 shape).1⟩
    change ZFSet.pair σ.val (s.encode p) ∈ τ.val
    rw [← shape]
    exact raw
  · rintro ⟨σ, p, entry, rfl⟩
    have bound := child_mem_doubleUnion entry
    exact ⟨bound, s.encode p, s.encode_mem p,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨bound, s.encode_mem p, entry⟩⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem immediateChildCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (τ : Name s) (ground : τ.val ∈ M.sets) :
    Name.immediateChildCodes τ ∈ M.sets := by
  have bound := M.union_mem unions (M.union_mem unions ground)
  exact M.relationImage_mem separation carrier bound
    (M.relationConverse_mem pairing unions powers separation bound carrier ground)

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_OrbitImageFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_codedNameActionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (g : G) (x y : ZFSet.{u}) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets codedNameActionFormula (extend (t.encode g) (extend x (extend y
      (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      ∃ σ : (M.nameDomain s).names, σ.val.val = x ∧ y = (a.act s g σ.val).val := by
  rw [codedNameActionFormula]
  change (Realize M.sets _ _ ∧ Realize M.sets _ _ ∧ Realize M.sets _ _) ↔ _
  simp only [realize_domainApplication, map_extend, map_empty]
  constructor
  · rintro ⟨nameX, nameY, action⟩
    have nx := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier x hx).1 nameX
    have ny := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier y hy).1 nameY
    have eq := (M.realize_nameActionFormula a s t pairing unions powers separation collection carrier group maps
      g ⟨x, nx⟩ ⟨y, ny⟩ hx hy).1 action
    exact ⟨⟨⟨x, nx⟩, hx⟩, rfl, (congrArg Subtype.val eq).symm⟩
  · rintro ⟨σ, rfl, rfl⟩
    refine ⟨(M.realize_uniformNameFormula s pairing unions powers separation collection carrier _ hx).2 σ.val.property,
      (M.realize_uniformNameFormula s pairing unions powers separation collection carrier _ hy).2
        (a.act s g σ.val).property, ?_⟩
    exact (M.realize_nameActionFormula a s t pairing unions powers separation collection carrier group maps
      g σ.val (a.act s g σ.val) hx hy).2 rfl

theorem realize_orbitImageFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W z y : ZFSet.{u}) (hz : z ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets orbitImageFormula (extend z (extend y (orbitParameters a s t W))) ↔
      ∃ g, ∃ σ : (M.nameDomain s).names, σ.val.val ∈ W ∧
        z = ZFSet.pair (t.encode g) σ.val.val ∧ y = (a.act s g σ.val).val := by
  rw [orbitImageFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨g, member, shape, action⟩ := (M.realize_exConditions t 5 _
      (extend x (extend z (extend y (orbitParameters a s t W)))) group rfl).1 rest
    rw [realize_atomicApplication, map_extend, map_extend, map_empty] at action
    obtain ⟨σ, eq, output⟩ := (M.realize_codedNameActionFormula a s t pairing unions powers separation collection
      carrier group maps g x y hx hy).1 action
    have raw := (M.realize_orderedPairFormula pairing 2 0 1
      (extend (t.encode g) (extend x (extend z (extend y (orbitParameters a s t W))))) hz
      (M.transitive group (t.encode_mem g)) hx).1 shape
    exact ⟨g, σ, eq.symm ▸ member, raw.trans (congrArg (ZFSet.pair (t.encode g)) eq.symm), output⟩
  · rintro ⟨g, σ, member, shape, output⟩
    refine ⟨σ.val.val, σ.property, ?_⟩
    apply (M.realize_exConditions t 5 _
      (extend σ.val.val (extend z (extend y (orbitParameters a s t W)))) group rfl).2
    refine ⟨g, member, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 2 0 1
        (extend (t.encode g) (extend σ.val.val (extend z (extend y (orbitParameters a s t W))))) hz
        (M.transitive group (t.encode_mem g)) σ.property).2 shape
    · rw [realize_atomicApplication, map_extend, map_extend, map_empty]
      exact (M.realize_codedNameActionFormula a s t pairing unions powers separation collection
        carrier group maps g σ.val.val y σ.property hy).2 ⟨σ, rfl, output⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMixtureTermBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem orbitCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) : a.orbitCodes s (M.nameDomain s) W ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers group hW
  apply M.definable_image_mem separation collection orbitImageFormula (orbitParameters a s t W)
    (Fin.cases hW (Fin.cases carrier (Fin.cases group (Fin.cases maps (fun i => Fin.elim0 i))))) hB
  · intro y hy
    obtain ⟨g, σ, hσ, _, rfl⟩ := (a.mem_orbitCodes s (M.nameDomain s) W y).1 hy
    exact M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ
  · intro y hy
    rw [a.mem_orbitCodes]
    constructor
    · rintro ⟨g, σ, hσ, hσW, eq⟩
      have hb := pairBound (t.encode g) (t.encode_mem g) σ.val hσW
      exact ⟨ZFSet.pair (t.encode g) σ.val, hb,
        (M.realize_orbitImageFormula a s t pairing unions powers separation collection carrier group maps W _ y
          (M.transitive hB hb) hy).2 ⟨g, ⟨σ, hσ⟩, hσW, rfl, eq⟩⟩
    · rintro ⟨z, hz, rel⟩
      obtain ⟨g, σ, hσW, _, eq⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
        carrier group maps W z y (M.transitive hB hz) hy).1 rel
      exact ⟨g, σ.val, σ.property, hσW, eq⟩
  · intro z hz y hy w hw rely relw
    obtain ⟨g, σ, _, shape, eqy⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
      carrier group maps W z y (M.transitive hB hz) hy).1 rely
    obtain ⟨h, τ, _, shape', eqw⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
      carrier group maps W z w (M.transitive hB hz) hw).1 relw
    have parts := ZFSet.pair_inj.1 (shape.symm.trans shape')
    have gh := t.injective parts.1
    have names : σ.val = τ.val := Subtype.ext parts.2
    rw [eqy, eqw, gh, names]

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mixtureTermCodes_mem (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) :
    M.mixtureTermCodes a s τ ∈ M.sets :=
  M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps _
    (M.immediateChildCodes_mem s pairing unions powers separation carrier τ ground)

theorem mixtureTermCodes_valid (τ : Name s) :
    ∀ y ∈ M.mixtureTermCodes a s τ, IsName s y := by
  intro y member
  obtain ⟨g, σ, _, _, rfl⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) y).1 member
  exact (a.act s g σ).property

theorem mixtureTermCodes_hs (F : NormalSubgroupFamily G) (τ : Name s)
    (hs : HereditarilySymmetric a s F τ) (ψ : Name s)
    (member : ψ.val ∈ M.mixtureTermCodes a s τ) : HereditarilySymmetric a s F ψ := by
  obtain ⟨g, σ, _, child, equal⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) ψ.val).1 member
  obtain ⟨ν, p, entry, childEqual⟩ := (Name.mem_immediateChildCodes τ σ.val).1 child
  have source : σ = ν := Subtype.ext childEqual
  subst σ
  have moved : ψ = a.act s g ν := Subtype.ext equal
  rw [moved]
  exact (hs.member entry).translated g

theorem mixtureTermCodes_rank (τ ψ : Name s)
    (member : ψ.val ∈ M.mixtureTermCodes a s τ) : Name.nameRank ψ < Name.nameRank τ := by
  obtain ⟨g, σ, _, child, equal⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) ψ.val).1 member
  obtain ⟨ν, p, entry, childEqual⟩ := (Name.mem_immediateChildCodes τ σ.val).1 child
  have source : σ = ν := Subtype.ext childEqual
  subst σ
  have moved : ψ = a.act s g ν := Subtype.ext equal
  rw [moved, a.nameRank_act]
  exact Name.entry_nameRank_lt entry

theorem mix_subset_mixtureTermCodes (τ : Name s) (ground : τ.val ∈ M.sets)
    (K : Subgroup G) (p : P) :
    (a.mix s K p τ).val ⊆ ZFSet.prod (M.mixtureTermCodes a s τ) s.carrier := by
  intro z member
  obtain ⟨σ, q, rfl⟩ := Name.entries_cover (a.mix s K p τ) member
  obtain ⟨g, _, ν, r, entry, rfl, _, _⟩ := (a.entry_mix s K p τ σ q).1 member
  refine ZFSet.pair_mem_prod.2 ⟨?_, s.encode_mem q⟩
  exact (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) _).2
    ⟨g, ν, (M.nameDomain s).children ground entry,
      (Name.mem_immediateChildCodes τ ν.val).2 ⟨ν, r, entry, rfl⟩, rfl⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMixtureNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem entry_restrictBelow (p : P) (τ σ : Name s) (q : P) :
    Entry σ (restrictBelow p τ) q ↔ ∃ r, Entry σ τ r ∧ q ≤ r ∧ q ≤ p :=
  entry_selectName _ τ σ q

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_restrictionEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets restrictionEntryFormula (extend z (extend τ.val (extend (s.encode p)
      (extend s.carrier (extend s.conditionOrder Fin.elim0))))) ↔
      z ∈ (Name.restrictBelow p τ).val := by
  let base := extend z (extend τ.val (extend (s.encode p) (extend s.carrier (extend s.conditionOrder Fin.elim0))))
  have hp := M.transitive carrier (s.encode_mem p)
  rw [restrictionEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨q, rest⟩ := (M.realize_exConditions s 4 _ (extend x base) carrier rfl).1 rest
    obtain ⟨r, shape, old, qr, qp⟩ := (M.realize_exConditions s 5 _
      (extend (s.encode q) (extend x base)) carrier rfl).1 rest
    let e := extend (s.encode r) (extend (s.encode q) (extend x base))
    have hq := M.transitive carrier (s.encode_mem q)
    have hr := M.transitive carrier (s.encode_mem r)
    have raw := (M.realize_pairMembershipFormula pairing 2 0 4 e hx hr hτ).1 old
    let σ : Name s := ⟨x, Name.isName_of_pair_mem τ x r raw⟩
    have eq := (M.realize_orderedPairFormula pairing 3 2 1 e hz hx hq).1 shape
    change z = ZFSet.pair x (s.encode q) at eq
    rw [eq]
    exact (Name.entry_restrictBelow p τ σ q).2 ⟨r, raw,
      (M.realize_conditionLE s pairing carrier order 1 0 7 e q r rfl rfl rfl).1 qr,
      (M.realize_conditionLE s pairing carrier order 1 5 7 e q p rfl rfl rfl).1 qp⟩
  · intro member
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (Name.restrictBelow p τ) member
    have entry : Name.Entry σ (Name.restrictBelow p τ) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (Name.restrictBelow p τ).val
      rwa [← eq]
    obtain ⟨r, old, qr, qp⟩ := (Name.entry_restrictBelow p τ σ q).1 entry
    have hσ := (M.nameDomain s).children hτ old
    refine ⟨σ.val, hσ, ?_⟩
    apply (M.realize_exConditions s 4 _ (extend σ.val base) carrier rfl).2
    refine ⟨q, ?_⟩
    apply (M.realize_exConditions s 5 _ (extend (s.encode q) (extend σ.val base)) carrier rfl).2
    let e := extend (s.encode r) (extend (s.encode q) (extend σ.val base))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 2 1 e hz hσ (M.transitive carrier (s.encode_mem q))).2 eq
    · exact (M.realize_pairMembershipFormula pairing 2 0 4 e hσ (M.transitive carrier (s.encode_mem r)) hτ).2 old
    · exact (M.realize_conditionLE s pairing carrier order 1 0 7 e q r rfl rfl rfl).2 qr
    · exact (M.realize_conditionLE s pairing carrier order 1 5 7 e q p rfl rfl rfl).2 qp

theorem restrictBelow_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) : (Name.restrictBelow p τ).val ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions hτ)) carrier
  have bound : (Name.restrictBelow p τ).val ⊆ B := by
    intro z hz
    obtain ⟨σ, q, rfl⟩ := Name.entries_cover (Name.restrictBelow p τ) hz
    obtain ⟨r, old, _, _⟩ := (Name.entry_restrictBelow p τ σ q).1 hz
    exact pairBound σ.val (Name.child_mem_doubleUnion old) (s.encode q) (s.encode_mem q)
  let context := extend τ.val (extend (s.encode p) (extend s.carrier (extend s.conditionOrder Fin.elim0)))
  have selected := M.separation_mem separation restrictionEntryFormula context
    (Fin.cases hτ (Fin.cases (M.transitive carrier (s.encode_mem p))
      (Fin.cases carrier (Fin.cases order (fun i => Fin.elim0 i))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets restrictionEntryFormula (extend z context)) B =
      (Name.restrictBelow p τ).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_restrictionEntryFormula s pairing carrier order p τ hτ z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_restrictionEntryFormula s pairing carrier order p τ hτ z
        (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_subgroupOrbitCodes (K : Subgroup G) (τ : Name s) (y : ZFSet.{u}) :
    y ∈ a.subgroupOrbitCodes s K τ ↔ ∃ g ∈ K, y = (a.act s g τ).val := by
  rw [subgroupOrbitCodes, ZFSet.mem_range]
  constructor
  · rintro ⟨g, eq⟩
    exact ⟨g.val, g.property, eq.symm⟩
  · rintro ⟨g, hg, eq⟩
    exact ⟨⟨g, hg⟩, eq.symm⟩

theorem entry_act_restrictBelow (g : G) (p : P) (τ σ : Name s) (q : P) :
    Name.Entry σ (a.act s g (Name.restrictBelow p τ)) q ↔
      ∃ ν r, Name.Entry ν τ r ∧ a.act s g ν = σ ∧ q ≤ a.iso g p ∧ q ≤ a.iso g r := by
  change Name.Entry σ (Name.rename s (a.iso g) (Name.restrictBelow p τ)) q ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, c, entry, eq, cq⟩
    obtain ⟨r, old, cr, cp⟩ := (Name.entry_restrictBelow p τ ν c).1 entry
    refine ⟨ν, r, old, eq, ?_, ?_⟩
    · rw [← cq]
      exact (a.iso g).monotone cp
    · rw [← cq]
      exact (a.iso g).monotone cr
  · rintro ⟨ν, r, old, eq, qp, qr⟩
    refine ⟨ν, (a.iso g).symm q, (Name.entry_restrictBelow p τ ν _).2 ⟨r, old, ?_, ?_⟩,
      eq, (a.iso g).apply_symm_apply q⟩
    · exact (a.iso g).le_iff_le.1 (by simpa only [OrderIso.apply_symm_apply] using qr)
    · exact (a.iso g).le_iff_le.1 (by simpa only [OrderIso.apply_symm_apply] using qp)

theorem mix_code_union (K : Subgroup G) (p : P) (τ : Name s) :
    (a.mix s K p τ).val = ⋃₀ (a.subgroupOrbitCodes s K (Name.restrictBelow p τ)) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · intro hz
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (a.mix s K p τ) hz
    have entry : Name.Entry σ (a.mix s K p τ) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (a.mix s K p τ).val
      rwa [← eq]
    obtain ⟨g, hg, ν, r, old, moved, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
    refine ⟨(a.act s g (Name.restrictBelow p τ)).val,
      (a.mem_subgroupOrbitCodes s K _ _).2 ⟨g, hg, rfl⟩, ?_⟩
    rw [eq]
    exact (a.entry_act_restrictBelow s g p τ σ q).2 ⟨ν, r, old, moved, qp, qr⟩
  · rintro ⟨w, hw, hz⟩
    obtain ⟨g, hg, rfl⟩ := (a.mem_subgroupOrbitCodes s K _ w).1 hw
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (a.act s g (Name.restrictBelow p τ)) hz
    have entry : Name.Entry σ (a.act s g (Name.restrictBelow p τ)) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (a.act s g (Name.restrictBelow p τ)).val
      rwa [← eq]
    obtain ⟨ν, r, old, moved, qp, qr⟩ := (a.entry_act_restrictBelow s g p τ σ q).1 entry
    rw [eq]
    exact (a.entry_mix s K p τ σ q).2 ⟨g, hg, ν, r, old, moved, qp, qr⟩

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_subgroupOrbitFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (τ : Name s) (hτ : τ.val ∈ M.sets) (y : ZFSet.{u}) (hy : y ∈ M.sets) :
    Realize M.sets subgroupOrbitFormula (extend y (extend τ.val (extend (t.subset (fun g => g ∈ K))
      (extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
      y ∈ a.subgroupOrbitCodes s K τ := by
  rw [subgroupOrbitFormula, M.realize_exConditions t 4 _ _ group rfl, a.mem_subgroupOrbitCodes]
  apply exists_congr
  intro g
  change (t.encode g ∈ t.subset (fun g => g ∈ K) ∧ Realize M.sets _ _) ↔ _
  rw [t.encode_mem_subset]
  apply and_congr_right
  intro _
  rw [realize_atomicApplication, map_extend, map_extend, map_empty]
  change Realize M.sets codedNameActionFormula (extend (t.encode g) (extend τ.val (extend y
    (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔ _
  rw [M.realize_codedNameActionFormula a s t pairing unions powers separation collection carrier group maps g τ.val y hτ hy]
  constructor
  · rintro ⟨σ, eq, output⟩
    have names : σ.val = τ := Subtype.ext eq
    rwa [names] at output
  · intro eq
    exact ⟨⟨τ, hτ⟩, rfl, eq⟩

theorem subgroupOrbitCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) : a.subgroupOrbitCodes s K τ ∈ M.sets := by
  let W := ({τ.val, τ.val} : ZFSet.{u})
  have hW : W ∈ M.sets := M.unorderedPair_mem pairing hτ hτ
  let B := a.orbitCodes s (M.nameDomain s) W
  have hB := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
  have bound : a.subgroupOrbitCodes s K τ ⊆ B := by
    intro y hy
    obtain ⟨g, _, eq⟩ := (a.mem_subgroupOrbitCodes s K τ y).1 hy
    exact (a.mem_orbitCodes s (M.nameDomain s) W y).2
      ⟨g, τ, hτ, ZFSet.mem_pair.2 (Or.inl rfl), eq⟩
  let context := extend τ.val (extend (t.subset (fun g => g ∈ K))
    (extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))
  have selected := M.separation_mem separation subgroupOrbitFormula context
    (Fin.cases hτ (Fin.cases hK (Fin.cases carrier (Fin.cases group (Fin.cases maps (fun i => Fin.elim0 i)))))) hB
  have eq : ZFSet.sep (fun y => Realize M.sets subgroupOrbitFormula (extend y context)) B =
      a.subgroupOrbitCodes s K τ := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hy, rel⟩
      exact (M.realize_subgroupOrbitFormula a s t pairing unions powers separation collection carrier group maps K τ hτ y
        (M.transitive hB hy)).1 rel
    · intro hy
      exact ⟨bound hy, (M.realize_subgroupOrbitFormula a s t pairing unions powers separation collection carrier group maps K τ hτ y
        (M.transitive hB (bound hy))).2 hy⟩
  exact eq ▸ selected

theorem mix_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) : (a.mix s K p τ).val ∈ M.sets := by
  rw [a.mix_code_union]
  exact M.union_mem unions (M.subgroupOrbitCodes_mem a s t pairing unions powers separation collection carrier group maps K hK
    (Name.restrictBelow p τ) (M.restrictBelow_mem s pairing unions powers separation carrier order p τ hτ))

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem groundSequenceUnion_extends {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) (n : Nat) :
    SetMembers.raw (seq n) ⊆ groundSequenceUnion seq :=
  fun _ hz => (mem_groundSequenceUnion seq _).2 ⟨n, hz⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem descending_function_union_partial (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      Antitone seq → PartialFunctionCode X Y (groundSequenceUnion seq) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq decreasing
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq z).1 hz
    exact (M.smallFunction_raw_properties X Y ZFSet.omega (seq n)).2.1.shape hn
  · intro x y z xy xz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq _).1 xy
    obtain ⟨m, hm⟩ := (mem_groundSequenceUnion seq _).1 xz
    have code := (M.smallFunction_raw_properties X Y ZFSet.omega (seq (max n m))).2.1
    exact code.unique x y z
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_left n m)) hn)
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_right n m)) hm)

theorem descending_function_union_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        groundSequenceUnion seq ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  obtain ⟨ground, small⟩ := M.countable_union_of_sequence_graph pairing unions powers separation infinite choice
    hQ (M.prod_mem pairing unions powers separation hX hY) graph
    (natPresentation.graph_isFunc (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))
      (fun n => seq n.down))
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.1.shape)
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.2)
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨ground, M.descending_function_union_partial X Y seq decreasing, small⟩

theorem countable_function_lower_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        ∃ p, SetMembers.raw p = groundSequenceUnion seq ∧ ∀ n, p ≤ seq n := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have member := M.descending_function_union_mem pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  let p := SetMembers.ofMem (groundSequenceUnion seq) member
  have raw : SetMembers.raw p = groundSequenceUnion seq := SetMembers.raw_ofMem _ _
  refine ⟨p, raw, fun n => (M.smallFunction_le_iff X Y ZFSet.omega p (seq n)).2 ?_⟩
  rw [raw]
  exact groundSequenceUnion_extends seq n

theorem countable_function_internally_closed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    InternallyCountablyClosed M (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  obtain ⟨p, _, lower⟩ := M.countable_function_lower_bound pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  exact ⟨p, lower⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPrincipalSupportZF
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G : Type u} [Group G]
variable (t : Presentation G) (b : Presentation I) (K : I → Subgroup G)

theorem supportBasis_fiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (separation : SeparationSchema M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (i : I) :
    t.subset (fun g => g ∈ K i) ∈ M.sets := by
  have hi := M.transitive indices (b.encode_mem i)
  let params := extend (b.encode i) (extend (supportBasisCode b t K) Fin.elim0)
  have selected := M.separation_mem separation (pairMembershipFormula 1 0 2) params
    (Fin.cases hi (Fin.cases supports (fun j => Fin.elim0 j))) group
  have eq : ZFSet.sep (fun y => Realize M.sets (pairMembershipFormula 1 0 2) (extend y params)) t.carrier =
      t.subset (fun g => g ∈ K i) := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hy, rel⟩
      obtain ⟨g, rfl⟩ := (t.mem_carrier y).1 hy
      apply (t.encode_mem_subset (fun g => g ∈ K i) g).2
      exact (pair_mem_supportBasisCode b t K i g).1
        ((M.realize_pairMembershipFormula pairing 1 0 2 (extend (t.encode g) params)
          hi (M.transitive group hy) supports).1 rel)
    · intro hy
      obtain ⟨g, hg, rfl⟩ := (t.mem_subset (fun g => g ∈ K i) y).1 hy
      exact ⟨t.encode_mem g, (M.realize_pairMembershipFormula pairing 1 0 2
        (extend (t.encode g) params) hi (M.transitive group (t.encode_mem g)) supports).2
        ((pair_mem_supportBasisCode b t K i g).2 hg)⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMixtureDensityRecovery
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mix_mem_mixtureCandidates (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) (p : P) :
    (a.mix s K p τ).val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s τ) K := by
  apply (M.name_mem_niceNameCandidates a s _ K _).2
  exact ⟨M.mix_mem a s t pairing unions powers separation collection carrier order group maps K hK p τ ground,
    M.mix_subset_mixtureTermCodes a s τ ground K p, fun _ hg => a.mix_fixed s K p τ hg⟩

theorem mixture_candidate_data (F : NormalSubgroupFamily G) (K : Subgroup G)
    (member : F.mem K) (τ : Name s) (hs : HereditarilySymmetric a s F τ)
    (σ : Name s) (candidate : σ.val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s τ) K) :
    σ.val ∈ M.sets ∧ K ≤ a.stabilizer s σ ∧ HereditarilySymmetric a s F σ ∧
      Name.nameRank σ ≤ Name.nameRank τ := by
  have data := (M.name_mem_niceNameCandidates a s _ K σ).1 candidate
  refine ⟨data.1, data.2.2,
    niceNameCode_hs a s F member (M.mixtureTermCodes_hs a s F τ hs)
      ((niceNameCode_iff a s σ).2 data.2), ?_⟩
  change ZFSet.rank (Name.eval Set.univ σ) ≤ Name.nameRank τ
  rw [ZFSet.rank_le_iff]
  intro value memValue
  obtain ⟨ν, p, entry, _, rfl⟩ := (Name.mem_eval Set.univ σ value).1 memValue
  exact (Name.rank_eval_le Set.univ ν).trans_lt
    (M.mixtureTermCodes_rank a s τ ν (Name.entry_term_of_subset data.2.1 entry))

variable [OrderTop P]

theorem mixture_visibility_mem {I : Type u} (t : Presentation G) (b : Presentation I)
    (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) (i : I) (hi : b.encode i ∈ M.sets) :
    (M.niceVisibilityName a s (M.mixtureTermCodes a s τ) (K i)).val ∈ M.sets :=
  M.niceVisibilityName_mem a s t b K pairing unions powers separation collection carrier group supports maps
    (M.mixtureTermCodes_mem a s t pairing unions powers separation collection carrier group maps τ ground)
    (M.mixtureTermCodes_valid a s τ) i hi

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P I : Type u} [Group G]
variable [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation I) (K : I → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)

include pairing unions powers separation collection carrier order group indices supports maps in
theorem forcesMem_mixtureVisibility_of_dense
    (i : I) (x : Name s) (ground : x.val ∈ M.sets) (p₀ : P)
    (dense : DenseBelow p₀ {p | Name.ForcesEq p x (a.mix s (K i) p x)}) :
    Name.ForcesMem p₀ x (M.niceVisibilityName a s (M.mixtureTermCodes a s x) (K i)) := by
  have subgroup := M.supportBasis_fiber_mem t b K pairing separation group indices supports i
  intro q below
  obtain ⟨p, pq, equal⟩ := dense q below
  refine ⟨p, pq, a.mix s (K i) p x, ⊤, ?_, le_top, equal⟩
  apply (M.entry_niceVisibilityName a s (M.mixtureTermCodes a s x) (K i) _ ⊤).2
  exact ⟨M.mix_mem_mixtureCandidates a s t pairing unions powers separation collection
    carrier order group maps (K i) subgroup x ground p, rfl⟩

include pairing unions powers separation collection carrier order group indices supports maps in
theorem exists_mixtureCandidate_of_dense
    (F : NormalSubgroupFamily G) (i : I) (member : F.mem (K i))
    (x : Name s) (ground : x.val ∈ M.sets) (symmetric : HereditarilySymmetric a s F x)
    (p₀ : P) (dense : DenseBelow p₀ {p | Name.ForcesEq p x (a.mix s (K i) p x)})
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (active : H.mem p₀) :
    ∃ z : Name s,
      z.val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s x) (K i) ∧
      z.val ∈ M.sets ∧ HereditarilySymmetric a s F z ∧
      K i ≤ a.stabilizer s z ∧ Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x := by
  have visibility := M.mixture_visibility_mem a s t b K pairing unions powers separation
    collection carrier group supports maps x ground i (M.transitive indices (b.encode_mem i))
  have forced := M.forcesMem_mixtureVisibility_of_dense a s t b K pairing unions powers
    separation collection carrier order group indices supports maps i x ground p₀ dense
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE => generic E (Or.inl hE)
  have value := Name.forcesMem_sound (M.nameDomain s) H atomic ground visibility active forced
  obtain ⟨z, candidate, equal⟩ :=
    (M.mem_eval_niceVisibilityName a s (M.mixtureTermCodes a s x) (K i)
      {q | H.mem q} H.top_mem (Name.eval {q | H.mem q} x)).1 value
  obtain ⟨groundZ, support, hs, rank⟩ :=
    M.mixture_candidate_data a s F (K i) member x symmetric z candidate
  exact ⟨z, candidate, groundZ, hs, support, rank, equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentedDomainConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order

theorem stageOneRawForces_condition_mono {n : Nat} (phi : SetFormula n)
    (names : Assignment (M.nameDomain s) n) {p q : P} (qp : q ≤ p)
    (forced : stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      (fun j => (names j).val.val)) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi
      (fun j => (names j).val.val) := by
  apply (M.stageOneRawForces_iff s pairing unions powers separation collection
    carrier order phi q names).2
  exact forces_mono (M.nameDomain s) phi names
    ((M.stageOneRawForces_iff s pairing unions powers separation collection
      carrier order phi p names).1 forced) qp

private theorem rawForces_pair_condition_mono
    (phi : SetFormula 2) (z tau : (M.nameDomain s).names) {p q : P} (qp : q ≤ p)
    (forced : stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      ![z.val.val, tau.val.val]) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi
      ![z.val.val, tau.val.val] := by
  have fields : (fun j : Fin 2 => (![z, tau] j).val.val) =
      ![z.val.val, tau.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  have moved := M.stageOneRawForces_condition_mono s pairing unions powers separation
    collection carrier order phi ![z, tau] qp
  rw [fields] at moved
  exact moved forced

theorem preparationForcingCode_condition_mono
    (nodes N visibility : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F f : ZFSet.{u})
    (range : f ⊆ ZFSet.prod nodes N) {p q : P} (qp : q ≤ p)
    (code : PreparationForcingCode M s.carrier s.conditionOrder (s.encode p)
      nodes visibility z.val.val F f) :
    PreparationForcingCode M s.carrier s.conditionOrder (s.encode q)
      nodes visibility z.val.val F f := by
  constructor
  · intro v V entry member
    let name : (M.nameDomain s).names :=
      ⟨⟨V, graphNames v V entry member⟩, M.pair_right (M.transitive graphGround entry)⟩
    have decisions := code.1 v V entry member
    exact ⟨fun yes => rawForces_pair_condition_mono M s pairing unions powers separation
      collection carrier order (.mem 0 1) z name qp (decisions.1 yes),
      fun no => rawForces_pair_condition_mono M s pairing unions powers separation
        collection carrier order (.neg (.mem 0 1)) z name qp (decisions.2 no)⟩
  · intro v tau entry
    have htau := (ZFSet.pair_mem_prod.1 (range entry)).2
    let name : (M.nameDomain s).names :=
      ⟨⟨tau, validN tau htau⟩, M.transitive namesGround htau⟩
    exact rawForces_pair_condition_mono M s pairing unions powers separation collection
      carrier order (.equal 0 1) z name qp (code.2 v tau entry)

end PartitionPilot.Forcing.TransitiveGround

end



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem storedPreparationRequests_mem {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (fields : Fin 15 → ZFSet.{u}) (members : ∀ j, fields j ∈ M.sets) :
    M.storedPreparationRequests A fields ∈ M.sets :=
  (M.definable_storedPreparationRequests pairing unions powers separation).closed
    (extend A fields) (Fin.cases hA members)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundVisibilitySupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_visibilitySupportIncidence
    (nodes names visibility top z : ZFSet.{u}) :
    z ∈ visibilitySupportIncidence nodes names visibility top ↔
      ∃ v ∈ nodes, ∃ tau ∈ names, z = ZFSet.pair v tau ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [visibilitySupportIncidence, ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, v, tau, rfl, V, entry, member⟩
    exact ⟨v, (ZFSet.pair_mem_prod.1 bound).1,
      tau, (ZFSet.pair_mem_prod.1 bound).2, rfl, V, entry, member⟩
  · rintro ⟨v, hv, tau, htau, rfl, V, entry, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, htau⟩, v, tau, rfl, V, entry, member⟩

theorem pair_mem_visibilitySupportIncidence
    (nodes names visibility top v tau : ZFSet.{u}) :
    ZFSet.pair v tau ∈ visibilitySupportIncidence nodes names visibility top ↔
      v ∈ nodes ∧ tau ∈ names ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [mem_visibilitySupportIncidence]
  constructor
  · rintro ⟨v', hv, tau', htau, equal, witness⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, htau, witness⟩
  · rintro ⟨hv, htau, witness⟩
    exact ⟨v, hv, tau, htau, rfl, witness⟩

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem supportedEqualityCertificateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.supportedEqualityCertificateBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.groundPower_mem powers hNodes)
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hN))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem synchronizedEnumerationBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) : M.synchronizedEnumerationBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation
    (M.groundRelations_mem pairing unions powers separation omega hNodes)
    (M.groundRelations_mem pairing unions powers separation omega hN)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStoredPreparedFamilyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_certificateUsedSupports (nodes k v : ZFSet.{u}) :
    v ∈ certificateUsedSupports nodes k ↔ v ∈ nodes ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B :=
  ZFSet.mem_sep

namespace BoundedFormula

theorem truth_certificateBasisMemberFormula {n} (v k : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (certificateBasisMemberFormula v k) env ↔
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧ env v ∈ B := by
  simp only [certificateBasisMemberFormula, truth_exGraphFields, truth_exPairFields, Truth]
  change (∃ z c, ZFSet.pair z c ∈ env k ∧ ∃ F tail, c = ZFSet.pair F tail ∧
    ∃ B f, tail = ZFSet.pair B f ∧ env v ∈ B) ↔ _
  constructor
  · rintro ⟨z, c, edge, F, tail, rfl, B, f, rfl, member⟩
    exact ⟨z, F, B, f, edge, member⟩
  · rintro ⟨z, F, B, f, edge, member⟩
    exact ⟨z, _, edge, F, _, rfl, B, f, rfl, member⟩

theorem truth_preparationEventSupportFormula {n} (v event : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (preparationEventSupportFormula v event) env ↔
      ∃ alpha r k enumerations,
        env event = ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) ∧
          ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ env v ∈ B := by
  simp only [preparationEventSupportFormula, truth_exPairFields, truth_certificateBasisMemberFormula]
  change (∃ alpha output, env event = ZFSet.pair alpha output ∧ ∃ r tail,
    output = ZFSet.pair r tail ∧ ∃ k enumerations, tail = ZFSet.pair k enumerations ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ env v ∈ B) ↔ _
  constructor
  · rintro ⟨alpha, output, equal, r, tail, rfl, k, enumerations, rfl, data⟩
    exact ⟨alpha, r, k, enumerations, equal, data⟩
  · rintro ⟨alpha, r, k, enumerations, equal, data⟩
    exact ⟨alpha, _, equal, r, _, rfl, k, enumerations, rfl, data⟩

end BoundedFormula






end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPreparationEventSupportGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem preparationEventUsedSupports_mem (separation : SeparationSchema M.sets)
    {nodes event : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hEvent : event ∈ M.sets) :
    preparationEventUsedSupports nodes event ∈ M.sets := by
  have ground := M.bounded_separation_mem separation
    (BoundedFormula.preparationEventSupportFormula 0 1) ![event]
    (Fin.cases hEvent (fun j => Fin.elim0 j)) hNodes
  have equal : ZFSet.sep (fun v => BoundedFormula.Truth
      (BoundedFormula.preparationEventSupportFormula 0 1) (extend v ![event])) nodes =
        preparationEventUsedSupports nodes event := by
    apply ZFSet.ext
    intro v
    rw [ZFSet.mem_sep, BoundedFormula.truth_preparationEventSupportFormula,
      preparationEventUsedSupports, ZFSet.mem_sep]
    rfl
  exact equal ▸ ground

theorem pair_mem_preparationEventSupportGraph (nodes E event support : ZFSet.{u}) :
    ZFSet.pair event support ∈ M.preparationEventSupportGraph nodes E ↔
      event ∈ E ∧ support ∈ M.groundPower nodes ∧
        support = preparationEventUsedSupports nodes event := by
  rw [preparationEventSupportGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨he, hs⟩, event', support', equal, value⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨he, hs, value⟩
  · rintro ⟨he, hs, value⟩
    exact ⟨⟨he, hs⟩, event, support, rfl, value⟩

theorem pair_mem_preparationUsedSupportSequence
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) (i support : ZFSet.{u}) :
    ZFSet.pair i support ∈ M.preparationUsedSupportSequence nodes E events ↔
      ∃ event, ZFSet.pair i event ∈ events ∧ support = preparationEventUsedSupports nodes event := by
  rw [preparationUsedSupportSequence, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, event, _, edge, value⟩
    exact ⟨event, edge, (M.pair_mem_preparationEventSupportGraph nodes E event support).1 value |>.2.2⟩
  · rintro ⟨event, edge, rfl⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have hs := (M.mem_groundPower nodes _).2
      ⟨M.preparationEventUsedSupports_mem separation hNodes (M.transitive hE bounds.2),
        fun _ h => (ZFSet.mem_sep.1 h).1⟩
    exact ⟨bounds.1, hs, event, bounds.2, edge,
      (M.pair_mem_preparationEventSupportGraph nodes E event _).2 ⟨bounds.2, hs, rfl⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNicePreparationWitnessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_preparationWitnessBound (nodes T Q r k enumerations : ZFSet.{u}) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q ↔
      r ∈ Q ∧ k ∈ M.groundRelations (M.groundRelations T Q)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q)) ∧
      enumerations ∈ M.groundRelations (M.groundRelations T Q)
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) := by
  simp only [preparationWitnessBound, ZFSet.pair_mem_prod]

theorem preparationWitnessBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes T Q : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.preparationWitnessBound nodes T Q ∈ M.sets := by
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  exact M.prod_mem pairing unions powers separation hQ
    (M.prod_mem pairing unions powers separation
      (M.groundRelations_mem pairing unions powers separation hW
        (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega))
      (M.groundRelations_mem pairing unions powers separation hW
        (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega)))

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundVaryingPreparationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationCode_pair_iff (packed Q upperOrder nodes T levels omega C E alpha p y : ZFSet.{u}) :
    M.VaryingPreparationCode packed Q upperOrder nodes T levels omega C E
      (ZFSet.pair (ZFSet.pair alpha p) y) ↔
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        (canonicalMeetGraph (fields 10) (fields 11)) omega C E fields p y := by
  constructor
  · rintro ⟨alpha', p', y', fields, equal, rest⟩
    obtain ⟨input, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
    exact ⟨fields, rest⟩
  · rintro ⟨fields, rest⟩
    exact ⟨alpha, p, y, fields, rfl, rest⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_varyingPreparationRelation
    (stages packed Q upperOrder nodes T alpha p y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
    alpha ∈ stages ∧ p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      ∃ fields : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
        fields 6 = T ∧ fields 10 = nodes ∧
        MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
        M.StoredPreparationCode upperOrder
          (rowAssignmentCutGraph Q (fields 7) (refinementDataHistoryLevels stages packed T) alpha)
          (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega
          (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
          (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  simp only [varyingPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod,
    M.varyingPreparationCode_pair_iff, and_assoc]

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRefinementBinaryUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}

theorem cut_order (run : RecursiveRefinementDataHistory M rows T stages history)
    {q A p D beta : ZFSet.{u}}
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) (hbeta : beta ∈ stages) :
    ZFSet.pair (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) beta A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) beta D)) ∈
      M.refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history) := by
  obtain ⟨hq, hp, rowsBelow, data⟩ := (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history q A p D).1 below
  exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history) _ _ _ _).2
    ⟨run.cut_mem hq hbeta, run.cut_mem hp hbeta, rowsBelow, assignmentCut_mono data⟩

end RecursiveRefinementDataHistory
namespace RecursiveRefinementOrderHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem lower_order {q A p D beta : ZFSet.{u}} (d : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) :
    ZFSet.pair (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) beta A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) beta D)) ∈ d 8 :=
  (run.order beta d entry).symm ▸ run.carriers.cut_order below (run.carriers.data.function.pair_source entry)

end RecursiveRefinementOrderHistory





end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

theorem semanticStructuralAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  unfold semanticStructuralAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawPreparedFamilyConditionPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem preparedCertificateCode_condition_mono
    (nodes nodeOrder meet N visibility top omega : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F B f e names : ZFSet.{u})
    {p q : P} (qp : q ≤ p)
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      nodes nodeOrder meet N visibility top omega z.val.val F B f e names) :
    PreparedCertificateCode M s.carrier s.conditionOrder (s.encode q)
      nodes nodeOrder meet N visibility top omega z.val.val F B f e names := by
  obtain ⟨filter, coinitial, nonempty, enumerated, supported, forced⟩ := code
  refine ⟨filter, coinitial, nonempty, enumerated, supported, ?_⟩
  apply M.preparationForcingCode_condition_mono s pairing unions powers separation collection
    carrier order nodes N visibility graphGround graphNames namesGround validN z F f _ qp forced
  intro entry member
  obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (enumerated.1.1 member)
  have incidence := (pair_mem_visibilitySupportIncidence nodes N visibility top v tau).1
    (supported v tau member)
  exact ZFSet.pair_mem_prod.2 ⟨incidence.1, htau⟩

theorem preparedCertificateFamilyCode_condition_mono
    (nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (requestsGround : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
    {p q : P} (qp : q ≤ p)
    (code : PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p)
      nodes nodeOrder meet N visibility top omega J C E k enumerations) :
    PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode q)
      nodes nodeOrder meet N visibility top omega J C E k enumerations := by
  refine ⟨code.1, code.2.1, ?_⟩
  intro z F B f e names stored enumerated
  have member := (ZFSet.pair_mem_prod.1 (code.1.1 stored)).1
  let name : (M.nameDomain s).names :=
    ⟨⟨z, validJ z member⟩, M.transitive requestsGround member⟩
  exact M.preparedCertificateCode_condition_mono s pairing unions powers separation collection
    carrier order nodes nodeOrder meet N visibility top omega graphGround graphNames
    namesGround validN name F B f e names qp (code.2.2 z F B f e names stored enumerated)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem preparedCertificateFamilyCode_raw_condition_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (P order nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u})
    (orderCode : PartialOrderCode P order)
    (carrierGround : P ∈ M.sets) (orderGround : order ∈ M.sets)
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes →
      IsName (SetMembers.presentation P) V)
    (namesGround : N ∈ M.sets)
    (validN : ∀ tau ∈ N, IsName (SetMembers.presentation P) tau)
    (requestsGround : J ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName (SetMembers.presentation P) z)
    (p q : ZFSet.{u}) (hp : p ∈ P) (hq : q ∈ P) (qp : ZFSet.pair q p ∈ order)
    (code : PreparedCertificateFamilyCode M P order p
      nodes nodeOrder meet N visibility top omega J C E k enumerations) :
    PreparedCertificateFamilyCode M P order q
      nodes nodeOrder meet N visibility top omega J C E k enumerations := by
  let := orderCode.toPartialOrder
  let s := SetMembers.presentation P
  have groundOrder : s.conditionOrder ∈ M.sets := M.decoded_order_mem orderCode orderGround
  have orderEq : s.conditionOrder = order := orderCode.conditionOrder_eq
  have pCode : s.encode (SetMembers.ofMem p hp) = p := SetMembers.raw_ofMem p hp
  have qCode : s.encode (SetMembers.ofMem q hq) = q := SetMembers.raw_ofMem q hq
  have typedBelow : SetMembers.ofMem q hq ≤ SetMembers.ofMem p hp := by
    change ZFSet.pair (SetMembers.raw (SetMembers.ofMem q hq))
      (SetMembers.raw (SetMembers.ofMem p hp)) ∈ order
    simpa only [SetMembers.raw_ofMem] using qp
  have initial : PreparedCertificateFamilyCode M s.carrier s.conditionOrder
      (s.encode (SetMembers.ofMem p hp)) nodes nodeOrder meet N visibility top omega
      J C E k enumerations := by
    exact (congrArg₂ (fun r c => PreparedCertificateFamilyCode M P r c
      nodes nodeOrder meet N visibility top omega J C E k enumerations) orderEq pCode).mpr code
  have moved := M.preparedCertificateFamilyCode_condition_mono s pairing unions powers
    separation collection carrierGround groundOrder nodes nodeOrder meet N visibility top omega
    J C E k enumerations graphGround graphNames namesGround validN requestsGround validJ
    typedBelow initial
  exact (congrArg₂ (fun r c => PreparedCertificateFamilyCode M P r c
    nodes nodeOrder meet N visibility top omega J C E k enumerations) orderEq qCode).mp moved

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStoredPreparationFamilyPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem preparationCut_strengthens
    {alpha r p q : ZFSet.{u}} (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (stronger : r ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair r p ∈ M.refinementHistoryOrder rows rowOrder T stages history)
    (selected : ZFSet.pair p q ∈ rowAssignmentCutGraph
      (M.refinementHistoryForcing rows T stages history) (fields 7)
      (refinementDataHistoryLevels stages history T) alpha) :
    ∃ rCut, rCut ∈ fields 7 ∧ q ∈ fields 7 ∧
      ZFSet.pair r rCut ∈ rowAssignmentCutGraph
        (M.refinementHistoryForcing rows T stages history) (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      ZFSet.pair rCut q ∈ fields 8 := by
  obtain ⟨_, oldRow, oldA, equal⟩ := (mem_rowAssignmentCutGraph _ _ _ _ _).1 selected
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have oldValid := ((pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 selected).2.1
  obtain ⟨newRow, _, newA, _, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history stronger)
  have member := run.carriers.data.function.pair_source stored
  have newValid := (run.carriers.carrier alpha fields stored).symm ▸
    run.carriers.cut_mem stronger member
  refine ⟨ZFSet.pair newRow
      (assignmentCut (refinementDataHistoryLevels stages history T) alpha newA),
    newValid, oldValid, ?_, run.lower_order fields stored below⟩
  exact (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2 ⟨stronger, newValid, rfl⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem storedPreparationFamily_cut_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {rows rowOrder T stages history alpha r p q A meet C E k enumerations : ZFSet.{u}}
    (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
    (fields : Fin 15 → ZFSet.{u}) (environment : StoredPreparationEnvironment M fields)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (hA : A ∈ M.sets)
    (stronger : r ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair r p ∈ M.refinementHistoryOrder rows rowOrder T stages history)
    (selected : ZFSet.pair p q ∈ rowAssignmentCutGraph
      (M.refinementHistoryForcing rows T stages history) (fields 7)
      (refinementDataHistoryLevels stages history T) alpha)
    (code : PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
      meet (fields 14) (fields 13) (fields 9) ZFSet.omega
      (M.storedPreparationRequests A fields) C E k enumerations) :
    ∃ rCut, rCut ∈ fields 7 ∧
      ZFSet.pair r rCut ∈ rowAssignmentCutGraph
        (M.refinementHistoryForcing rows T stages history) (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      ZFSet.pair rCut q ∈ fields 8 ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) rCut (fields 10) (fields 11)
        meet (fields 14) (fields 13) (fields 9) ZFSet.omega
        (M.storedPreparationRequests A fields) C E k enumerations := by
  obtain ⟨rCut, hrCut, hq, cut, lowerBelow⟩ :=
    run.preparationCut_strengthens fields stored stronger below selected
  have requestsGround := M.storedPreparationRequests_mem pairing unions powers separation
    hA fields environment.ground
  have requestsValid : ∀ z ∈ M.storedPreparationRequests A fields,
      IsName (SetMembers.presentation (fields 7)) z := by
    intro z hz
    rcases ZFSet.mem_union.1 hz with left | right
    · exact environment.names_valid z ((mem_relationImage _ _ _ _).1 left).1
    · exact environment.names_valid z ((mem_relationImage _ _ _ _).1 right).1
  refine ⟨rCut, hrCut, cut, lowerBelow, ?_⟩
  exact M.preparedCertificateFamilyCode_raw_condition_mono pairing unions powers separation collection
    (fields 7) (fields 8) (fields 10) (fields 11) meet (fields 14) (fields 13) (fields 9)
    ZFSet.omega (M.storedPreparationRequests A fields) C E k enumerations environment.order
    (environment.ground 7) (environment.ground 8) (environment.ground 13)
    environment.visibility_valid (environment.ground 14) environment.names_valid
    requestsGround requestsValid q rCut hq hrCut lowerBelow code

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_preparationEnvironment (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    StoredPreparationEnvironment M fields := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : fields = M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored exactStored)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have members : ∀ j, fields j ∈ M.sets := M.refinementFormulaDataCode_fields_mem fields
    (M.transitive (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion stored))
  refine ⟨?_, members, ?_, ?_⟩
  · rw [same]
    exact lower.conditionOrder_code
  · rw [same]
    intro z hz
    exact Name.isName_of_subset valid ((M.mem_groundRelations T lower.carrier z).1 hz).2
  · rw [same]
    intro v V entry _
    obtain ⟨i, equal⟩ := (M.mem_niceVisibilityGraph act lower b T d.principalFix
      (ZFSet.pair v V)).1 entry
    have value := (ZFSet.pair_inj.1 equal).2
    rw [value]
    exact (M.niceVisibilityName act lower T (d.principalFix i)).property

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainEasyCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
universe u
private theorem decoded_property_congr
    {G R : Type u} [Group G] [PartialOrder R]
    (M : TransitiveGround.{u}) (c : Presentation R) (t : Presentation G)
    (T alpha rowGraph packed1 packed2 assignments1 assignments2 action1 action2 : ZFSet.{u})
    (packedEq : packed1 = packed2) (assignmentsEq : assignments1 = assignments2)
    (actionEq : action1 = action2)
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop)
    (code1 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
      let Q1 := M.refinementHistoryForcing c.carrier T alpha packed1
      PosetActionCode t.carrier Q1 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q1).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q1 c.carrier (⋃₀ ⋃₀ Q1) assignments1 rowGraph action1))
    (code2 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
      let Q2 := M.refinementHistoryForcing c.carrier T alpha packed2
      PosetActionCode t.carrier Q2 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q2).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q2 c.carrier (⋃₀ ⋃₀ Q2) assignments2 rowGraph action2)) :
    Property (M.refinementHistoryForcing c.carrier T alpha packed1)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
       code1.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed1))) ↔
    Property (M.refinementHistoryForcing c.carrier T alpha packed2)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
       code2.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed2))) := by
  subst packed2
  subst assignments2
  subst action2
  rfl

variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_restricted_property
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop) :
    Property
      (M.refinementHistoryForcing c.carrier T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.semanticStructuralAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
        cutOrdinal (trace.restrict cutOrdinal subset)) ↔
    Property Q (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked)
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset) := by
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  unfold semanticStructuralAction semanticStructuralPrefixAction
  exact decoded_property_congr M c t T alpha (a.actionGraph c t) _ _ _ _ _ _ packedEq
    (M.structuralAssignments_history_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 alpha history)
    (M.structuralAssignmentActionGraph_history_restrict t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history)
    Property _ _

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecordedPreparationSupportInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_preparationUsedSupportUnion
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) (v : ZFSet.{u}) :
    v ∈ M.preparationUsedSupportUnion nodes E events ↔
      v ∈ nodes ∧ ∃ i ∈ ZFSet.omega, ∃ alpha r k enumerations z F B f,
        ZFSet.pair i (ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))) ∈ events ∧
          ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B := by
  rw [preparationUsedSupportUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨support, hs, member⟩
    obtain ⟨_, i, hi, edge⟩ := (mem_relationImage _ _ _ _).1 hs
    obtain ⟨event, eventEdge, rfl⟩ :=
      (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).1 edge
    obtain ⟨hv, alpha, r, k, enumerations, rfl, z, F, B, f, certificate, inside⟩ := ZFSet.mem_sep.1 member
    exact ⟨hv, i, hi, alpha, r, k, enumerations, z, F, B, f, eventEdge, certificate, inside⟩
  · rintro ⟨hv, i, hi, alpha, r, k, enumerations, z, F, B, f, eventEdge, certificate, inside⟩
    let event := ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))
    let support := preparationEventUsedSupports nodes event
    have edge := (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).2
      ⟨event, eventEdge, rfl⟩
    have hs := (pair_mem_relationCompose _ _ _ _ _ _ _).1 edge |>.2.1
    exact ⟨support, (mem_relationImage _ _ _ _).2 ⟨hs, i, hi, edge⟩,
      ZFSet.mem_sep.2 ⟨hv, alpha, r, k, enumerations, rfl, z, F, B, f, certificate, inside⟩⟩

theorem recordedCertificateUsedSupports_subset
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events)
    {i alpha r k enumerations : ZFSet.{u}}
    (edge : ZFSet.pair i (ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))) ∈ events) :
    certificateUsedSupports nodes k ⊆ M.preparationUsedSupportUnion nodes E events := by
  intro v member
  obtain ⟨hv, z, F, B, f, certificate, inside⟩ :=
    (mem_certificateUsedSupports nodes k v).1 member
  exact (M.mem_preparationUsedSupportUnion separation hNodes hE function v).2
    ⟨hv, i, (ZFSet.pair_mem_prod.1 (function.1 edge)).1,
      alpha, r, k, enumerations, z, F, B, f, edge, certificate, inside⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)






theorem structural_common_support
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (H : ConditionFilter (SetMembers upperQ))
    (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) x →
    Name.eval {p | H.mem p} x = Name.eval {p | H.mem p} y →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∃ z : Name upper, z.val ∈ M.sets ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z ∧
      a.principalFix (geometry.meet.smallMeet V W) ≤ upperAct.stabilizer upper z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {p | H.mem p} z = Name.eval {p | H.mem p} x := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  intro H genericFormula V W x y groundX groundY supportX supportY symmetric values descent
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let historyTop := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    recursive.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  have upperCarrier : upper.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hLifted hs hPacked omega
  have upperOrder : upper.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier forcingOrder
      hLifted hs hPacked omega
  have upperGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier forcingAction hG hL order graph supports hLifted hSquared hs hh omega
  have upperMaps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b
    pairing unions powers separation collection upperCarrier hG upperGraph
  have atoms : H.GenericFor (Name.atomicFamily (M.nameDomain upper)) :=
    fun E member => genericFormula E (Or.inl member)
  obtain ⟨p0, active, equal⟩ :=
    (Name.eval_eq_iff_forcesEq (M.nameDomain upper) H atoms groundX groundY).1 values
  have dense := fulfilled.structural_dense_mixture_equalities collection infinite choice small
    smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p0 V W x y groundX groundY supportX supportY equal descent
  obtain ⟨z, _candidate, groundZ, hsZ, supportZ, rankZ, valueZ⟩ :=
    M.exists_mixtureCandidate_of_dense upperAct upper b s a.principalFix
      pairing unions powers separation collection upperCarrier upperOrder hG hL supports upperMaps
      (a.principalSupportFamily ⊥ directed) (geometry.meet.smallMeet V W)
      ⟨geometry.meet.smallMeet V W, le_rfl⟩ x groundX symmetric p0 dense H genericFormula active
  exact ⟨z, groundZ, hsZ, supportZ, rankZ, valueZ⟩






theorem structural_common_support_all_stages
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (H : ConditionFilter (SetMembers upperQ))
    (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) x →
    Name.eval {p | H.mem p} x = Name.eval {p | H.mem p} y →
    ∃ z : Name upper, z.val ∈ M.sets ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z ∧
      a.principalFix (geometry.meet.smallMeet V W) ≤ upperAct.stabilizer upper z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {p | H.mem p} z = Name.eval {p | H.mem p} x := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages
  induction stages using ZFSet.inductionOn with
  | h stages ih =>
    intro history hs hh stagesOrdinal trace
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
    let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace
    let upper := SetMembers.presentation upperQ
    intro H genericFormula V W x y groundX groundY supportX supportY symmetric values
    apply fulfilled.structural_common_support collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace
      H genericFormula V W x y groundX groundY supportX supportY symmetric values
    intro alpha member
    let hAlpha := M.transitive hs member
    let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
    let subset := (And.left stagesOrdinal) alpha member
    let Property : ∀ (Q : ZFSet.{u}) (orderQ : PartialOrder (SetMembers Q)),
        @PosetAction (SetMembers geometry.actors) _ (SetMembers Q) orderQ → Prop :=
      fun Q orderQ actionQ =>
        letI := orderQ
        let presentation := SetMembers.presentation Q
        ∀ (filter : ConditionFilter (SetMembers Q)),
          filter.GenericFor (formulaFamily (M.nameDomain presentation)) →
          ∀ (v w : SetMembers geometry.carrier) (first second : Name presentation),
            first.val ∈ M.sets → second.val ∈ M.sets →
            a.principalFix v ≤ actionQ.stabilizer presentation first →
            a.principalFix w ≤ actionQ.stabilizer presentation second →
            HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) first →
            Name.eval {q | filter.mem q} first = Name.eval {q | filter.mem q} second →
            ∃ z : Name presentation, z.val ∈ M.sets ∧
              HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) z ∧
              a.principalFix (geometry.meet.smallMeet v w) ≤ actionQ.stabilizer presentation z ∧
              Name.nameRank z ≤ Name.nameRank first ∧
              Name.eval {q | filter.mem q} z = Name.eval {q | filter.mem q} first
    have earlier := ih alpha member (graphRestriction alpha history) hAlpha
      (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal
      (trace.restrict cutOrdinal subset)
    have transferred := (M.semanticStructuralPrefixAction_restricted_property c act b s a ⊥
      directed lifted squared (c.encode ⊤) pairing unions powers separation collection
      carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared
      omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hh trace hAlpha cutOrdinal subset Property).1 earlier
    dsimp only
    intro lowerH _coded ordinary v w first second firstSupport secondSupport firstHS _secondHS equal
    obtain ⟨z, groundZ, symmetricZ, supportZ, _rankZ, valueZ⟩ := transferred lowerH ordinary
      v w first.val second.val first.property second.property firstSupport secondSupport firstHS equal
    exact ⟨⟨z, groundZ⟩, symmetricZ, supportZ, valueZ⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundFixedFairPreparationLimitCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]

theorem fixedFairPreparationLimit_supportPrepared
    (c : Presentation R)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {T stages packed nodes E prepSelector : ZFSet.{u}}
    (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages packed)
    (environments : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
        StoredPreparationEnvironment M fields)
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (prepSelected : prepSelector ⊆ M.varyingPreparationRelation stages packed
      (M.refinementHistoryForcing c.carrier T stages packed)
      (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) nodes T) :
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let order := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    let B := M.groundSmallSubsets
      (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
    let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
    let data := flatCarrierData c Q B shape
    ∀ (seq : Nat → SetMembers Q) (events : Nat → ZFSet.{u}),
      ZFSet.IsFunc ZFSet.omega E (familyCodeGraph natSetCode events) →
    ∀ limit : SetMembers Q,
      (∀ n, ZFSet.pair (SetMembers.raw limit) (SetMembers.raw (seq n)) ∈ order) →
      (∀ x ∈ SetMembers.raw (data limit),
        ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
          Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
          x ∈ SetMembers.raw (data (seq i)) ∧
          ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
          ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages packed T ∧
          (∀ k, Nat.pair i j ≤ k →
            x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
          ∃ y ∈ M.preparationWitnessBound nodes T Q, ∃ payload,
            y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
            ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
            events (Nat.pair i j + 1) = ZFSet.pair alpha y) →
      StoredSupportPreparedConditionCode M c.carrier T stages packed nodes (SetMembers.raw limit)
        (M.preparationUsedSupportUnion nodes E (familyCodeGraph natSetCode events)) := by
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let order := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let B := M.groundSmallSubsets
    (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c Q B shape
  dsimp only
  intro seq events eventFunction limit below visits limitRow limitA limitCode x hx
  have limitData : SetMembers.raw (data limit) = limitA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape limit).symm.trans limitCode)).2
  have inData : x ∈ SetMembers.raw (data limit) := limitData.symm ▸ hx
  obtain ⟨i, j, alpha, hAlpha, fields, _unpaired, _born, _early, stored, _level,
    retained, y, _hy, payload, yCode, selected, eventAt⟩ := visits x inData
  let n := Nat.pair i j
  have relationEntry := prepSelected selected
  rw [yCode] at relationEntry
  obtain ⟨_, _inputMember, bounded, other, otherStored, terms, nodeCarrier, meetCode, code⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q order nodes T alpha
      (SetMembers.raw (seq n)) (ZFSet.pair (SetMembers.raw (seq (n + 1))) payload)).1 relationEntry
  have same : other = fields :=
    refinementFormulaDataCode_injective (run.carriers.data.function.unique otherStored stored)
  subst other
  obtain ⟨sourceRow, sourceA, output, k, enumerations, q,
    inputCode, outputCode, _visitBelow, cut, family⟩ := code
  have sourceData : SetMembers.raw (data (seq n)) = sourceA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape (seq n)).symm.trans inputCode)).2
  obtain ⟨outputEq, payloadEq⟩ := ZFSet.pair_inj.1 outputCode
  subst output
  rw [payloadEq] at bounded
  obtain ⟨_, hkBound, heBound⟩ := (M.mem_preparationWitnessBound nodes T Q
    (SetMembers.raw (seq (n + 1))) k enumerations).1 bounded
  have hk := ((M.mem_groundRelations _ _ k).1 hkBound).1
  have hEnumerations := ((M.mem_groundRelations _ _ enumerations).1 heBound).1
  have hSourceA : sourceA ∈ M.sets := sourceData ▸
    ((M.mem_groundSmallSubsets _ _ _).1 (SetMembers.raw_mem (data (seq n)))).1
  have sourceMember : ZFSet.pair sourceRow sourceA ∈ Q := inputCode ▸ SetMembers.raw_mem (seq n)
  have sourceBelow := below n
  rw [limitCode, inputCode] at sourceBelow
  have sourceSubset := ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
    stages packed limitRow limitA sourceRow sourceA).1 sourceBelow).2.2.2
  have sourceSelected : x ∈ assignmentOnIndices (fields 0) T sourceA :=
    sourceData ▸ retained n (Nat.le_refl n)
  have environment := environments alpha fields stored
  obtain ⟨rCut, hrCut, finalCut, _cutBelow, finalFamily⟩ :=
    M.storedPreparationFamily_cut_mono pairing unions powers separation collection run fields
      environment stored hSourceA (SetMembers.raw_mem limit) (below (n + 1)) cut family
  have recorded : ZFSet.pair (natSetCode (n + 1))
      (ZFSet.pair alpha (ZFSet.pair (SetMembers.raw (seq (n + 1)))
        (ZFSet.pair k enumerations))) ∈ familyCodeGraph natSetCode events := by
    apply (mem_familyCodeGraph natSetCode events _).2
    refine ⟨n + 1, ?_⟩
    rw [eventAt, yCode, payloadEq]
  have supportBound := M.recordedCertificateUsedSupports_subset separation hNodes hE
    eventFunction recorded
  exact ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meetCode, environment,
    sourceRow, sourceA, hSourceA, sourceMember, sourceSubset, sourceSelected,
    k, hk, enumerations, hEnumerations, rCut, hrCut, finalCut, finalFamily, supportBound⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalStructuralPrefixDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_prefix_descent
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let Property : ∀ (Q : ZFSet.{u}) (orderQ : PartialOrder (SetMembers Q)),
      @PosetAction (SetMembers geometry.actors) _ (SetMembers Q) orderQ → Prop :=
    fun Q orderQ actionQ =>
      letI := orderQ
      let presentation := SetMembers.presentation Q
      ∀ (filter : ConditionFilter (SetMembers Q)),
        filter.GenericFor (formulaFamily (M.nameDomain presentation)) →
        ∀ (v w : SetMembers geometry.carrier) (first second : Name presentation),
          first.val ∈ M.sets → second.val ∈ M.sets →
          a.principalFix v ≤ actionQ.stabilizer presentation first →
          a.principalFix w ≤ actionQ.stabilizer presentation second →
          HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) first →
          Name.eval {q | filter.mem q} first = Name.eval {q | filter.mem q} second →
          ∃ z : Name presentation, z.val ∈ M.sets ∧
            HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) z ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ actionQ.stabilizer presentation z ∧
            Name.nameRank z ≤ Name.nameRank first ∧
            Name.eval {q | filter.mem q} z = Name.eval {q | filter.mem q} first
  have earlier := fulfilled.structural_common_support_all_stages
    collection infinite choice small smallD irreflexive columns hColumns hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    alpha (graphRestriction alpha history) hAlpha
    (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal
    (trace.restrict cutOrdinal subset)
  have transferred := (M.semanticStructuralPrefixAction_restricted_property c act b s a ⊥
    directed lifted squared (c.encode ⊤) pairing unions powers separation collection
    carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared
    omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hh trace hAlpha cutOrdinal subset Property).1 earlier
  intro lowerH _coded ordinary v w first second firstSupport secondSupport firstHS _secondHS equal
  obtain ⟨z, groundZ, symmetricZ, supportZ, _rankZ, valueZ⟩ := transferred lowerH ordinary
    v w first.val second.val first.property second.property firstSupport secondSupport firstHS equal
  exact ⟨⟨z, groundZ⟩, symmetricZ, supportZ, valueZ⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalStructuralSupportPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_groundSupportPreparedStrengthening
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (_descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val
    ),
    ∀ p ∈ upperQ, GroundSupportPreparedStrengtheningResult M c T stages packed b.carrier p := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history hs hh ordinal trace
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
  intro descent p hp
  refine Exists.elim
    (fulfilled.exists_groundFairPreparationOrbit c collection infinite choice small smallD irreflexive rowClosed
      a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
      topMem topRows stages history hs hh ordinal trace descent p hp)
    (fun enumSelector enumRest => ?_)
  have hEnum := enumRest.1
  have enumFunction := enumRest.2.1
  have enumSelected := enumRest.2.2.1
  refine Exists.elim enumRest.2.2.2 (fun E0 rangeRest => ?_)
  have hE0 := rangeRest.1
  have rangeFunction := rangeRest.2.1
  refine Exists.elim rangeRest.2.2 (fun prepSelector prepRest => ?_)
  have hPrep := prepRest.1
  have prepFunction := prepRest.2.1
  have prepSelected := prepRest.2.2.1
  refine Exists.elim prepRest.2.2.2 (fun e eRest => ?_)
  have he := eRest.1
  have chosen := eRest.2.1
  refine Exists.elim eRest.2.2 (fun orbit orbitRest => ?_)
  have hOrbit := orbitRest.1
  have orbitFunction := orbitRest.2.1
  have initial := orbitRest.2.2.1
  have steps := orbitRest.2.2.2
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let pTyped : SetMembers upperQ := SetMembers.ofMem p hp
  have typedChosen : ZFSet.pair (SetMembers.raw pTyped) e ∈ enumSelector := by
    simpa only [pTyped, SetMembers.raw_ofMem] using chosen
  have typedInitial : ∀ state, ZFSet.pair ∅ state ∈ orbit ↔
      state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw pTyped) (ZFSet.pair {ZFSet.pair ∅ e} ∅)) := by
    simpa only [pTyped, SetMembers.raw_ofMem] using initial
  obtain ⟨seq, start, seqGround, decreasing, clocks, births, events,
      clockZero, birthZero, eventZero, entries, eventGround, eventFunction,
      supportGround, supportSubset, supportSmall, rawSteps, limit, below, dataEqual,
      unionGround, exactEntries, visits⟩ :=
    M.semanticStructuralFairPreparation_supported_lower_bound c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction
      geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
      hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace infinite choice rowClosed pTyped E0 enumSelector prepSelector orbit e
      hE0 hOrbit rangeFunction enumSelected prepSelected typedChosen orbitFunction typedInitial steps
  have initialRaw : SetMembers.raw (seq 0) = p :=
    (congrArg SetMembers.raw start).trans (SetMembers.raw_ofMem p hp)
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let U := M.preparationWitnessBound b.carrier T upperQ
  let E := insert ∅ (ZFSet.prod stages U)
  let supportSet := M.preparationUsedSupportUnion b.carrier E (familyCodeGraph natSetCode events)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrder
      (Fin.cases supports (Fin.cases hT (Fin.cases hT2 (Fin.cases hs
        (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hUpper := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hU := M.preparationWitnessBound_mem pairing unions powers separation
    geometry.carrier_ground hT hUpper omega
  have hE := M.insert_mem pairing unions (M.empty_mem ⟨upperQ, hUpper⟩)
    (M.prod_mem pairing unions powers separation hs hU)
  have environments : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
        StoredPreparationEnvironment M fields := by
    intro alpha fields stored
    have member := historyRun.carriers.data.function.pair_source stored
    exact M.semanticStructuralPrefix_preparationEnvironment c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction
      geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
      hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace member fields stored
  refine ⟨SetMembers.raw limit, SetMembers.raw_mem limit, initialRaw ▸ below 0,
    supportSet, supportGround, supportSubset, supportSmall, ?_⟩
  exact M.fixedFairPreparationLimit_supportPrepared c pairing unions powers separation collection
    historyRun environments geometry.carrier_ground hE prepSelected seq events eventFunction
    limit below visits

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
open scoped ZFSet
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_support_prepared_strengthening_oai
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
    (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
    (_stagesOrdinal : ordinalSetProperty stages)
    (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  ∀ p ∈ upperQ,
    GroundSupportPreparedStrengtheningResult M c lifted stages packed s.carrier p := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  intro p member
  have descent := fulfilled.structural_prefix_descent
    collection infinite choice small smallD irreflexive columns hColumns hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation
    infinite choice coordinates two
  exact fulfilled.exists_groundSupportPreparedStrengthening c
    collection infinite choice small smallD irreflexive rowClosed act lifted squared (c.encode ⊤)
    carrier forcingOrder forcingAction hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    topMem topRows stages history hs hh stagesOrdinal trace descent p member

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening_oai.{u, v}
