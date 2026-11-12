-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_represented_domain_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:36:52.113204+00:00
-- url     : https://prove2.me/submissions/1531653c-cc2f-4d93-89ca-a713b403454a

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_compatible_insertion_unions
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_dense_mixture_equalities
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_successor_prepared_insertion_profiles
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralSuccessor_decide_represented_visibleLift
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralSuccessor_represented_absentLift_actor
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralSuccessor_represented_or_fresh

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NonemptyTupleFields
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementIndexCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {level C E U Rf Rc : ZFSet.{u}} (hl : level ∈ M.sets) (hC : C ∈ M.sets)
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hf : Rf ∈ M.sets) (hc : Rc ∈ M.sets) :
    refinementIndexCode level C E U Rf Rc ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 5 _
    (Fin.cases hl (Fin.cases hC (Fin.cases hE (Fin.cases hU
      (Fin.cases hf (Fin.cases hc (fun j => Fin.elim0 j)))))))

end PartitionPilot.Forcing.TransitiveGround



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentCuts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutFormula {n : Nat} (z levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutFormula z levels alpha) env ↔
      ∃ row A, env z = ZFSet.pair (ZFSet.pair row A)
        (ZFSet.pair row (assignmentCut (env levels) (env alpha) A)) := by
  rw [rowAssignmentCutFormula, realize_exBlock]
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (SetFormula.rowAssignmentCutBody z levels alpha).toFormula
        (extendMany 5 f env) ↔
      env z = ZFSet.pair (f 3) (f 4) ∧ f 3 = ZFSet.pair (f 0) (f 1) ∧
        f 4 = ZFSet.pair (f 0) (f 2) ∧
          f 2 = assignmentCut (env levels) (env alpha) (f 1) := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members)]
    simp only [SetFormula.rowAssignmentCutBody, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_assignmentCutFormula,
      extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨equal, upper, lower, cut⟩ := (actual f ground).1 body
    rw [upper, lower, cut] at equal
    exact ⟨f 0, f 1, equal⟩
  · rintro ⟨row, A, equal⟩
    have pairGround := equal ▸ members z
    have upper := M.pair_left pairGround
    have lower := M.pair_right pairGround
    let cut := assignmentCut (env levels) (env alpha) A
    let f : Fin 5 → ZFSet.{u} := ![row, A, cut, ZFSet.pair row A, ZFSet.pair row cut]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (M.pair_left upper) (Fin.cases (M.pair_right upper)
        (Fin.cases (M.pair_right lower) (Fin.cases upper
          (Fin.cases lower (fun j => Fin.elim0 j)))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, rfl, rfl, rfl⟩⟩

theorem rowAssignmentCutGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {upper lower levels alpha : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLower : lower ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) :
    rowAssignmentCutGraph upper lower levels alpha ∈ M.sets := by
  let params : Fin 2 → ZFSet.{u} := ![levels, alpha]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hLevels (Fin.cases hAlpha (fun j => Fin.elim0 j))
  have bound := M.prod_mem pairing unions powers separation hUpper hLower
  have selected := M.separation_mem separation (rowAssignmentCutFormula 0 1 2) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (rowAssignmentCutFormula 0 1 2) (extend z params))
      (ZFSet.prod upper lower) = rowAssignmentCutGraph upper lower levels alpha := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_rowAssignmentCutGraph]
    apply and_congr_right
    intro hz
    exact M.realize_rowAssignmentCutFormula 0 1 2 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

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



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

private theorem realize_representedReuseFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (A q P order T idx cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedReuseFormula A q P order T idx cu classes) env ↔
      ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
        stageOneAssignment (env idx) v w ∈ env A ∧
        ZFSet.pair v z ∈ env classes ∧
        stageOneRawForces M (env P) (env order) (env q)
          (.equal 0 1 : SetFormula 2) ![env cu, z] := by
  rw [representedReuseFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 T))
        (.conj (.mem (prefixIndex n 3 1) (suffixIndex n 3 T))
          (.conj (tripleMembershipFormula (suffixIndex n 3 idx) (prefixIndex n 3 0)
            (prefixIndex n 3 1) (suffixIndex n 3 A))
            (.conj (pairMembershipFormula (prefixIndex n 3 0) (prefixIndex n 3 2)
              (suffixIndex n 3 classes))
              (stageOneForcingAt (.equal 0 1 : SetFormula 2) (suffixIndex n 3 q)
                (suffixIndex n 3 P) (suffixIndex n 3 order)
                ![suffixIndex n 3 cu, prefixIndex n 3 2]))))) (extendMany 3 f env) ↔
      f 0 ∈ env T ∧ f 1 ∈ env T ∧
      stageOneAssignment (env idx) (f 0) (f 1) ∈ env A ∧
      ZFSet.pair (f 0) (f 2) ∈ env classes ∧
      stageOneRawForces M (env P) (env order) (env q)
        (.equal 0 1 : SetFormula 2) ![env cu, f 2] := by
    have allGround := extendMany_members 3 f env ground members
    simp only [Realize]
    rw [M.realize_tripleMembershipFormula pairing _ _ _ _ _
      (allGround _) (allGround _) (allGround _) (allGround _),
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      M.realize_stageOneForcingAt]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨hv, hw, literal, entry, forced⟩ := (actual f ground).1 body
    exact ⟨f 0, hv, f 1, hw, f 2, literal, entry, forced⟩
  · rintro ⟨v, hv, w, hw, z, literal, entry, forced⟩
    have ground : ∀ j, (![v, w, z] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members T) hv) (Fin.cases (M.transitive (members T) hw)
        (Fin.cases (M.pair_right (M.transitive (members classes) entry)) (fun j => Fin.elim0 j)))
    exact ⟨![v, w, z], ground, (actual ![v, w, z] ground).2 ⟨hv, hw, literal, entry, forced⟩⟩

private theorem realize_representedEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (p P order cut T idx u U cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedEntryFormula p P order cut T idx u U cu classes) env ↔
      ∃ row A q, env p = ZFSet.pair row A ∧ ZFSet.pair (env p) q ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) q
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) q (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ A ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) q
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
  rw [representedEntryFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.orderedPairFormula (suffixIndex n 3 p)
        (prefixIndex n 3 0) (prefixIndex n 3 1)).toFormula
        (.conj (pairMembershipFormula (suffixIndex n 3 p) (prefixIndex n 3 2) (suffixIndex n 3 cut))
          (disj (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) (prefixIndex n 3 2)
            (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
            (.conj (stageOneForcingAt (.mem 0 1 : SetFormula 2) (prefixIndex n 3 2)
              (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
              (representedReuseFormula (prefixIndex n 3 1) (prefixIndex n 3 2)
                (suffixIndex n 3 P) (suffixIndex n 3 order) (suffixIndex n 3 T)
                (suffixIndex n 3 idx) (suffixIndex n 3 cu) (suffixIndex n 3 classes))))))
        (extendMany 3 f env) ↔
      env p = ZFSet.pair (f 0) (f 1) ∧ ZFSet.pair (env p) (f 2) ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) (f 2)
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) (f 2) (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ f 1 ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) (f 2)
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
    have allGround := extendMany_members 3 f env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_orderedPairFormula, Realize,
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      realize_disj, M.realize_stageOneForcingAt, Realize, M.realize_stageOneForcingAt,
      realize_representedReuseFormula M pairing _ _ _ _ _ _ _ _ _ allGround]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 body⟩
  · rintro ⟨row, A, q, shape, cutEntry, code⟩
    have ground : ∀ j, (![row, A, q] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.pair_left (shape ▸ members p)) (Fin.cases (M.pair_right (shape ▸ members p))
        (Fin.cases (M.pair_right (M.transitive (members cut) cutEntry)) (fun j => Fin.elim0 j)))
    exact ⟨![row, A, q], ground, (actual ![row, A, q] ground).2 ⟨shape, cutEntry, code⟩⟩

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem representedDomainConditions_subset (upper levels alpha T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (U Rc u : (M.nameDomain s).names) :
    M.representedDomainConditions s upper levels alpha T valid idx U Rc u ⊆ upper :=
by
  intro z member
  rw [representedDomainConditions, ZFSet.mem_sep] at member
  exact member.1

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
private theorem representedParams_ground {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) :
    ∀ j, (![s.carrier, s.conditionOrder, rowAssignmentCutGraph upper s.carrier levels alpha,
      T, idx, u.val.val, U.val.val, (Name.refinementClass T valid Rc.val u.val).val,
      Name.refinementClassGraph T valid Rc.val T valid] : Fin 9 → ZFSet.{u}) j ∈ M.sets :=
  Fin.cases carrier (Fin.cases order
    (Fin.cases (M.rowAssignmentCutGraph_mem pairing unions powers separation hUpper carrier hLevels hAlpha)
      (Fin.cases hT (Fin.cases hIdx (Fin.cases u.property (Fin.cases U.property
        (Fin.cases (M.refinementClass_mem s pairing unions powers separation collection carrier order
          hT valid Rc.val u.val Rc.property u.property)
          (Fin.cases (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
            hT hT valid valid Rc.val Rc.property) (fun j => Fin.elim0 j)))))))))

include pairing unions powers separation collection carrier order in
theorem representedDomainConditions_mem {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) :
    M.representedDomainConditions s upper levels alpha T valid idx U Rc u ∈ M.sets :=
  M.separation_mem separation (representedEntryFormula 0 1 2 3 4 5 6 7 8 9) _
    (representedParams_ground M s pairing unions powers separation collection carrier order
      hUpper hLevels hAlpha hT valid hIdx U Rc u) hUpper

include pairing unions powers separation collection carrier order in
theorem pair_mem_representedDomainConditions {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) (row A : ZFSet.{u}) (q : P)
    (cut : s.encode q = ZFSet.pair row (assignmentCut levels alpha A)) :
    ZFSet.pair row A ∈ M.representedDomainConditions s upper levels alpha T valid idx U Rc u ↔
      ZFSet.pair row A ∈ upper ∧
      ((∀ r : P, r ≤ q → ¬ Name.ForcesMem r u.val U.val) ∨
        (Name.ForcesMem q u.val U.val ∧ ∃ v w : Name s,
          v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment idx v.val w.val ∈ A ∧
          Name.ForcesEq q (Name.refinementClass T valid Rc.val u.val)
            (Name.refinementClass T valid Rc.val v))) := by
  let params : Fin 9 → ZFSet.{u} := ![s.carrier, s.conditionOrder,
    rowAssignmentCutGraph upper s.carrier levels alpha, T, idx, u.val.val, U.val.val,
    (Name.refinementClass T valid Rc.val u.val).val, Name.refinementClassGraph T valid Rc.val T valid]
  have paramsGround := representedParams_ground M s pairing unions powers separation collection carrier order
    hUpper hLevels hAlpha hT valid hIdx U Rc u
  have raw (phi : SetFormula 2) (x y : (M.nameDomain s).names) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi ![x.val.val, y.val.val] ↔
        Forces (M.nameDomain s) phi ![x, y] q := by
    have fields : (fun j : Fin 2 => (![x, y] j).val.val) = ![x.val.val, y.val.val] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    have result := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi q ![x, y]
    rw [fields] at result
    exact result
  let className (v : (M.nameDomain s).names) : (M.nameDomain s).names :=
    ⟨Name.refinementClass T valid Rc.val v.val,
      M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid
        Rc.val v.val Rc.property v.property⟩
  rw [representedDomainConditions, ZFSet.mem_sep]
  change (ZFSet.pair row A ∈ upper ∧ Realize M.sets (representedEntryFormula 0 1 2 3 4 5 6 7 8 9)
    (extend (ZFSet.pair row A) params)) ↔ _
  apply and_congr_right
  intro member
  rw [realize_representedEntryFormula M pairing _ _ _ _ _ _ _ _ _ _ _
    (Fin.cases (M.transitive hUpper member) paramsGround)]
  change (∃ row' A' q', ZFSet.pair row A = ZFSet.pair row' A' ∧
    ZFSet.pair (ZFSet.pair row A) q' ∈ rowAssignmentCutGraph upper s.carrier levels alpha ∧
    (stageOneRawForces M s.carrier s.conditionOrder q' (.neg (.mem 0 1) : SetFormula 2) ![u.val.val, U.val.val] ∨
      (stageOneRawForces M s.carrier s.conditionOrder q' (.mem 0 1 : SetFormula 2) ![u.val.val, U.val.val] ∧
        ∃ v ∈ T, ∃ w ∈ T, ∃ z, stageOneAssignment idx v w ∈ A' ∧
          ZFSet.pair v z ∈ Name.refinementClassGraph T valid Rc.val T valid ∧
          stageOneRawForces M s.carrier s.conditionOrder q' (.equal 0 1 : SetFormula 2)
            ![(className u).val.val, z]))) ↔ _
  constructor
  · rintro ⟨row', A', q', same, entry, branch⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 same
    have equal := ((pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A q').1 entry).2.2
    have eq : q' = s.encode q := equal.trans cut.symm
    rw [eq] at branch
    rcases branch with inactive | ⟨active, v, hv, w, hw, z, literal, classEntry, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).1 inactive)
    · let vName : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
      have classEqual := (Name.pair_mem_refinementClassGraph T valid Rc.val T valid vName.val z).1 classEntry |>.2
      rw [classEqual] at equal
      exact Or.inr ⟨(raw (.mem 0 1) u U).1 active, vName.val, ⟨w, valid w hw⟩,
        hv, hw, literal, (raw (.equal 0 1) (className u) (className vName)).1 equal⟩
  · intro branch
    refine ⟨row, A, s.encode q, rfl,
      (pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A (s.encode q)).2
        ⟨member, s.encode_mem q, cut⟩, ?_⟩
    rcases branch with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).2 inactive)
    · let vName : (M.nameDomain s).names := ⟨v, M.transitive hT hv⟩
      exact Or.inr ⟨(raw (.mem 0 1) u U).2 active, v.val, hv, w.val, hw,
        (className vName).val.val, literal,
        (Name.pair_mem_refinementClassGraph T valid Rc.val T valid v _).2 ⟨hv, rfl⟩,
        (raw (.equal 0 1) (className u) (className vName)).2 equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTestedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem mem_testedMeetFilter (F r e x : ZFSet.{u}) :
    x ∈ testedMeetFilter F r e ↔ x ∈ F ∧ ZFSet.pair e x ∈ r := by
  rw [testedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨hx, a, ha, edge⟩
    exact ⟨hx, (ZFSet.mem_singleton.1 ha) ▸ edge⟩
  · rintro ⟨hx, edge⟩
    exact ⟨hx, e, ZFSet.mem_singleton.2 rfl, edge⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFinalInsertionExceptions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace FinalInsertionFamiliesCode
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}
variable (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
include family

theorem tests (order : PartialOrderCode P r) (filter : MeetFilterCode P r μ F)
    {label cap v : ZFSet.{u}} (entry : ZFSet.pair label cap ∈ caps)
    (hv : v ∈ P) (above : ZFSet.pair e v ∈ r) :
    (v ∈ F → ZFSet.pair cap v ∈ r) ∧
      (v ∉ F → ZFSet.pair (ZFSet.pair cap v) c ∈ μ) := by
  have profile := (family.profiles label cap entry).profile v hv above
  refine ⟨fun member => profile.1 ⟨v, member, order.refl v hv⟩, ?_⟩
  intro negative
  apply profile.2
  rintro ⟨f, hf, lower⟩
  exact negative (filter.upward f hf v hv lower)

end FinalInsertionFamiliesCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.FinalInsertionFamiliesCode
open SetRealization
universe u
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}

theorem decodedCaps_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedCaps label)) ∈ caps :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation P)
    caps family.cap_injection.function label

theorem decodedActors_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedActors label)) ∈ actors :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation G)
    actors family.actor_injection.function label

end PartitionPilot.Forcing.FinalInsertionFamiliesCode



namespace PartitionPilot.Forcing
open SetFormula
universe u

private theorem pair_mem_capExceptionRelation
    (profiles : Bool) (S Labels P r c caps x label : ZFSet.{u}) :
    ZFSet.pair x label ∈ capExceptionRelation profiles S Labels P r c caps ↔
      x ∈ S ∧ label ∈ Labels ∧ ∃ cap ∈ P, ZFSet.pair label cap ∈ caps ∧
        capExceptionTest profiles r c x cap := by
  rw [capExceptionRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, l, hl, cap, hcap, eq, entry, test⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hy, hl, cap, hcap, entry, test⟩
  · rintro ⟨hx, hl, cap, hcap, entry, test⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hl⟩, x, hx, label, hl, cap, hcap,
      rfl, entry, test⟩

private theorem truth_capExceptionEntryFormula {n}
    (profiles : Bool) (z s labels p r c caps : Fin n) (env : Fin n → ZFSet.{u}) :
    BoundedFormula.Truth (capExceptionEntryFormula profiles z s labels p r c caps) env ↔
      ∃ x ∈ env s, ∃ label ∈ env labels, ∃ cap ∈ env p,
        env z = ZFSet.pair x label ∧ ZFSet.pair label cap ∈ env caps ∧
          capExceptionTest profiles (env r) (env c) x cap := by
  cases profiles <;>
    simp only [capExceptionEntryFormula, capExceptionTest, Bool.false_eq_true, ↓reduceIte,
      BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_pairMembershipFormula] <;> rfl

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

private theorem capExceptionRelation_mem
    (profiles : Bool) {S Labels P r c caps : ZFSet.{u}}
    (hS : S ∈ M.sets) (hLabels : Labels ∈ M.sets) (hP : P ∈ M.sets)
    (hr : r ∈ M.sets) (hc : c ∈ M.sets) (hCaps : caps ∈ M.sets) :
    capExceptionRelation profiles S Labels P r c caps ∈ M.sets := by
  let params := extend S (extend Labels (extend P (extend r (extend c (extend caps Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (capExceptionEntryFormula profiles 0 1 2 3 4 5 6) params
    (Fin.cases hS (Fin.cases hLabels (Fin.cases hP (Fin.cases hr
      (Fin.cases hc (Fin.cases hCaps (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hS hLabels)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (capExceptionEntryFormula profiles 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod S Labels) = capExceptionRelation profiles S Labels P r c caps := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, capExceptionRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (truth_capExceptionEntryFormula profiles 0 1 2 3 4 5 6 _)
  exact eq ▸ selected

private theorem partial_image_countable
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S Labels rel : ZFSet.{u}} (hS : S ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hRel : rel ∈ M.sets) (code : PartialFunctionCode S Labels rel)
    (smallS : M.groundEmbeddable S ZFSet.omega) :
    M.groundEmbeddable (relationImage S Labels rel) ZFSet.omega := by
  have hImage := M.relationImage_mem separation hS hLabels hRel
  have restricted : PartialFunctionCode S (relationImage S Labels rel) rel := by
    refine ⟨?_, code.unique⟩
    intro z hz
    obtain ⟨x, hx, label, hl, rfl⟩ := ZFSet.mem_prod.1 (code.shape hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, (mem_relationImage _ _ _ _).2 ⟨hl, x, hx, hz⟩⟩
  obtain ⟨f, hf, injection⟩ := M.groundEmbeddable_of_partial_surjection
    pairing unions powers separation choice hS hImage hRel restricted
    (fun label member => ((mem_relationImage _ _ _ label).1 member).2)
  obtain ⟨g, hg, count⟩ := smallS
  exact ⟨relationCompose (relationImage S Labels rel) S ZFSet.omega f g,
    M.relationCompose_mem pairing unions powers separation hImage hS
      (M.omega_mem separation infinite) hf hg, injection.compose count⟩
end TransitiveGround

namespace FinalInsertionFamiliesCode

theorem exists_ground_countable_exceptions
    {Labels P G r μ A c e d F caps actors Used Profiles extra : ZFSet.{u}}
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hc : c ∈ M.sets) (hCaps : caps ∈ M.sets)
    (hUsed : Used ∈ M.sets) (hProfiles : Profiles ∈ M.sets) (hExtra : extra ∈ M.sets)
    (meet : MeetOrderCode P r μ) (usedSubset : Used ⊆ P)
    (filters : ∀ profile ∈ Profiles, MeetFilterCode P r μ profile)
    (smallUsed : M.groundEmbeddable Used ZFSet.omega)
    (smallProfiles : M.groundEmbeddable Profiles ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega) (extraSubset : extra ⊆ Labels) :
    ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
      ∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
        (∀ node ∈ Used, ZFSet.pair node cap ∈ r → ZFSet.pair node c ∈ r) ∧
        (∀ profile ∈ Profiles, c ∉ profile → cap ∉ profile) := by
  classical
  let nodes := capExceptionRelation false Used Labels P r c caps
  let profiles := capExceptionRelation true Profiles Labels P r c caps
  have hNodes : nodes ∈ M.sets := M.capExceptionRelation_mem pairing unions powers separation
    false hUsed hLabels hP hr hc hCaps
  have hProfilesRel : profiles ∈ M.sets := M.capExceptionRelation_mem pairing unions powers separation
    true hProfiles hLabels hP hr hc hCaps
  have nodesPartial : PartialFunctionCode Used Labels nodes := by
    refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
    intro node first second one two
    obtain ⟨used, _, cap₁, _, entry₁, negative, below₁⟩ :=
      (pair_mem_capExceptionRelation false Used Labels P r c caps node first).1 one
    obtain ⟨_, _, cap₂, _, entry₂, _, below₂⟩ :=
      (pair_mem_capExceptionRelation false Used Labels P r c caps node second).1 two
    by_contra different
    exact negative (meet.greatest cap₁ cap₂ c node (usedSubset used)
      (family.meets first second cap₁ cap₂ entry₁ entry₂ different) below₁ below₂)
  have profilesPartial : PartialFunctionCode Profiles Labels profiles := by
    refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
    intro profile first second one two
    obtain ⟨used, _, cap₁, _, entry₁, negative, positive₁⟩ :=
      (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile first).1 one
    obtain ⟨_, _, cap₂, _, entry₂, _, positive₂⟩ :=
      (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile second).1 two
    by_contra different
    exact negative ((filters profile used).closed_meet cap₁ positive₁ cap₂ positive₂ c
      (family.meets first second cap₁ cap₂ entry₁ entry₂ different))
  let nodeBad := relationImage Used Labels nodes
  let profileBad := relationImage Profiles Labels profiles
  have hNodeBad : nodeBad ∈ M.sets := M.relationImage_mem separation hUsed hLabels hNodes
  have hProfileBad : profileBad ∈ M.sets := M.relationImage_mem separation hProfiles hLabels hProfilesRel
  have nodeSmall := M.partial_image_countable pairing unions powers separation infinite choice
    hUsed hLabels hNodes nodesPartial smallUsed
  have profileSmall := M.partial_image_countable pairing unions powers separation infinite choice
    hProfiles hLabels hProfilesRel profilesPartial smallProfiles
  have hBoth := M.binary_union_mem pairing unions hNodeBad hProfileBad
  have smallBoth := M.groundCountable_binary_union pairing unions powers separation infinite choice
    hNodeBad hProfileBad nodeSmall profileSmall
  refine ⟨(nodeBad ∪ profileBad) ∪ extra, M.binary_union_mem pairing unions hBoth hExtra, ?_,
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      hBoth hExtra smallBoth smallExtra, ?_, ?_⟩
  · intro label member
    rcases ZFSet.mem_union.1 member with both | more
    · rcases ZFSet.mem_union.1 both with node | profile
      · exact ((mem_relationImage _ _ _ _).1 node).1
      · exact ((mem_relationImage _ _ _ _).1 profile).1
    · exact extraSubset more
  · intro label member
    exact ZFSet.mem_union.2 (Or.inr member)
  · intro label cap entry good
    have bounds := ZFSet.pair_mem_prod.1 (family.cap_injection.function.1 entry)
    constructor
    · intro node used below
      by_contra negative
      apply good
      apply ZFSet.mem_union.2 ∘ Or.inl
      apply ZFSet.mem_union.2 ∘ Or.inl
      exact (mem_relationImage _ _ _ _).2 ⟨bounds.1, node, used,
        (pair_mem_capExceptionRelation false Used Labels P r c caps node label).2
          ⟨used, bounds.1, cap, bounds.2, entry, negative, below⟩⟩
    · intro profile used negative positive
      apply good
      apply ZFSet.mem_union.2 ∘ Or.inl
      apply ZFSet.mem_union.2 ∘ Or.inr
      exact (mem_relationImage _ _ _ _).2 ⟨bounds.1, profile, used,
        (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile label).2
          ⟨used, bounds.1, cap, bounds.2, entry, negative, positive⟩⟩

end FinalInsertionFamiliesCode
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




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
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

theorem semanticStructuralPrefixAction_subhistory_property
    {gamma : ZFSet.{u}} (hGamma : gamma ∈ M.sets) (gammaOrdinal : ordinalSetProperty gamma)
    (alphaGamma : alpha ⊆ gamma) (gammaSubset : gamma ⊆ stages)
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop) :
    let historyGamma := graphRestriction gamma history
    let hhGamma := M.graphRestriction_mem unions separation hGamma hh
    let traceGamma := trace.restrict gammaOrdinal gammaSubset
    let packedGamma := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 gamma historyGamma
    Property (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packedGamma))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packedGamma))
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hhGamma traceGamma hAlpha cutOrdinal alphaGamma) ↔
    Property Q (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked)
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset) := by
  dsimp only
  have inner := M.semanticStructuralPrefixAction_restricted_property c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows (M.graphRestriction_mem unions separation hGamma hh)
    (trace.restrict gammaOrdinal gammaSubset) hAlpha cutOrdinal alphaGamma Property
  have outer := M.semanticStructuralPrefixAction_restricted_property c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset Property
  let Step := fun level prior stage => stage =
    M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 level prior
  let Applied := fun (h : ZFSet.{u}) (ground : h ∈ M.sets)
      (tr : OrdinalRecursionTrace Step alpha h) =>
    Property (M.refinementHistoryForcing c.carrier T alpha
      (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 alpha h))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha h))
      (M.semanticStructuralAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hAlpha ground cutOrdinal tr)
  have congruent (h1 h2 : ZFSet.{u}) (equal : h1 = h2)
      (ground1 : h1 ∈ M.sets) (ground2 : h2 ∈ M.sets)
      (trace1 : OrdinalRecursionTrace Step alpha h1) (trace2 : OrdinalRecursionTrace Step alpha h2) :
      Applied h1 ground1 trace1 ↔ Applied h2 ground2 trace2 := by
    subst h2
    rfl
  have aligned := congruent _ _ (graphRestriction_restrict alphaGamma)
    (M.graphRestriction_mem unions separation hAlpha (M.graphRestriction_mem unions separation hGamma hh))
    (M.graphRestriction_mem unions separation hAlpha hh)
    ((trace.restrict gammaOrdinal gammaSubset).restrict cutOrdinal alphaGamma)
    (trace.restrict cutOrdinal subset)
  exact inner.symm.trans (aligned.trans outer)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainPersistence
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

theorem semanticStructuralPrefix_representedDomain_ground_downward :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (idx : ZFSet.{u}), idx ∈ M.sets → ∀ (U Rc u : (M.nameDomain lower).names),
    let upper := M.refinementHistoryForcing c.carrier T stages packed
    let D := M.representedDomainConditions lower upper
      (refinementDataHistoryLevels stages packed T) alpha T valid idx U Rc u
    D ∈ M.sets ∧ D ⊆ upper ∧
      ∀ p q, ZFSet.pair q p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed →
        p ∈ D → q ∈ D := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro idx hIdx U Rc u
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have lowerCarrier : lower.carrier ∈ M.sets := fields 7
  have lowerOrder : lower.conditionOrder ∈ M.sets := fields 8
  have hUpper := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  refine ⟨M.representedDomainConditions_mem lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels hAlpha hT valid hIdx U Rc u,
    M.representedDomainConditions_subset lower _ _ _ _ valid idx U Rc u, ?_⟩
  intro p q below represented
  have shapes := ZFSet.pair_mem_prod.1
    ((M.refinementHistoryOrder_partialOrder c.conditionOrder_code T stages packed).relation below)
  obtain ⟨row, _, A, _, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed shapes.2)
  obtain ⟨newRow, _, newA, _, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed shapes.1)
  have orderFacts := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    newRow newA row A).1 below
  let pCut : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A))
    ((run).carriers.cut_mem orderFacts.2.1 member)
  let qCut : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair newRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha newA))
    ((run).carriers.cut_mem orderFacts.1 member)
  have pCode : lower.encode pCut = ZFSet.pair row
      (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A) := SetMembers.raw_ofMem _ _
  have qCode : lower.encode qCut = ZFSet.pair newRow
      (assignmentCut (refinementDataHistoryLevels stages packed T) alpha newA) := SetMembers.raw_ofMem _ _
  have cutBelow : qCut ≤ pCut := by
    change ZFSet.pair (lower.encode qCut) (lower.encode pCut) ∈ _
    rw [qCode, pCode]
    exact (run).cut_order_le ordinal cutOrdinal subset below
  have branches := (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels hAlpha hT valid hIdx U Rc u row A pCut pCode).1 represented
  apply (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels hAlpha hT valid hIdx U Rc u newRow newA qCut qCode).2
  refine ⟨orderFacts.1, ?_⟩
  rcases branches.2 with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
  · exact Or.inl (fun r belowR => inactive r (belowR.trans cutBelow))
  · exact Or.inr ⟨Name.forcesMem_mono active cutBelow, v, w, hv, hw,
      orderFacts.2.2.2 literal, Name.forcesEq_mono equal cutBelow⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStructuralLateProfileExclusions
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

theorem structural_compatible_insertion_with_late_profiles
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable)
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  ∀ (row : SetMembers c.carrier) (A : ZFSet.{u}),
    ZFSet.pair (c.encode row) A ∈ upperQ →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (ZFSet.pair (c.encode row) A) →
  ∀ (V E D0 : SetMembers geometry.carrier) (generators lateProfiles : ZFSet.{u}),
    V < E → V ≤ D0 → generators ∈ M.sets → generators ⊆ geometry.carrier →
    generators.Nonempty → (∀ z ∈ generators, ZFSet.pair (s.encode E) z ∈ geometry.order) →
    lateProfiles ∈ M.sets → M.groundEmbeddable lateProfiles ZFSet.omega →
    (∀ profile ∈ lateProfiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph profile) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) → i ≤ D0) →
    (∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A indices lifted S s.carrier mu
      s.nonbottom.carrier s.conditionOrder anchors tuples) →
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
  F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
    generators ⊆ F ∧
    (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
      generators ⊆ filter → F ⊆ filter) ∧
    (∀ x ∈ F, ZFSet.pair (s.encode E) x ∈ geometry.order) ∧
  ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
    ∃ family : FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
      geometry.meetGraph geometry.action (s.encode V) (s.encode E) (s.encode D0) F caps actors,
  ∃ badComp ∈ M.sets, badComp ⊆ Labels ∧ M.groundEmbeddable badComp ZFSet.omega ∧
  ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ badComp ⊆ bad ∧
    (∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
      ∀ profile ∈ lateProfiles, s.encode V ∉ profile → cap ∉ profile) ∧
    (∃ label : SetMembers Labels, SetMembers.raw label ∉ bad) ∧
    ∀ label : SetMembers Labels, SetMembers.raw label ∉ bad →
      let h := family.decodedActors label
      let cap := family.decodedCaps label
      h ∈ a.principalFix V ∧ V < cap ∧ ¬ E ≤ cap ∧ a.iso h D0 ≤ cap ∧
      (∀ v : SetMembers geometry.carrier, E ≤ v →
        (s.encode v ∈ F → cap ≤ v) ∧
        (s.encode v ∉ F → ZFSet.pair (ZFSet.pair (s.encode cap) (s.encode v))
          (s.encode V) ∈ geometry.meetGraph)) ∧
      let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A
      ∃ commonRow : SetMembers c.carrier,
        SetMembers.raw commonRow = SetMembers.raw row ∪ SetMembers.raw (act.iso h row) ∧
        ZFSet.pair (c.encode commonRow) (A ∪ movedA) ∈ upperQ ∧
        ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA)) (ZFSet.pair (c.encode row) A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed ∧
        ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA))
          (ZFSet.pair (c.encode (act.iso h row)) movedA) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed := by
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared V E D0 generators lateProfiles lower bound
    hGenerators generatorSubset generatorNonempty above hProfiles smallProfiles profileFilters rowD dataD
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have labelGround : Labels ∈ M.sets := labels.symm ▸ spec.1
  have labelLarge : ¬ M.groundEmbeddable Labels ZFSet.omega := labels.symm ▸ spec.2.2.2
  have emptyGround := M.empty_mem ⟨s.carrier, hL⟩
  have emptySmall := M.empty_groundEmbeddable ZFSet.omega ⟨s.carrier, hL⟩
  have rawRowD : ∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) →
      ZFSet.pair (s.encode i) (s.encode D0) ∈ geometry.order := fun i hi => rowD i hi
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, preparedProfileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, badComp, hBadComp, badCompSubset, badCompSmall, containsExtra, good, available, unionsFor⟩ :=
    fulfilled.structural_compatible_insertion_unions collection infinite choice small columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace row A condition prepared
      generators (s.encode V) (s.encode E) (s.encode D0) ∅
      labelGround hGenerators generatorSubset generatorNonempty (s.encode_mem V)
      (s.encode_mem E) (s.encode_mem D0) (le_of_lt lower) (not_le_of_gt lower) bound above
      emptyGround emptySmall (fun _ member => (ZFSet.notMem_empty _ member).elim) rawRowD dataD
  obtain ⟨bad, hBad, badSubset, badSmall, containsComp, lateGood⟩ :=
    family.exists_ground_countable_exceptions M pairing unions powers separation infinite choice
      labelGround hL geometry.order_ground (M.transitive hL (s.encode_mem V)) hCaps
      emptyGround hProfiles hBadComp geometry.meet
      (fun _ member => (ZFSet.notMem_empty _ member).elim)
      profileFilters emptySmall smallProfiles badCompSmall badCompSubset
  have survivor : ∃ label : SetMembers Labels, SetMembers.raw label ∉ bad := by
    classical
    by_contra none
    apply labelLarge
    have equal : bad = Labels := by
      apply ZFSet.ext
      intro label
      refine ⟨fun member => badSubset member, ?_⟩
      intro member
      by_contra outside
      exact none ⟨SetMembers.ofMem label member, by simpa only [SetMembers.raw_ofMem] using outside⟩
    rwa [equal] at badSmall
  refine ⟨filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, badComp, hBadComp, badCompSubset, badCompSmall, bad, hBad, badSubset, badSmall,
    containsComp, fun label cap entry outside => (lateGood label cap entry outside).2, survivor, ?_⟩
  intro label outside
  have compGood : SetMembers.raw label ∉ badComp := fun member => outside (containsComp member)
  let h := family.decodedActors label
  let cap := family.decodedCaps label
  have actorEdge := family.decodedActors_entry label
  have capEdge := family.decodedCaps_entry label
  have fixed : h ∈ a.principalFix V := by
    intro v hv
    exact (geometry.action_code.act_eq_iff h v v).2
      (family.fixes _ _ actorEdge _ (s.encode_mem v) hv)
  have profile := family.profiles _ _ capEdge
  have strictCap : V < cap := lt_iff_le_not_ge.2 ⟨profile.target_below_cap, profile.cap_not_below_target⟩
  have movedBound : a.iso h D0 ≤ cap :=
    family.dominates _ _ _ actorEdge capEdge _ (s.encode_mem _) (geometry.action_code.act_mem h D0)
  exact ⟨fixed, strictCap, profile.separator_not_below_cap, movedBound,
    fun v aboveV => family.tests geometry.meet.order filterCode capEdge (s.encode_mem v) aboveV,
    unionsFor label compGood⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalPrefixCompatibleCaps
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

theorem structural_prefix_compatible_caps
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable)
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
      let indices := refinementDataHistoryIndices alpha lowerPacked
      let anchors := refinementIndexFieldGraph indices s.carrier 2
      ∀ (r : SetMembers Q) (row : SetMembers c.carrier) (A : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode row) A →
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) →
      ∀ (V E D0 : SetMembers geometry.carrier) (B Pb Profiles : ZFSet.{u}),
        V < E → V ≤ D0 →
        MeetFilterCode geometry.carrier geometry.order geometry.meetGraph Pb →
        B ∈ M.sets → B.Nonempty → B ⊆ testedMeetFilter Pb geometry.order (s.encode E) →
        M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph B =
          testedMeetFilter Pb geometry.order (s.encode E) →
        Profiles ∈ M.sets → M.groundEmbeddable Profiles ZFSet.omega →
        (∀ profile ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph profile) →
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) → i ≤ D0) →
        (∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A indices lifted S s.carrier mu
          s.nonbottom.carrier s.conditionOrder anchors tuples) →
      ∃ (g : SetMembers geometry.actors) (cap : SetMembers geometry.carrier) (q : SetMembers Q),
        q ≤ r ∧ q ≤ localAct.iso g r ∧ g ∈ a.principalFix V ∧ V < cap ∧ ¬ E ≤ cap ∧
        a.iso g D0 ≤ cap ∧
        (∀ v : SetMembers geometry.carrier,
          s.encode v ∈ testedMeetFilter Pb s.conditionOrder (s.encode E) → cap ≤ v) ∧
        (∀ v : SetMembers geometry.carrier, E ≤ v →
          s.encode v ∉ testedMeetFilter Pb s.conditionOrder (s.encode E) → geometry.meet.smallMeet cap v = V) ∧
        (∀ profile ∈ Profiles, s.encode V ∉ profile → s.encode cap ∉ profile) ∧
        let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) lifted squared alpha history (b.encode g) A
        ∃ commonRow : SetMembers c.carrier,
          SetMembers.raw commonRow = SetMembers.raw row ∪ SetMembers.raw (act.iso g row) ∧
          lower.encode q = ZFSet.pair (c.encode commonRow) (A ∪ movedA) := by
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let indices := refinementDataHistoryIndices alpha lowerPacked
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro r row A rCode prepared V E D0 B Pb Profiles strict bound filter hB nonempty contained
    generated hProfiles smallProfiles profileFilters rowD dataD
  have packedEq := (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared alpha history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared subset)
  have inNodes : B ⊆ geometry.carrier := fun z hz =>
    filter.subset ((mem_testedMeetFilter Pb geometry.order (s.encode E) z).1 (contained hz)).1
  have above : ∀ z ∈ B, ZFSet.pair (s.encode E) z ∈ geometry.order := fun z hz =>
    ((mem_testedMeetFilter Pb geometry.order (s.encode E) z).1 (contained hz)).2
  have condition : ZFSet.pair (c.encode row) A ∈ Q := rCode ▸ SetMembers.raw_mem r
  obtain ⟨filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, badComp, hBadComp, badCompSubset, badCompSmall, bad, hBad, badSubset, badSmall,
    includesComp, goodProfiles, survivor, compatible⟩ :=
    fulfilled.structural_compatible_insertion_with_late_profiles collection infinite choice labels small
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      alpha (graphRestriction alpha history) hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
      cutOrdinal (trace.restrict cutOrdinal subset) row A
      (by
        change ZFSet.pair (c.encode row) A ∈ M.refinementHistoryForcing c.carrier lifted alpha
          (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
            (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history))
        rw [packedEq]
        exact condition)
      (by
        change StoredPreparedConditionCode M c.carrier lifted alpha
          (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
            (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history))
          s.carrier (ZFSet.pair (c.encode row) A)
        rw [packedEq]
        exact rCode ▸ prepared)
      V E D0 B Profiles strict bound hB inNodes nonempty above hProfiles smallProfiles profileFilters rowD
      (by
        let restrictedPacked := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
          (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history)
        change ∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A
          (refinementDataHistoryIndices alpha restrictedPacked) lifted S s.carrier mu
          s.nonbottom.carrier s.conditionOrder
          (refinementIndexFieldGraph (refinementDataHistoryIndices alpha restrictedPacked) s.carrier 2) tuples
        dsimp only [restrictedPacked]
        rw [packedEq]
        exact dataD)
  obtain ⟨label, outside⟩ := survivor
  let g := family.decodedActors label
  let cap := family.decodedCaps label
  have capEdge := family.decodedCaps_entry label
  obtain ⟨fixed, strictCap, notAbove, movedBound, tested, commonRow, rowCode,
      qCondition, qBelow, qMovedBelow⟩ := compatible label outside
  rw [M.structuralAssignmentImage_history_restrict, packedEq] at qCondition qBelow qMovedBelow
  let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared alpha history (b.encode g) A
  let q : SetMembers Q := SetMembers.ofMem (ZFSet.pair (c.encode commonRow) (A ∪ movedA)) qCondition
  have qCode : lower.encode q = ZFSet.pair (c.encode commonRow) (A ∪ movedA) :=
    SetMembers.raw_ofMem _ _
  have actedCode := M.semanticStructuralPrefixAction_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset g r row A rCode
  have leR : q ≤ r := by
    change ZFSet.pair (lower.encode q) (lower.encode r) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder lifted alpha lowerPacked
    rw [qCode, rCode]
    exact qBelow
  have leMoved : q ≤ localAct.iso g r := by
    change ZFSet.pair (lower.encode q) (SetMembers.raw (localAct.iso g r)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder lifted alpha lowerPacked
    rw [qCode, actedCode]
    exact qMovedBelow
  refine ⟨g, cap, q, leR, leMoved, fixed, strictCap, notAbove, movedBound, ?_, ?_, ?_,
    commonRow, rowCode, qCode⟩
  · intro v member
    rw [geometry.decoded_order_eq] at member
    have ev : E ≤ v := ((mem_testedMeetFilter Pb geometry.order (s.encode E) (s.encode v)).1 member).2
    apply (tested v ev).1
    rwa [generated]
  · intro v ev absent
    rw [geometry.decoded_order_eq] at absent
    apply (geometry.meet.smallMeet_eq_iff cap v V).2
    apply (tested v ev).2
    rwa [generated]
  · exact goodProfiles _ _ capEdge outside

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalPersistentAssignmentLabels
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

theorem structural_successor_represented_of_nonvisible
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
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
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) (graphRestriction (insert alpha alpha) packed) →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ pCut r0 : SetMembers Q,
      let next := graphRestriction (insert alpha alpha) packed
      let upper := M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) next
      let levels := refinementDataHistoryLevels (insert alpha alpha) next lifted
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → r0 ≤ pCut →
      Name.ForcesMem r0 u.val U.val →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ lifted → z.val.val ∈ lifted →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        ∀ q, q ≤ r0 → ¬ Name.ForcesEq q
          (Name.refinementClass lifted localValid Rc.val u.val)
          (Name.refinementClass lifted localValid Rc.val v.val)) →
      (∀ q, q ≤ r0 → ¬ Name.ForcesMem q
        (Name.refinementClass lifted localValid Rf.val u.val)
        (M.niceVisibilityName localAct lower lifted (a.principalFix V))) →
      ∃ newRow newA : ZFSet.{u},
        ZFSet.pair newRow newA ∈
          M.representedDomainConditions lower upper levels alpha lifted localValid idx U Rc u ∧
        ZFSet.pair (ZFSet.pair newRow newA) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted (insert alpha alpha) next ∧
        A ⊆ newA := by
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
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let localValid := M.refinementHistoryRowNameFamily_valid c
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
  intro row A condition V E U Rf Rc u inI hu pCut r0 cutCode r0p active fresh absent
  let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
  let J := M.fixedIndexAugmentedRequests localAct lower s a alpha lifted squared localValid idx A Rc.val u.val
  let N := M.niceSupportNameCodes localAct lower lifted a.principalFix
  obtain ⟨_hJ, _smallJ, k, _hk, _function, profilesGround, profilesSmall, profileFilters,
    Pb, _basis, _representatives, _coarseEntry, pbMember,
    generators, hGenerators, _smallGenerators, generatorsNonempty, generatorsSubset, generatedEq,
    r, rr0, rowR, lowerA, rCode, prepared,
    D0, eD0, uSupport, rowsBound, dataBound, coarseDecisions, _allDecisions, oldProfiles⟩ :=
    fulfilled.successor_prepared_insertion_profiles collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member
      row A condition V E U Rf Rc u inI hu r0
  let system := M.semanticStructuralPrefix_refinementSystem c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member
  have strict := ((system.indices.typed_entries V E U Rf Rc).1 inI).1
  have vD0 := strict.le.trans eD0
  obtain ⟨g, cap, q, qr, qgr, fixed, _above, _notAbove, movedBound,
    capPositive, capNegative, avoidProfiles, _unionCoordinates⟩ :=
    fulfilled.structural_prefix_compatible_caps collection infinite choice labels small
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member
      r rowR lowerA rCode prepared V E D0 generators Pb (M.certificateProfileImage J s.carrier N k)
      strict vD0 (profileFilters Pb pbMember) hGenerators generatorsNonempty generatorsSubset
      generatedEq profilesGround profilesSmall profileFilters rowsBound dataBound
  have descent := fulfilled.structural_prefix_descent collection infinite choice small smallD irreflexive
    columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace alpha member
  obtain ⟨w, _acted, _hw, _activeW, _groundD, newRow, newLowerA, _qCode,
    _upperMember, edge, retained, _newAssignment, _cut, _self, inD⟩ :=
    M.semanticStructuralSuccessor_represented_absentLift_actor c act b s a ⊥ directed
      lifted squared (c.encode ⊤) pairing unions powers separation collection
      carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega
      valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace member
      infinite choice small condition geometry.meet.smallMeet descent
      V E D0 cap U Rf Rc u Pb inI hu vD0 uSupport g fixed movedBound
      pCut r q cutCode (rr0.trans r0p) qr qgr (Name.forcesMem_mono active rr0)
      capPositive capNegative coarseDecisions
      (fun p pr => absent p (pr.trans rr0))
      (by
        intro v z hv hz old
        obtain ⟨F, _B, _f, _entry, memberF, decisions⟩ := oldProfiles v z hv hz old
        exact ⟨fun p pr => fresh v z hv hz old p (pr.trans rr0),
          F, decisions, avoidProfiles F memberF⟩)
  exact ⟨newRow, _, inD, edge, retained⟩






theorem structural_represented_domain_dense_oai
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
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
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      let next := graphRestriction (insert alpha alpha) packed
      let upper := M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) next
      let levels := refinementDataHistoryLevels (insert alpha alpha) next lifted
      let Dt := M.representedDomainConditions lower upper levels alpha lifted localValid idx U Rc u
      Dt ∈ M.sets ∧ Dt ⊆ upper ∧
        (∀ p q, ZFSet.pair q p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder lifted
          (insert alpha alpha) next → p ∈ Dt → q ∈ Dt) ∧
        letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted (insert alpha alpha) next
        Dense {p : SetMembers upper | SetMembers.raw p ∈ Dt} := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed
    alpha member hAlpha cutOrdinal subset lowerPacked Q
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  intro lower localAct localValid
  let gamma := insert alpha alpha
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have gammaOrdinal : ordinalSetProperty gamma := ordinalSetProperty_succ cutOrdinal
  have alphaGamma : alpha ⊆ gamma := fun _ hx => ZFSet.mem_insert_of_mem _ hx
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset _ old
  let historyGamma := graphRestriction gamma history
  have hhGamma : historyGamma ∈ M.sets := M.graphRestriction_mem unions separation hGamma hh
  have traceGamma := trace.restrict gammaOrdinal gammaSubset
  let packedGamma := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared gamma historyGamma
  have packedGammaEq : packedGamma = graphRestriction gamma packed :=
    (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared gamma history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared gammaSubset)
  let next := graphRestriction gamma packed
  let upper := M.refinementHistoryForcing c.carrier lifted gamma next
  let levels := refinementDataHistoryLevels gamma next lifted
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder lifted gamma next
  let Property : ∀ (domainSet : ZFSet.{u}) (orderQ : PartialOrder (SetMembers domainSet)),
      @PosetAction (SetMembers geometry.actors) _ (SetMembers domainSet) orderQ → Prop :=
    fun domainSet orderQ actionQ =>
      letI := orderQ
      ∀ topQ : OrderTop (SetMembers domainSet),
      letI := topQ
      let lower := SetMembers.presentation domainSet
      ∀ localValid : ∀ z ∈ lifted, IsName lower z,
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices actionQ lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      let Dt := M.representedDomainConditions lower upper levels alpha lifted localValid idx U Rc u
      Dt ∈ M.sets ∧ Dt ⊆ upper ∧
        (∀ p q, ZFSet.pair q p ∈ upperOrder → p ∈ Dt → q ∈ Dt) ∧
        ∀ p ∈ upper, ∃ q ∈ Dt, ZFSet.pair q p ∈ upperOrder
  let QGamma := M.refinementHistoryForcing c.carrier lifted alpha (graphRestriction alpha packedGamma)
  let gammaOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma)
  let runGamma := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared gammaOrdinal traceGamma
  let topGamma := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma) (runGamma.carriers.restrict cutOrdinal alphaGamma)
    cutOrdinal carrier (c.encode ⊤) topMem topRows
  let validGamma := M.refinementHistoryRowNameFamily_valid c
    (runGamma.carriers.restrict cutOrdinal alphaGamma) cutOrdinal carrier lifted valid1
  let actionGamma := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hhGamma traceGamma hAlpha cutOrdinal alphaGamma
  have inside : Property QGamma gammaOrder actionGamma := by
    intro topQ
    have topEq : topQ = topGamma := Subsingleton.elim _ _
    subst topQ
    dsimp only
    intro validQ
    have validEq : validQ = validGamma := Subsingleton.elim _ _
    subst validQ
    intro V E U Rf Rc u inI hu
    let lowerGamma := SetMembers.presentation QGamma
    let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
    let upperGamma := M.refinementHistoryForcing c.carrier lifted gamma packedGamma
    let levelsGamma := refinementDataHistoryLevels gamma packedGamma lifted
    let orderGamma := M.refinementHistoryOrder c.carrier c.conditionOrder lifted gamma packedGamma
    have upperEq : upperGamma = upper := by dsimp only [upperGamma, upper, next]; rw [packedGammaEq]
    have levelsEq : levelsGamma = levels := by dsimp only [levelsGamma, levels, next]; rw [packedGammaEq]
    have orderEq : orderGamma = upperOrder := by dsimp only [orderGamma, upperOrder, next]; rw [packedGammaEq]
    let DtGamma := M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u
    let DtOuter := M.representedDomainConditions lowerGamma upper levels alpha lifted validGamma idx U Rc u
    have domainEq : DtGamma = DtOuter := by
      dsimp only [DtGamma, DtOuter]
      rw [upperEq, levelsEq]
    have moveMember {z : ZFSet.{u}} (h : z ∈ DtGamma) : z ∈ DtOuter :=
      Eq.mp (congrArg (fun bound : ZFSet.{u} => z ∈ bound) domainEq) h
    have moveOrder {z p : ZFSet.{u}} (h : ZFSet.pair z p ∈ orderGamma) :
        ZFSet.pair z p ∈ upperOrder :=
      Eq.mp (congrArg (fun relation : ZFSet.{u} => ZFSet.pair z p ∈ relation) orderEq) h
    have selfRestrict : graphRestriction gamma packedGamma = packedGamma :=
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared (fun _ h => h : gamma ⊆ gamma)).symm
    have hIdx := M.refinementIndexCode_mem pairing hAlpha
      (M.transitive hL (s.encode_mem V)) (M.transitive hL (s.encode_mem E))
      U.property Rf.property Rc.property
    obtain ⟨groundD, subsetD, downwardD⟩ :=
      M.semanticStructuralPrefix_representedDomain_ground_downward c act b s a ⊥ directed lifted squared
        (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
        hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
        children1 children2 topMem topRows hGamma hhGamma gammaOrdinal traceGamma
        (ZFSet.mem_insert alpha alpha) idx hIdx U Rc u
    change M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u ∈ M.sets at groundD
    change M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u ⊆ upperGamma at subsetD
    change ∀ p q, ZFSet.pair q p ∈ orderGamma →
      p ∈ M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u →
      q ∈ M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u at downwardD
    rw [upperEq, levelsEq] at groundD subsetD
    rw [upperEq, levelsEq, orderEq] at downwardD
    refine ⟨groundD, subsetD, downwardD, ?_⟩
    intro p hp
    have hpGamma : p ∈ upperGamma := upperEq.symm ▸ hp
    obtain ⟨row, _rowMem, A, _assignmentsMem, pCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape c.carrier lifted gamma packedGamma hpGamma)
    subst p
    obtain ⟨pCut, r, cutCode, below, lowerRow, lowerA, _rCode,
      _liftedCondition, liftedBelow, _retained, _exactCut, represented | fresh⟩ :=
      M.semanticStructuralSuccessor_represented_or_fresh b s a ⊥ directed
        pairing unions powers separation collection infinite choice
        (ZFSet.prod s.nonbottom.carrier columns) coordinates act lifted squared (c.encode ⊤)
        forcingAction hG hL order graph nodeMaps supports hLifted hSquared
        valid1 valid2 closed1 closed2 children1 children2 topMem topRows
        gamma historyGamma hGamma hhGamma gammaOrdinal traceGamma alpha (ZFSet.mem_insert alpha alpha)
        hpGamma V E U Rf Rc inI u.val hu
    · exact ⟨ZFSet.pair lowerRow (assignmentSplice levelsGamma alpha lowerA A),
        moveMember represented, moveOrder liftedBelow⟩
    · obtain ⟨active, coarseFresh⟩ := fresh
      have successorCondition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted
          (insert alpha alpha) (graphRestriction (insert alpha alpha) packedGamma) := by
        change ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted gamma (graphRestriction gamma packedGamma)
        rw [selfRestrict]
        exact hpGamma
      have successorCut : lowerGamma.encode pCut = ZFSet.pair row
          (assignmentCut (refinementDataHistoryLevels (insert alpha alpha)
            (graphRestriction (insert alpha alpha) packedGamma) lifted) alpha A) := by
        change lowerGamma.encode pCut = ZFSet.pair row
          (assignmentCut (refinementDataHistoryLevels gamma (graphRestriction gamma packedGamma) lifted) alpha A)
        rw [selfRestrict]
        exact cutCode
      obtain ⟨q, qr, activeQ, freshQ, positive | negative⟩ :=
        M.semanticStructuralSuccessor_decide_represented_visibleLift c act b s a ⊥ directed lifted squared
          (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
          hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
          children1 children2 topMem topRows hGamma hhGamma gammaOrdinal traceGamma
          (ZFSet.mem_insert alpha alpha) infinite choice small successorCondition
          V E U Rf Rc u inI hu pCut r successorCut below active
          (fun v z hv hz old k kr => coarseFresh v.val z.val hv hz old k kr)
      · obtain ⟨_existsLift, _w, _hw, _activeU, _activeW, newRow, newA, _qCode,
          _newCondition, newBelow, _retained, _literal, _exactCut, _selfEqual, inD⟩ := positive
        rw [selfRestrict] at inD newBelow
        exact ⟨_, moveMember inD, moveOrder newBelow⟩
      · obtain ⟨_absentLift, _fineMember, _mapEdge, nonvisible⟩ := negative
        obtain ⟨newRow, newA, inD, newBelow, _retained⟩ :=
          fulfilled.structural_successor_represented_of_nonvisible collection infinite choice labels
            small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared
            valid1 valid2 closed1 closed2 children1 children2
            gamma historyGamma hGamma hhGamma gammaOrdinal traceGamma alpha (ZFSet.mem_insert alpha alpha)
            row A successorCondition V E U Rf Rc u inI hu pCut q successorCut (qr.trans below)
            activeQ freshQ nonvisible
        rw [selfRestrict] at inD newBelow
        exact ⟨ZFSet.pair newRow newA, moveMember inD, moveOrder newBelow⟩
  have outside := (M.semanticStructuralPrefixAction_subhistory_property c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset hGamma gammaOrdinal alphaGamma gammaSubset Property).1 inside
  intro V E U Rf Rc u indexCode inI hu nextOuter upperOuter levelsOuter domainOuter
  obtain ⟨groundD, subsetD, downwardD, denseD⟩ := outside inferInstance localValid V E U Rf Rc u inI hu
  refine ⟨groundD, subsetD, downwardD, ?_⟩
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted gamma next
  intro p
  obtain ⟨q, hq, below⟩ := denseD (SetMembers.raw p) (SetMembers.raw_mem p)
  let qTyped : SetMembers upper := SetMembers.ofMem q (subsetD hq)
  have qCode : SetMembers.raw qTyped = q := SetMembers.raw_ofMem _ _
  refine ⟨qTyped, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw qTyped) (SetMembers.raw p) ∈ upperOrder
    rwa [qCode]
  · change SetMembers.raw qTyped ∈ M.representedDomainConditions lower upper levels alpha lifted
      localValid (refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val) U Rc u
    rw [qCode]
    exact hq






end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_represented_domain_dense_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_represented_domain_dense_oai.{u, v}
