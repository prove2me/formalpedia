-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:37:22.289625+00:00
-- url     : https://prove2.me/submissions/3101a84d-da0b-4802-802b-d7df50cb9fb7

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_represented_domain_dense
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralAssignmentLabel_injection_package
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralTrace_refinementOutputs

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_EvaluatedDomains
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace Name

open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

theorem mem_eval_assemble (H : Set P) {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) (x : ZFSet.{u}) :
    x ∈ eval H (assemble names conditions) ↔
      ∃ i, conditions i ∈ H ∧ eval H (names i) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨i, rfl, rfl⟩ := (entry_assemble names conditions σ p).1 entry
    exact ⟨i, hp, eq⟩
  · rintro ⟨i, hp, eq⟩
    exact ⟨names i, conditions i,
      (entry_assemble names conditions _ _).2 ⟨i, rfl, rfl⟩, hp, eq⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forcesEq_refl (σ : Name s) (p : P) : ForcesEq p σ σ := by
  induction σ using inductionOn generalizing p with
  | step σ ih =>
    rw [ForcesEq]
    constructor
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩

theorem forcesMem_entry {σ τ : Name s} {r : P} (entry : Entry σ τ r) :
    ForcesMem r σ τ := forcesMem_of_witness ⟨σ, r, entry, le_rfl, forcesEq_refl σ r⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem eval_singleton (H : Set P) (one : P) (hone : one ∈ H) (σ : Name s) :
    eval H (singleton one σ) = {eval H σ} := by
  apply ZFSet.ext
  intro x
  rw [singleton, mem_eval_assemble, ZFSet.mem_singleton]
  constructor
  · rintro ⟨_, _, eq⟩
    exact eq.symm
  · intro eq
    exact ⟨(), hone, eq.symm⟩

theorem eval_unorderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (unorderedPair one σ τ) = {eval H σ, eval H τ} := by
  apply ZFSet.ext
  intro x
  rw [unorderedPair, mem_eval_assemble, ZFSet.mem_pair]
  constructor
  · rintro ⟨b, _, eq⟩
    cases b with
    | false => exact Or.inr eq.symm
    | true => exact Or.inl eq.symm
  · rintro (eq | eq)
    · exact ⟨true, hone, eq.symm⟩
    · exact ⟨false, hone, eq.symm⟩

theorem eval_orderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (orderedPair one σ τ) = ZFSet.pair (eval H σ) (eval H τ) := by
  rw [orderedPair, eval_unorderedPair H one hone,
    eval_singleton H one hone, eval_unorderedPair H one hone]
  rfl

end Name



end PartitionPilot.Forcing

end OAI
end

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



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompleteProjectionPredensity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v
variable {Upper : Type u} {Lower : Type v} [PartialOrder Upper] [PartialOrder Lower]

namespace CompleteProjection
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem dense_preimage {E : Set Lower} (dense : Dense E) :
    Dense {p : Upper | restriction p ∈ E} := by
  intro p
  obtain ⟨q, below, member⟩ := dense (restriction p)
  obtain ⟨r, rp, equal⟩ := projection.lift p q below
  refine ⟨r, rp, ?_⟩
  change restriction r ∈ E
  rw [equal]
  exact member

theorem projectedFilter_mem_iff (H : ConditionFilter Upper) (q : Lower) :
    (projection.projectedFilter H).mem q ↔
      ∃ p : Upper, H.mem p ∧ restriction p = q := by
  constructor
  · intro member
    exact ⟨inclusion q, member, projection.retract q⟩
  · rintro ⟨p, member, rfl⟩
    exact H.upward member (projection.le_include_restriction p)

end CompleteProjection
end



namespace Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable (s : Presentation P) (t : Presentation Q)
variable (pi : Q →o P) (inc : P ↪o Q) (projection : CompleteProjection pi inc)
include projection

theorem forcesEq_rename_completeProjection (q : Q) (σ τ : Name s) :
    ForcesEq q (rename t inc σ) (rename t inc τ) ↔ ForcesEq (pi q) σ τ := by
  induction σ using inductionOn generalizing τ q with
  | step σ ih =>
    rw [ForcesEq, ForcesEq]
    constructor
    · rintro ⟨left, right⟩
      constructor
      · intro ρ r hr p pq pr
        obtain ⟨v, vq, vp⟩ := projection.lift q p pq
        have vr : v ≤ inc r := (projection.le_include_iff v r).2 (vp.symm ▸ pr)
        have entry := (entry_rename t inc σ (rename t inc ρ) (inc r)).2 ⟨ρ, r, hr, rfl, rfl⟩
        obtain ⟨w, wv, ν, k, hk, wk, eq⟩ := left _ _ entry v vq vr
        obtain ⟨ν₀, k₀, old, rfl, rfl⟩ := (entry_rename t inc τ ν k).1 hk
        exact ⟨pi w, (pi.monotone wv).trans_eq vp, ν₀, k₀, old,
          (projection.le_include_iff w k₀).1 wk, (ih ρ r hr (q := w) (τ := ν₀)).1 eq⟩
      · intro ν k hk p pq pk
        obtain ⟨v, vq, vp⟩ := projection.lift q p pq
        have vk : v ≤ inc k := (projection.le_include_iff v k).2 (vp.symm ▸ pk)
        have entry := (entry_rename t inc τ (rename t inc ν) (inc k)).2 ⟨ν, k, hk, rfl, rfl⟩
        obtain ⟨w, wv, ρ, r, hr, wr, eq⟩ := right _ _ entry v vq vk
        obtain ⟨ρ₀, r₀, old, rfl, rfl⟩ := (entry_rename t inc σ ρ r).1 hr
        exact ⟨pi w, (pi.monotone wv).trans_eq vp, ρ₀, r₀, old,
          (projection.le_include_iff w r₀).1 wr, (ih ρ₀ r₀ old (q := w) (τ := ν)).1 eq⟩
    · rintro ⟨left, right⟩
      constructor
      · intro ρ r hr v vq vr
        obtain ⟨ρ₀, r₀, old, rfl, rfl⟩ := (entry_rename t inc σ ρ r).1 hr
        obtain ⟨p, pv, ν, k, hk, pk, eq⟩ :=
          left ρ₀ r₀ old (pi v) (pi.monotone vq) ((projection.le_include_iff v r₀).1 vr)
        obtain ⟨w, wv, wp⟩ := projection.lift v p pv
        refine ⟨w, wv, rename t inc ν, inc k,
          (entry_rename t inc τ (rename t inc ν) (inc k)).2 ⟨ν, k, hk, rfl, rfl⟩,
          (projection.le_include_iff w k).2 (wp.symm ▸ pk), ?_⟩
        exact (ih ρ₀ r₀ old (q := w) (τ := ν)).2 (wp.symm ▸ eq)
      · intro ν k hk v vq vk
        obtain ⟨ν₀, k₀, old, rfl, rfl⟩ := (entry_rename t inc τ ν k).1 hk
        obtain ⟨p, pv, ρ, r, hr, pr, eq⟩ :=
          right ν₀ k₀ old (pi v) (pi.monotone vq) ((projection.le_include_iff v k₀).1 vk)
        obtain ⟨w, wv, wp⟩ := projection.lift v p pv
        refine ⟨w, wv, rename t inc ρ, inc r,
          (entry_rename t inc σ (rename t inc ρ) (inc r)).2 ⟨ρ, r, hr, rfl, rfl⟩,
          (projection.le_include_iff w r).2 (wp.symm ▸ pr), ?_⟩
        exact (ih ρ r hr (q := w) (τ := ν₀)).2 (wp.symm ▸ eq)

end Name



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionGenericity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem ordinary_generic_meets_coded_dense (H : ConditionFilter P)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain s))) {E : Set P}
    (code : s.subset E ∈ M.sets) (dense : Dense E) : H.Meets E := by
  have emptyGround : (∅ : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨s.subset E, code⟩
  let witness : Name s := ⟨ZFSet.prod {∅} (s.subset E), IsName.mk
    (by
      intro z hz
      obtain ⟨x, hx, y, hy, shape⟩ := ZFSet.mem_prod.1 hz
      obtain ⟨p, _hp, rfl⟩ := (s.mem_subset E y).1 hy
      have empty : x = ∅ := ZFSet.mem_singleton.1 hx
      exact ⟨∅, p, shape.trans (congrArg (fun v => ZFSet.pair v (s.encode p)) empty)⟩)
    (by
      intro y p member
      have empty : y = ∅ := ZFSet.mem_singleton.1 (ZFSet.pair_mem_prod.1 member).1
      exact empty.symm ▸ (Name.empty s).property)⟩
  have witnessGround : witness.val ∈ M.sets := M.prod_mem pairing unions powers separation
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing emptyGround emptyGround) code
  have entries (sigma : Name s) (p : P) :
      Name.Entry sigma witness p ↔ sigma = Name.empty s ∧ p ∈ E := by
    constructor
    · intro entry
      have components : sigma.val ∈ {∅} ∧ s.encode p ∈ s.subset E :=
        ZFSet.pair_mem_prod.1 entry
      exact ⟨Subtype.ext (ZFSet.mem_singleton.1 components.1),
        (s.encode_mem_subset E p).1 components.2⟩
    · rintro ⟨rfl, member⟩
      exact ZFSet.pair_mem_prod.2
        ⟨ZFSet.mem_singleton.2 rfl, (s.encode_mem_subset E p).2 member⟩
  have forced (p : P) : Name.ForcesMem p (Name.empty s) witness := by
    apply Name.forcesMem_of_dense
    intro q _qp
    obtain ⟨r, rq, member⟩ := dense q
    exact ⟨r, rq, Name.forcesMem_entry ((entries (Name.empty s) r).2 ⟨rfl, member⟩)⟩
  obtain ⟨p, hp⟩ := H.nonempty
  have member := Name.forcesMem_sound (M.nameDomain s) H
    (fun E hE => ordinary E (Or.inl hE)) emptyGround witnessGround hp (forced p)
  obtain ⟨sigma, q, entry, hq, _equal⟩ := (Name.mem_eval {r | H.mem r} witness _).1 member
  exact ⟨q, hq, ((entries sigma q).1 entry).2⟩

theorem ordinary_generic_meets_ground_dense (H : ConditionFilter P)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain s))) {D : ZFSet.{u}}
    (ground : D ∈ M.sets) (subset : D ⊆ s.carrier)
    (dense : Dense {p | s.encode p ∈ D}) : H.Meets {p | s.encode p ∈ D} := by
  have codeEq : s.subset (fun p => s.encode p ∈ D) = D := by
    apply ZFSet.ext
    intro z
    rw [s.mem_subset]
    constructor
    · rintro ⟨p, member, rfl⟩
      exact member
    · intro member
      obtain ⟨p, same⟩ := (s.mem_carrier z).1 (subset member)
      exact ⟨p, same.symm ▸ member, same⟩
  exact M.ordinary_generic_meets_coded_dense s pairing unions powers separation H ordinary
    (codeEq.symm ▸ ground) dense

end TransitiveGround



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NamePresentationEquivalences
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
universe u
variable {P : Type u} (s : Presentation P)

theorem encode_intoSet (B : ZFSet.{u}) (sub : s.carrier ⊆ B) (p : P) :
    (SetMembers.presentation B).encode (s.intoSet B sub p) = s.encode p :=
  SetMembers.raw_ofMem _ _

end PartitionPilot.SetRealization.Presentation

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentLabelNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [OrderTop P]
variable {s : Presentation P} (upper : Presentation Q) (incl : P → Q) (one : Q)

theorem entry_refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s)
    (sigma : Name upper) (p : Q) :
    Entry sigma (refinementAssignmentLabel upper incl one T valid idx Rf Rc) p ↔
      ∃ v w : Name s, v.val ∈ T ∧ w.val ∈ T ∧
        (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A) ∧
        orderedPair one (rename upper incl (refinementClass T valid Rc v))
          (rename upper incl (refinementClass T valid Rf w)) = sigma := by
  rw [refinementAssignmentLabel, entry_assemble]
  constructor
  · rintro ⟨a, equal, condition⟩
    refine ⟨⟨a.val.1.1.val, valid _ a.val.1.1.property⟩,
      ⟨a.val.1.2.val, valid _ a.val.1.2.property⟩,
      a.val.1.1.property, a.val.1.2.property, ?_, equal⟩
    exact condition ▸ a.property
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    exact ⟨⟨((⟨v.val, hv⟩, ⟨w.val, hw⟩), p), literal⟩, equal, rfl⟩

theorem mem_eval_refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s)
    (H : Set Q) (hone : one ∈ H) (z : ZFSet.{u}) :
    z ∈ eval H (refinementAssignmentLabel upper incl one T valid idx Rf Rc) ↔
      ∃ (p : Q) (v w : Name s), p ∈ H ∧ v.val ∈ T ∧ w.val ∈ T ∧
        (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A) ∧
        ZFSet.pair (eval {q | incl q ∈ H} (refinementClass T valid Rc v))
          (eval {q | incl q ∈ H} (refinementClass T valid Rf w)) = z := by
  rw [mem_eval]
  constructor
  · rintro ⟨sigma, p, entry, hp, equal⟩
    obtain ⟨v, w, hv, hw, literal, rfl⟩ :=
      (entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc sigma p).1 entry
    refine ⟨p, v, w, hp, hv, hw, literal, ?_⟩
    simpa only [eval_orderedPair H one hone, eval_rename] using equal
  · rintro ⟨p, v, w, hp, hv, hw, literal, equal⟩
    refine ⟨_, p, (entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc _ p).2
      ⟨v, w, hv, hw, literal, rfl⟩, hp, ?_⟩
    simpa only [eval_orderedPair H one hone, eval_rename] using equal

end PartitionPilot.Forcing.Name

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionAtomicTruth
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
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem rename_between_mem (s : Presentation P) (t : Presentation Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) : (Name.rename t f τ).val ∈ M.sets := by
  let U := s.carrier ∪ t.carrier
  let D := ZFSet.sep (fun x => x ∉ s.carrier) U
  let F := s.graph t f
  let G := F ∪ identityFunctionGraph D
  have subS : s.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inl hx)
  have subT : t.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inr hx)
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have hD : D ∈ M.sets := M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend s.carrier Fin.elim0) (Fin.cases hs (fun i => Fin.elim0 i)) hU
  have hG : G ∈ M.sets := M.binary_union_mem pairing unions hf
    (M.identityFunctionGraph_mem pairing unions powers separation hD)
  have ff := s.graph_isFunc t f
  have full : ZFSet.IsFunc U U G := by
    constructor
    · intro z hz
      rcases ZFSet.mem_union.1 hz with old | identity
      · obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ff.1 old)
        exact ZFSet.mem_prod.2 ⟨x, subS hx, y, subT hy, eq⟩
      · obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph D z).1 identity
        exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.mem_sep.1 hx).1, (ZFSet.mem_sep.1 hx).1⟩
    · intro x hx
      by_cases source : x ∈ s.carrier
      · obtain ⟨y, entry, unique⟩ := ff.2 x source
        refine ⟨y, ZFSet.mem_union.2 (Or.inl entry), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact unique z old
        · exact False.elim ((ZFSet.mem_sep.1
            ((pair_mem_identityFunctionGraph D x z).1 identity).2).2 source)
      · refine ⟨x, ZFSet.mem_union.2 (Or.inr
          ((pair_mem_identityFunctionGraph D x x).2 ⟨rfl, ZFSet.mem_sep.2 ⟨hx, source⟩⟩)), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact False.elim (source (ZFSet.pair_mem_prod.1 (ff.1 old)).1)
        · exact ((pair_mem_identityFunctionGraph D x z).1 identity).1.symm
  let u := SetMembers.presentation U
  let es := s.intoSet U subS
  let et := t.intoSet U subT
  let h := u.decodeFunction u G full
  have commute (p : P) : h (es p) = et (f p) := by
    apply (u.decodeFunction_iff u G full (es p) (et (f p))).2
    rw [s.encode_intoSet U subS, t.encode_intoSet U subT]
    exact ZFSet.mem_union.2 (Or.inl ((s.pair_mem_graph t f p (f p)).2 rfl))
  have sourceCode := Name.rename_val_of_encode u es (s.encode_intoSet U subS) τ
  have ground := M.rename_mem u pairing unions powers separation collection hU h
    ((u.graph_decodeFunction u G full).symm ▸ hG)
    (Name.rename u es τ) (sourceCode ▸ hτ)
  have equation : Name.rename u h (Name.rename u es τ) =
      Name.rename u et (Name.rename t f τ) := by
    rw [Name.rename_comp, Name.rename_comp]
    apply congrArg (fun k => Name.rename u k τ)
    funext p
    exact commute p
  rw [equation, Name.rename_val_of_encode u et (t.encode_intoSet U subT)] at ground
  exact ground

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Lower Upper : Type u}
variable [PartialOrder Lower] [PartialOrder Upper]
variable (lower : Presentation Lower) (upper : Presentation Upper)
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
variable (inclusionGround : lower.graph upper inclusion ∈ M.sets)
variable (H : ConditionFilter Upper)
variable (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper)))
include pairing unions powers separation collection lowerGround upperGround inclusionGround ordinary

theorem completeProjection_eval_eq_iff_forcesEq (sigma tau : Name lower)
    (sigmaGround : sigma.val ∈ M.sets) (tauGround : tau.val ∈ M.sets) :
    Name.eval {q | (projection.projectedFilter H).mem q} sigma =
      Name.eval {q | (projection.projectedFilter H).mem q} tau ↔
    ∃ q, (projection.projectedFilter H).mem q ∧ Name.ForcesEq q sigma tau := by
  have liftedSigma := M.rename_between_mem lower upper pairing unions powers separation collection
    lowerGround upperGround inclusion inclusionGround sigma sigmaGround
  have liftedTau := M.rename_between_mem lower upper pairing unions powers separation collection
    lowerGround upperGround inclusion inclusionGround tau tauGround
  have truth := Name.eval_eq_iff_forcesEq (M.nameDomain upper) H
    (fun E member => ordinary E (Or.inl member)) liftedSigma liftedTau
  simp only [Name.eval_rename] at truth
  constructor
  · intro equal
    obtain ⟨p, member, forced⟩ := truth.1 equal
    exact ⟨restriction p, (projection.projectedFilter_mem_iff H _).2 ⟨p, member, rfl⟩,
      (Name.forcesEq_rename_completeProjection lower upper restriction inclusion projection p sigma tau).1 forced⟩
  · rintro ⟨q, member, forced⟩
    apply truth.2
    refine ⟨inclusion q, member, ?_⟩
    apply (Name.forcesEq_rename_completeProjection lower upper restriction inclusion projection
      (inclusion q) sigma tau).2
    simpa only [projection.retract] using forced

end PartitionPilot.Forcing.TransitiveGround

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalRowOrdinaryZF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

include fulfilled

theorem decoded_strict_growth :
    let geometry := run.finalGeometry i₀
    letI := geometry.meet.order.toPartialOrder
    ∀ x : SetMembers geometry.carrier, ∃ y : SetMembers geometry.carrier, x < y := by
  let geometry := run.finalGeometry i₀
  let := geometry.meet.order.toPartialOrder
  dsimp only
  intro x
  obtain ⟨y, hy, lower, strict⟩ := fulfilled.growth _ (SetMembers.raw_mem x)
  refine ⟨SetMembers.ofMem y hy, lt_iff_le_not_ge.2 ⟨?_, ?_⟩⟩
  · change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem y hy))
      ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using lower
  · change ¬ ZFSet.pair (SetMembers.raw (SetMembers.ofMem y hy)) (SetMembers.raw x)
      ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using strict

end GroundMainPrefix.FinalFulfillment

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRowCompleteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "sU" => SetMembers.presentation U
local notation "sL" => SetMembers.presentation L

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)

variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
    ∀ A lower stronger, stageOneRawTests M d A lower →
      ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "inc" => run.inclusionFunction ordinal cutOrdinal subset pairing unions powers separation infinite choice
  hStages hHistory hT hAlpha hRows top topMem topRows mono

theorem inclusionFunction_graph : (sL).graph sU inc = identityFunctionGraph L := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph, mem_identityFunctionGraph]
  have code := run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
    hStages hHistory hT hAlpha hRows top topMem topRows mono
  constructor
  · rintro ⟨x, rfl⟩
    change ∃ y ∈ L, ZFSet.pair (SetMembers.raw x) (SetMembers.raw (inc x)) = ZFSet.pair y y
    rw [code x]
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, rfl⟩
  · rintro ⟨x, member, rfl⟩
    let q := SetMembers.ofMem x member
    refine ⟨q, ?_⟩
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw (inc q)) = ZFSet.pair x x
    rw [code q, SetMembers.raw_ofMem]

include pairing unions powers separation hStages hHistory hT hAlpha hRows in
theorem inclusionFunction_graph_mem (omega : ZFSet.omega ∈ M.sets) :
    (sL).graph sU inc ∈ M.sets := by
  rw [run.inclusionFunction_graph]
  exact M.identityFunctionGraph_mem pairing unions powers separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hHistory) omega)

end RecursiveRefinementOrderHistory

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAssignmentLabelDomainTotality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}
variable [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q]
variable (lower : Presentation P) (upper : Presentation Q)
variable {restriction : Q →o P} {inclusion : P ↪o Q}
variable (projection : CompleteProjection restriction inclusion)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
variable (lowerOrder : lower.conditionOrder ∈ M.sets)
variable (inclusionGround : lower.graph upper inclusion ∈ M.sets)
variable {levels alpha T : ZFSet.{u}}
variable (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName lower z) (idx : ZFSet.{u}) (hIdx : idx ∈ M.sets)
variable (U Rc : (M.nameDomain lower).names) (Rf : Name lower)
variable (cutCoordinates : ∀ p : Q, ∃ row A : ZFSet.{u}, upper.encode p = ZFSet.pair row A ∧
  lower.encode (restriction p) = ZFSet.pair row (assignmentCut levels alpha A))
variable (H : ConditionFilter Q) (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper)))
include pairing unions powers separation collection lowerGround upperGround lowerOrder inclusionGround
  hLevels hAlpha hT hIdx cutCoordinates ordinary

local notation "lowerH" => projection.projectedFilter H
local notation "label" => Name.refinementAssignmentLabel upper inclusion ⊤ T valid idx Rf Rc.val
local notation "domainSet" => (M.representedDomainConditions lower upper.carrier levels alpha T valid idx U Rc)

theorem refinementAssignmentLabel_represents_active_term
    (u : (M.nameDomain lower).names) (_hu : u.val.val ∈ T)
    (ground : domainSet u ∈ M.sets)
    (dense : Dense {p : Q | upper.encode p ∈ domainSet u})
    (active : ∃ q : P, (lowerH).mem q ∧ Name.ForcesMem q u.val U.val) :
    ∃ a : ZFSet.{u}, ZFSet.pair
      (Name.eval {q | (lowerH).mem q} (Name.refinementClass T valid Rc.val u.val)) a ∈
      Name.eval {p | H.mem p} label := by
  obtain ⟨p, hp, inD⟩ := M.ordinary_generic_meets_ground_dense upper pairing unions powers separation
    H ordinary ground (M.representedDomainConditions_subset lower _ _ _ _ valid idx U Rc u) dense
  obtain ⟨row, A, pCode, cutCode⟩ := cutCoordinates p
  have cutMember : (lowerH).mem (restriction p) :=
    (projection.projectedFilter_mem_iff H _).2 ⟨p, hp, rfl⟩
  have branches := (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerGround lowerOrder upperGround hLevels hAlpha hT valid hIdx U Rc u row A
    (restriction p) cutCode).1 (pCode ▸ inD)
  rcases branches.2 with inactive | ⟨_active, v, w, hv, hw, literal, forcedEqual⟩
  · obtain ⟨q, hq, activeQ⟩ := active
    obtain ⟨r, _hr, rp, rq⟩ := (lowerH).directed cutMember hq
    exact False.elim (inactive r rp (Name.forcesMem_mono activeQ rq))
  · have classU := M.refinementClass_mem lower pairing unions powers separation collection
      lowerGround lowerOrder hT valid Rc.val u.val Rc.property u.property
    have classV := M.refinementClass_mem lower pairing unions powers separation collection
      lowerGround lowerOrder hT valid Rc.val v Rc.property (M.transitive hT hv)
    have equal := (M.completeProjection_eval_eq_iff_forcesEq lower upper projection
      pairing unions powers separation collection lowerGround upperGround inclusionGround H ordinary
      (Name.refinementClass T valid Rc.val u.val) (Name.refinementClass T valid Rc.val v)
      classU classV).2 ⟨restriction p, cutMember, forcedEqual⟩
    let a := Name.eval {q | (lowerH).mem q} (Name.refinementClass T valid Rf w)
    refine ⟨a, (Name.mem_eval_refinementAssignmentLabel upper inclusion ⊤ T valid idx Rf Rc.val
      {p | H.mem p} H.top_mem _).2 ?_⟩
    exact ⟨p, v, w, hp, hv, hw, ⟨row, A, pCode, literal⟩,
      congrArg (fun x => ZFSet.pair x a) equal.symm⟩

theorem refinementAssignmentLabel_domain_total
    (density : ∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
      domainSet u ∈ M.sets ∧ Dense {p : Q | upper.encode p ∈ domainSet u}) :
    ∀ b ∈ Name.eval {q | (lowerH).mem q} (Name.refinementQuotient T valid U.val Rc.val),
      ∃ a : ZFSet.{u}, ZFSet.pair b a ∈ Name.eval {p | H.mem p} label := by
  intro b member
  obtain ⟨sigma, q, entry, hq, equal⟩ := (Name.mem_eval {q | (lowerH).mem q}
    (Name.refinementQuotient T valid U.val Rc.val) b).1 member
  obtain ⟨u, hu, active, rfl⟩ := (Name.entry_refinementQuotient T valid U.val Rc.val sigma q).1 entry
  let term : (M.nameDomain lower).names := ⟨u, M.transitive hT hu⟩
  have result := M.refinementAssignmentLabel_represents_active_term lower upper projection
    pairing unions powers separation collection lowerGround upperGround lowerOrder inclusionGround
    hLevels hAlpha hT valid idx hIdx U Rc Rf cutCoordinates H ordinary term hu
    (density term hu).1 (density term hu).2 ⟨q, hq, active⟩
  exact equal ▸ result

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAssignmentLabelDomainTotality
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

theorem semanticStructuralPrefix_stageSystem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    RefinementStageSystem M act lower t b d base directed alpha T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1
    closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  exact M.recursiveRefinementStageSystem c a t b d base directed T T2 alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal pairing unions powers separation collection
    carrier rowOrderGround group nodes nodeOrder nodeMaps supports hT hT2 hAlpha hLowerPacked
    omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 rowTop topMem topRows
    act image coordinates emptyImage hGraph

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace member
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "inc" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal cutOrdinal subset
  pairing unions powers separation infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono

theorem semanticStructuralAssignmentLabel_domain_total :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let upper := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      ∀ (H : ConditionFilter (SetMembers Q)), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      (∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
        M.representedDomainConditions lower upper.carrier levels alpha T valid idx U Rc u ∈ M.sets ∧
        Dense {p : SetMembers Q | upper.encode p ∈
          M.representedDomainConditions lower upper.carrier levels alpha T valid idx U Rc u}) →
      ∀ z ∈ Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rc.val),
        ∃ y : ZFSet.{u}, ZFSet.pair z y ∈ Name.eval {p | H.mem p}
          (Name.refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let upper := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let restriction := (run).restriction ordinal cutOrdinal subset c.conditionOrder_code
  let inclusion := (run).inclusion ordinal cutOrdinal subset pairing unions powers separation
    infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code
  have projection : CompleteProjection restriction inclusion :=
    M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have lowerGround : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hAlpha hLowerPacked omega
  have upperGround : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hs hPacked omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have inclusionGround : lower.graph upper inclusion ∈ M.sets :=
    (run).inclusionFunction_graph_mem ordinal cutOrdinal subset pairing unions powers separation
      hs hPacked hT hAlpha carrier infinite choice rowTop topMem topRows mono omega
  have levelsGround := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  have cutCoordinates : ∀ p : SetMembers Q, ∃ row A : ZFSet.{u},
      upper.encode p = ZFSet.pair row A ∧
      lower.encode (restriction p) = ZFSet.pair row (assignmentCut levels alpha A) := by
    intro p
    obtain ⟨row, _rowMem, A, _dataMem, code⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem p))
    exact ⟨row, A, code, (run).restrictionFunction_raw ordinal cutOrdinal subset p row A code⟩
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  dsimp only
  intro C E U Rf Rc index H ordinary density
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have hIdx : idx ∈ M.sets := M.transitive system.indices.index_ground index
  exact M.refinementAssignmentLabel_domain_total lower upper projection
    pairing unions powers separation collection lowerGround upperGround lowerOrder inclusionGround
    levelsGround hAlpha hT valid idx hIdx U Rc Rf.val cutCoordinates H ordinary density

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

local notation "parentQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "parentLevels" => refinementDataHistoryLevels stages packed T
local notation "gamma" => insert alpha alpha
local notation "nextPacked" => graphRestriction gamma packed
local notation "nextQ" => M.refinementHistoryForcing c.carrier T gamma nextPacked
local notation "nextLevels" => refinementDataHistoryLevels gamma nextPacked T

omit rowAction nodeAction nodeMaps valid2 closed1 closed2 symmetric1 symmetric2 in
theorem semanticStructuralPrefix_representedDomain_of_successor_cut :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (idx : ZFSet.{u}), idx ∈ M.sets → ∀ (U Rc u : (M.nameDomain lower).names),
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ parentQ →
      ZFSet.pair row (assignmentCut parentLevels gamma A) ∈
        M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u →
      ZFSet.pair row A ∈
        M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro idx hIdx U Rc u row A condition represented
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have alphaGamma : alpha ⊆ gamma := fun _ hx => ZFSet.mem_insert_of_mem _ hx
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset _ old
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hNextPacked := M.graphRestriction_mem unions separation hGamma hPacked
  have lowerGround : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hAlpha hLowerPacked omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have hParent := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hs hPacked omega
  have hNext := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hGamma hNextPacked omega
  have hParentLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  have hNextLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hGamma hNextPacked hT
  let q : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair row (assignmentCut parentLevels alpha A)) ((run).carriers.cut_mem condition member)
  have cutCode : lower.encode q = ZFSet.pair row (assignmentCut parentLevels alpha A) :=
    SetMembers.raw_ofMem _ _
  have sharedCut : assignmentCut nextLevels alpha (assignmentCut parentLevels gamma A) =
      assignmentCut parentLevels alpha A := by
    rw [(run).carriers.data.prefix_cut gammaSubset alphaGamma, assignmentCut_nested alphaGamma]
  have nextCutCode : lower.encode q =
      ZFSet.pair row (assignmentCut nextLevels alpha (assignmentCut parentLevels gamma A)) := by
    rw [sharedCut]
    exact cutCode
  have branches := (M.pair_mem_representedDomainConditions lower
    pairing unions powers separation collection lowerGround lowerOrder hNext hNextLevels hAlpha hT
    valid hIdx U Rc u row (assignmentCut parentLevels gamma A) q nextCutCode).1 represented
  apply (M.pair_mem_representedDomainConditions lower
    pairing unions powers separation collection lowerGround lowerOrder hParent hParentLevels hAlpha hT
    valid hIdx U Rc u row A q cutCode).2
  refine ⟨condition, ?_⟩
  rcases branches.2 with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
  · exact Or.inl inactive
  · exact Or.inr ⟨active, v, w, hv, hw,
      assignmentCut_subset parentLevels gamma A literal, equal⟩

variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)

include infinite choice in
theorem semanticStructuralPrefix_representedDomain_persistent_dense :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma nextPacked
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      (∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
        M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u ∈ M.sets ∧
        Dense {p : SetMembers nextQ | SetMembers.raw p ∈
          M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u}) →
      ∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
        M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u ∈ M.sets ∧
        Dense {p : SetMembers parentQ | SetMembers.raw p ∈
          M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u} := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma nextPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have gammaOrdinal : ordinalSetProperty gamma := ordinalSetProperty_succ cutOrdinal
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset _ old
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  let restriction := (run).restriction ordinal gammaOrdinal gammaSubset c.conditionOrder_code
  let inclusion := (run).inclusion ordinal gammaOrdinal gammaSubset pairing unions powers separation
    infinite choice hs hPacked hT hGamma carrier rowTop topMem topRows mono c.conditionOrder_code
  have projection : CompleteProjection restriction inclusion :=
    M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace gamma hGamma gammaOrdinal gammaSubset infinite choice
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  dsimp only
  intro C E U Rf Rc index successorDensity u hu
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have hIdx : idx ∈ M.sets := M.transitive system.indices.index_ground index
  have groundDownward := M.semanticStructuralPrefix_representedDomain_ground_downward
    c a t b d base directed T T2 rowTop pairing unions powers separation collection
    carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
    idx hIdx U Rc u
  refine ⟨groundDownward.1, ?_⟩
  intro p
  obtain ⟨q, qp, represented⟩ := projection.dense_preimage (successorDensity u hu).2 p
  obtain ⟨row, _rowMem, A, _dataMem, qCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem q))
  have parentMember : ZFSet.pair row A ∈ parentQ := qCode ▸ SetMembers.raw_mem q
  have nextCode : SetMembers.raw (restriction q) =
      ZFSet.pair row (assignmentCut parentLevels gamma A) :=
    (run).restrictionFunction_raw ordinal gammaOrdinal gammaSubset q row A qCode
  have representedCut : ZFSet.pair row (assignmentCut parentLevels gamma A) ∈
      M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u := by
    change SetMembers.raw (restriction q) ∈
      M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u at represented
    exact nextCode ▸ represented
  refine ⟨q, qp, ?_⟩
  change SetMembers.raw q ∈
    M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u
  rw [qCode]
  exact M.semanticStructuralPrefix_representedDomain_of_successor_cut
    c a t b d T T2 rowTop pairing unions powers separation collection
    carrier rowOrderGround group nodes nodeOrder supports hT hT2 omega valid1
    topMem topRows hs hh ordinal trace member idx hIdx U Rc u row A parentMember representedCut

end PartitionPilot.Forcing.TransitiveGround

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






theorem structural_assignment_label_injection
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
      let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
        historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
      let upper := SetMembers.presentation upperSet
      let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
        ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
          lifted, squared, stages, history]
        (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
          (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
      let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace
      let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared stages history
        pairing unions powers separation collection hG hL supports hh hLifted witnesses
      let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal cutOrdinal subset
        pairing unions powers separation infinite choice hs hPacked hLifted hAlpha carrier (c.encode ⊤)
        topMem topRows mono
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid →
      ∀ (H : ConditionFilter (SetMembers upperSet)), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let label := Name.refinementAssignmentLabel upper inc ⊤ lifted localValid idx Rf.val Rc.val
      let J := Name.eval {p | H.mem p} label
      let coarse := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient lifted localValid U.val Rc.val)
      let fine := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient lifted localValid U.val Rf.val)
      let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace
      InjectionCode coarse fine J ∧
        J ∈ (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H).sets := by
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
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
  let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared stages history
    pairing unions powers separation collection hG hL supports hh hLifted witnesses
  let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal cutOrdinal subset
    pairing unions powers separation infinite choice hs hPacked hLifted hAlpha carrier (c.encode ⊤)
    topMem topRows mono
  intro V E U Rf Rc index H ordinary
  have density := M.semanticStructuralPrefix_representedDomain_persistent_dense c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder
    forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace member
    infinite choice V E U Rf Rc index (by
      intro u hu
      have successorDensity := fulfilled.structural_represented_domain_dense collection infinite choice labels
        small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared
        valid1 valid2 closed1 closed2 children1 children2
        stages history hs hh stagesOrdinal trace alpha member V E U Rf Rc u index hu
      exact ⟨successorDensity.1, successorDensity.2.2.2⟩)
  have total := M.semanticStructuralAssignmentLabel_domain_total c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member infinite choice V E U Rf Rc index H ordinary density
  exact M.semanticStructuralAssignmentLabel_injection_package c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member infinite choice V E U Rf Rc index H ordinary total

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundMainFinalPartitionModel
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






theorem structural_refinement_quotient_injection_oai
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
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history)
    (_standard : GroundStandardInaccessible M stages)
    (_smallRows : GroundBelow M c.carrier stages) (_smallLifted : GroundBelow M lifted stages),
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
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers stagesOrdinal carrier lifted valid1
  ∀ (H : ConditionFilter (SetMembers upperSet)),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    (∀ (beta : ZFSet.{u}) (member : beta ∈ stages),
      let hBeta := M.transitive hs member
      let betaOrdinal := ordinalSetProperty_member stagesOrdinal member
      let betaSubset := (And.left stagesOrdinal) beta member
      let lowerPacked := graphRestriction beta packed
      let lowerSet := M.refinementHistoryForcing c.carrier lifted beta lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted beta lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted beta lowerPacked
        (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation lowerSet
      let projection := M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace beta hBeta betaOrdinal betaSubset infinite choice
      (projection.projectedFilter H).GenericFor (M.codedFamily lower) ∧
      (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower))) →
    ∀ tau : Fin 3 → (M.nameDomain upper).names,
      (∀ i, HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) (tau i).val) →
      RefinementValidityCode
        (Name.eval {p | H.mem p} (Name.familySet ⊤ lifted validUpper))
        (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
        (Name.eval {p | H.mem p} (tau 2).val) →
      ∃ J ∈ (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H).sets,
        InjectionCode
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 2).val))
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 1).val)) J := by
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
    stages history hs hh stagesOrdinal trace standard smallRows smallLifted
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
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers stagesOrdinal carrier lifted valid1
  intro H ordinary lowerGeneric tau symmetric originalValid
  have indexed := M.semanticStructuralTrace_refinementOutputs c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh standard trace infinite choice smallRows smallLifted small rfl
    fulfilled.toFinalFulfillment.decoded_strict_growth tau symmetric
  obtain ⟨beta, member, data⟩ := indexed
  let hBeta := M.transitive hs member
  let betaOrdinal := ordinalSetProperty_member stagesOrdinal member
  let betaSubset := (And.left stagesOrdinal) beta member
  let lowerPacked := graphRestriction beta packed
  let lowerSet := M.refinementHistoryForcing c.carrier lifted beta lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted beta lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted beta lowerPacked
    (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation lowerSet
  let localValid := M.refinementHistoryRowNameFamily_valid c
    (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier lifted valid1
  let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared stages history
    pairing unions powers separation collection hG hL supports hh hLifted witnesses
  let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal betaOrdinal betaSubset
    pairing unions powers separation infinite choice hs hPacked hLifted hBeta carrier (c.encode ⊤) topMem topRows mono
  dsimp only at data
  obtain ⟨_env, _names, _last, normalized, _entries, _normalizedLast, _forced, _supported,
    V, E, _baseV, _strict, _fixes, index, _stored, _attained, _fineGround, _coarseGround, _mapGround, values⟩ := data
  have outputValues := values H ordinary (lowerGeneric beta member).1 (lowerGeneric beta member).2 originalValid
  obtain ⟨_same, _objects, fineValues, coarseValues, _naturalMap⟩ := outputValues
  have injection := fulfilled.structural_assignment_label_injection collection infinite choice labels small smallD
    irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace beta member V E (normalized 0) (normalized 1) (normalized 2)
    index H ordinary
  have fineEq : Name.eval {q | H.mem (inc q)}
      (Name.refinementQuotient lifted localValid (normalized 0).val (normalized 1).val) =
      equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val) :=
    fineValues
  have coarseEq : Name.eval {q | H.mem (inc q)}
      (Name.refinementQuotient lifted localValid (normalized 0).val (normalized 2).val) =
      equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 2).val) :=
    coarseValues
  refine ⟨_, injection.2, ?_⟩
  rw [← coarseEq, ← fineEq]
  exact injection.1






end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection_oai.{u, v}
