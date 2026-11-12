-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_pair_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:06.740175+00:00
-- url     : https://prove2.me/submissions/d0c8cb02-12c5-49b3-b91b-2be302bfe340

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_assignment_tests

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u
namespace BoundedFormula

theorem truth_refinementCollisionFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementCollisionFormula env ↔ (env 0 = env 1 ↔ env 2 = env 3) := by
  simp only [refinementCollisionFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

end BoundedFormula
namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_refinementCollisionFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementCollisionFormula env ↔ (env 0 = env 1 ↔ env 2 = env 3) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementCollisionFormula env)

end TransitiveGround
end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem refinementCollision_eval (env : Assignment (M.nameDomain s) 4)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) refinementCollisionFormula env p) :
    (Name.eval {q | H.mem q} (env 0).val = Name.eval {q | H.mem q} (env 1).val ↔
      Name.eval {q | H.mem q} (env 2).val = Name.eval {q | H.mem q} (env 3).val) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  exact (evaluated.realize_refinementCollisionFormula (evalAssignment {q | H.mem q} env)
    (fun j => ⟨env j, rfl⟩)).1
      (forces_sound (M.nameDomain s) H generic _ env hp forced)

end TransitiveGround

open SetRealization SetFormula
universe u

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

theorem restrictionFunction_graph :
    (sU).graph sL (run.restrictionFunction ordinal cutOrdinal subset) =
      rowAssignmentCutGraph U L (refinementDataHistoryLevels stages history T) alpha :=
  (sU).graph_decodeFunction sL _ (run.restrictionGraph_function ordinal cutOrdinal subset)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)

include pairing unions powers separation hStages hHistory hT hAlpha hRows in
theorem restrictionFunction_graph_mem (omega : ZFSet.omega ∈ M.sets) :
    (sU).graph sL (run.restrictionFunction ordinal cutOrdinal subset) ∈ M.sets := by
  rw [run.restrictionFunction_graph]
  exact M.rowAssignmentCutGraph_mem pairing unions powers separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega)
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hHistory) omega)
    (M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT) hAlpha

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompleteProjectionRefinementTests
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
include pairing unions powers separation collection lowerGround upperGround inclusionGround

theorem completeProjection_refinementCollision_eval
    (H : ConditionFilter Upper) (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (env : Assignment (M.nameDomain lower) 4) {q : Lower}
    (member : (projection.projectedFilter H).mem q)
    (test : Forces (M.nameDomain lower) refinementCollisionFormula env q) :
    (Name.eval {r | (projection.projectedFilter H).mem r} (env 0).val =
      Name.eval {r | (projection.projectedFilter H).mem r} (env 1).val ↔
    Name.eval {r | (projection.projectedFilter H).mem r} (env 2).val =
      Name.eval {r | (projection.projectedFilter H).mem r} (env 3).val) := by
  let lifted : Assignment (M.nameDomain upper) 4 := fun i =>
    ⟨Name.rename upper inclusion (env i).val,
      M.rename_between_mem lower upper pairing unions powers separation collection
        lowerGround upperGround inclusion inclusionGround (env i).val (env i).property⟩
  have atomic (p : Upper) (i j : Fin 4) :
      Name.ForcesEq p (lifted i).val (lifted j).val ↔
        Name.ForcesEq (restriction p) (env i).val (env j).val :=
    Name.forcesEq_rename_completeProjection lower upper restriction inclusion projection p _ _
  have transfer (i j k l : Fin 4)
      (clause : ∀ r, r ≤ q → ¬ (Name.ForcesEq r (env i).val (env j).val ∧
        ∀ p, p ≤ r → ¬ Name.ForcesEq p (env k).val (env l).val)) :
      ∀ r, r ≤ inclusion q → ¬ (Name.ForcesEq r (lifted i).val (lifted j).val ∧
        ∀ p, p ≤ r → ¬ Name.ForcesEq p (lifted k).val (lifted l).val) := by
    intro r rq facts
    apply clause (restriction r) ((projection.le_include_iff r q).1 rq)
    refine ⟨(atomic r i j).1 facts.1, ?_⟩
    intro p pr eq
    obtain ⟨v, vr, vp⟩ := projection.lift r p pr
    apply facts.2 v vr
    exact (atomic v k l).2 (vp.symm ▸ eq)
  have upperTest : Forces (M.nameDomain upper) refinementCollisionFormula lifted (inclusion q) :=
    ⟨transfer 0 1 2 3 test.1, transfer 2 3 0 1 test.2⟩
  have evaluated := M.refinementCollision_eval upper lifted H ordinary member upperTest
  simpa only [lifted, Name.eval_rename, CompleteProjection.projectedFilter,
    Set.mem_ofPred_eq] using evaluated

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAssignmentLabelInjectionPackages
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
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "pi" => RecursiveRefinementOrderHistory.restrictionFunction run ordinal cutOrdinal subset
include hs hh ordinal trace hAlpha cutOrdinal subset
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

theorem semanticStructuralMapGraphs_mem :
    (SetMembers.presentation Q).graph (SetMembers.presentation LQ) pi ∈ M.sets ∧
      (SetMembers.presentation LQ).graph (SetMembers.presentation Q) inc ∈ M.sets := by
  constructor
  · exact (run).restrictionFunction_graph_mem ordinal cutOrdinal subset pairing unions powers separation
      hs hPacked hT hAlpha carrier omega
  · exact (run).inclusionFunction_graph_mem ordinal cutOrdinal subset pairing unions powers separation
      hs hPacked hT hAlpha carrier infinite choice rowTop topMem topRows mono omega

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

theorem semanticStructuralAssignmentLabel_pair_eq_iff_oai :
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
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let label := Name.refinementAssignmentLabel upper inc ⊤ T valid
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) Rf Rc
      ∀ x y x' y' : ZFSet.{u},
        ZFSet.pair x y ∈ Name.eval {p | H.mem p} label →
        ZFSet.pair x' y' ∈ Name.eval {p | H.mem p} label →
        (x = x' ↔ y = y') := by
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
  have lowerGround : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hAlpha
    (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have upperGround : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hs hPacked omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have inclusionGround := (M.semanticStructuralMapGraphs_mem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice).2
  let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  dsimp only
  intro C E U Rf Rc index H ordinary x y x' y' first second
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  obtain ⟨p, v, w, hp, hv, hw, ⟨row, A, code, entry⟩, equal⟩ :=
    (Name.mem_eval_refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val
      {p | H.mem p} H.top_mem (ZFSet.pair x y)).1 first
  obtain ⟨p', v', w', hp', hv', hw', ⟨row', A', code', entry'⟩, equal'⟩ :=
    (Name.mem_eval_refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val
      {p | H.mem p} H.top_mem (ZFSet.pair x' y')).1 second
  change SetMembers.raw p = ZFSet.pair row A at code
  change SetMembers.raw p' = ZFSet.pair row' A' at code'
  obtain ⟨q, hq, below, below'⟩ := H.directed hp hp'
  obtain ⟨qRow, _qRowMem, qA, _qAMem, qCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem q))
  have retains : A ⊆ qA := by
    have edge : ZFSet.pair (SetMembers.raw q) (SetMembers.raw p) ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := below
    rw [qCode, code] at edge
    exact ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
      qRow qA row A).1 edge).2.2.2
  have retains' : A' ⊆ qA := by
    have edge : ZFSet.pair (SetMembers.raw q) (SetMembers.raw p') ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := below'
    rw [qCode, code'] at edge
    exact ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
      qRow qA row' A').1 edge).2.2.2
  let gv : (M.nameDomain lower).names := ⟨v, M.transitive hT hv⟩
  let gv' : (M.nameDomain lower).names := ⟨v', M.transitive hT hv'⟩
  let gw : (M.nameDomain lower).names := ⟨w, M.transitive hT hw⟩
  let gw' : (M.nameDomain lower).names := ⟨w', M.transitive hT hw'⟩
  have tests := M.semanticStructuralPrefix_assignment_tests c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member q qRow qA qCode
  have collision := (tests C E U Rf Rc index).2 gv gv' gw gw' hv hv' hw hw'
    (retains entry) (retains' entry')
  let cls := M.stageOneClassName lower pairing unions powers separation collection
    lowerGround lowerOrder hT valid
  have projectedMember : (projection.projectedFilter H).mem
      ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code q) :=
    (projection.projectedFilter_mem_iff H _).2 ⟨q, hq, rfl⟩
  have compared := M.completeProjection_refinementCollision_eval lower upper projection
    pairing unions powers separation collection lowerGround upperGround inclusionGround H ordinary
    ![cls Rc gv, cls Rc gv', cls Rf gw, cls Rf gw'] projectedMember collision
  have values :
      (Name.eval {q | inc q ∈ {p | H.mem p}} (Name.refinementClass T valid Rc.val v) =
        Name.eval {q | inc q ∈ {p | H.mem p}} (Name.refinementClass T valid Rc.val v') ↔
      Name.eval {q | inc q ∈ {p | H.mem p}} (Name.refinementClass T valid Rf.val w) =
        Name.eval {q | inc q ∈ {p | H.mem p}} (Name.refinementClass T valid Rf.val w')) := compared
  obtain ⟨vx, wy⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨vx', wy'⟩ := ZFSet.pair_inj.1 equal'
  simpa only [vx, wy, vx', wy'] using values

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_pair_eq_iff_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_pair_eq_iff_oai.{u}
