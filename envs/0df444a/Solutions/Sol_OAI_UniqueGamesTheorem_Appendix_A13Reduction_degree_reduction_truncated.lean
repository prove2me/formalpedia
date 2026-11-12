-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:47.916544+00:00
-- url     : https://prove2.me/submissions/44472e22-e44e-42ec-9468-c09e4082aa16

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P011
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A13Reduction_weakFourthSum_le_positiveTripleSum
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_BadConvolution_badConvolution_sq_sum_le

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite Gram-energy estimates used in Lemma A.1. -/
namespace UniqueGamesTheorem.Appendix.F1Gram
open scoped BigOperators

/-- The squared entries of a Gram matrix are bounded by the squared total
energy of its underlying rows. This is a pairwise Cauchy–Schwarz argument. -/
theorem gram_energy_le {R C : Type*} [Fintype R] [Fintype C] (p : R → C → ℝ) :
    (∑ r, ∑ s, (∑ c, p r c * p s c)^2) ≤
      (∑ r, ∑ c, p r c^2)^2 := by
  classical
  let e : R → ℝ := fun r => ∑ c, p r c^2
  calc
    _ ≤ ∑ r, ∑ s, e r * e s := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (p r) (p s)
    _ = (∑ r, e r) * (∑ s, e s) := (Finset.sum_mul_sum _ _ _ _).symm
    _ = (∑ r, ∑ c, p r c^2)^2 := (pow_two _).symm

theorem sum_subtype_eq {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] (f : A → ℝ) :
    (∑ x : {x // P x}, f x) = ∑ x : A, if P x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, f x := by
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
      · intro x _ y _ h
        exact Subtype.ext h
      · intro y hy
        exact ⟨⟨y, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _
        rfl
    _ = _ := by rw [Finset.sum_filter]

theorem sum_comp_le {A B : Type*} [Fintype A] [Fintype B] (e : A → B)
    (he : Function.Injective e) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b :=
      (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ ∑ b ∈ Finset.univ, f b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun b _ _ => hf b)

end UniqueGamesTheorem.Appendix.F1Gram

end

section

namespace UniqueGamesTheorem.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem quotient_rank_selected (A : Submodule K V) (Y : W →ₗ[K] V)
    (hA : A ≤ range Y) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at h
  exact h

omit [FiniteDimensional K V] in
theorem domain_rank_selected (B : Submodule K W) (Y : W →ₗ[K] V)
    (hB : ker Y ≤ B) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp, (Submodule.comapSubtypeEquivOfLe hB).finrank_eq] at h₁
  omega

omit [FiniteDimensional K V] in
theorem hybrid_rank_loss (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) (hA : A ≤ range Y) (hB : A.comap Y ≤ B) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have hquot := quotient_rank_selected A Y hA
  have hdom := domain_rank_selected B (A.mkQ.comp Y) (by
    simpa only [ker_comp, Submodule.ker_mkQ] using hB)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hdom
  omega

end UniqueGamesTheorem.Appendix.Level.LinearRank

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_DegreeCover
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/
namespace UniqueGamesTheorem.Appendix.DegreeCover

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Glue a linear map on P to zero on Q when the restrictions agree. -/
theorem exists_glue_zero (P Q : Submodule F2 W) (f : W →ₗ[F2] V)
    (cover : P ⊔ Q = ⊤) (compatible : ∀ w ∈ P, w ∈ Q → f w = 0) :
    ∃ g : W →ₗ[F2] V,
      (∀ w ∈ P, g w = f w) ∧ (∀ w ∈ Q, g w = 0) := by
  let p : W →ₗ.[F2] V := ⟨P, f.comp P.subtype⟩
  let q : W →ₗ.[F2] V := ⟨Q, 0⟩
  have hc : ∀ (x : p.domain) (y : q.domain), (x : W) = y → p x = q y := by
    intro x y hxy
    exact compatible x x.property (hxy ▸ y.property)
  let t := p.sup q hc
  have ht : ∀ w : W, w ∈ t.domain := by
    intro w
    change w ∈ P ⊔ Q
    rw [cover]
    exact Submodule.mem_top
  let inc : W →ₗ[F2] t.domain := (LinearMap.id : W →ₗ[F2] W).codRestrict t.domain ht
  refine ⟨t.toFun.comp inc, ?_, ?_⟩
  · intro w hw
    exact ((p.left_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm
  · intro w hw
    exact ((p.right_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm

private theorem binary_cross {a b c d : V} (h : a + b = c + d) : c + a = d + b := by
  calc
    c + a = (c + a) + (b + b) := by simp
    _ = c + (a + b) + b := by abel
    _ = c + (c + d) + b := by rw [h]
    _ = (c + c) + (d + b) := by abel
    _ = d + b := by simp

theorem exists_cover_component (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R : W →ₗ[F2] V,
      (∀ w ∈ LinearMap.ker Z, R w = Y w) ∧
      (∀ w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z), R w = 0) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y := by
  have cov : LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) = ⊤ := by
    simpa only [sup_assoc, sup_comm, sup_left_comm] using cover
  have compatible : ∀ w ∈ LinearMap.ker Z,
      w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z) → Y w = 0 := by
    intro w hw hz
    change Z w = 0 at hw
    rcases Submodule.mem_sup.mp hz with ⟨a, ha, b, hb, hab⟩
    change Y a = 0 at ha
    change (Y + Z) b = 0 at hb
    have hYb : Y b = Z b := by
      have h := congrArg (fun v : V => v + Z b) hb
      simpa only [LinearMap.add_apply, add_assoc, binary_add_self, add_zero, zero_add] using h
    have hYw : Y w = Z b := by rw [← hab, map_add, ha, zero_add, hYb]
    have hmem : Y w ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z :=
      ⟨⟨⟨w, by simp only [LinearMap.add_apply, hw, add_zero]⟩, ⟨w, rfl⟩⟩,
        ⟨b, hYw.symm⟩⟩
    rw [triple] at hmem
    exact hmem
  obtain ⟨R, hRZ, hRYX⟩ := exists_glue_zero (LinearMap.ker Z)
    (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) Y cov compatible
  refine ⟨R, hRZ, hRYX, ?_⟩
  rintro v ⟨w, rfl⟩
  have hw : w ∈ LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) := by
    rw [cov]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, b, hb, hab⟩
  have heq : R w = Y a := by rw [← hab, map_add, hRZ a ha, hRYX b hb, add_zero]
  refine ⟨⟨a, ?_⟩, ⟨a, heq.symm⟩⟩
  change Z a = 0 at ha
  rw [LinearMap.add_apply, ha, add_zero, heq]

/-- A general, dimension-free decomposition with pairwise disjoint images.
These are exactly the linear-algebra data used to establish the cover in A.1. -/
theorem exists_disjoint_decomposition (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Disjoint (LinearMap.range R) (LinearMap.range S) ∧
      Disjoint (LinearMap.range R) (LinearMap.range C) ∧
      Disjoint (LinearMap.range S) (LinearMap.range C) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y ∧
      LinearMap.range S ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Z ∧
      LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
  obtain ⟨R, hRZ, hRYX, rangeR⟩ := exists_cover_component Y Z triple cover
  obtain ⟨S, hSY, hSZX, rangeS⟩ := exists_cover_component Z Y
    (by simpa only [add_comm Z Y, inf_assoc, inf_comm, inf_left_comm] using triple)
    (by simpa only [add_comm Z Y, sup_assoc, sup_comm, sup_left_comm] using cover)
  rw [add_comm Z Y] at hSZX rangeS
  have eqX : Set.EqOn (R + S) (Y + Z) (LinearMap.ker (Y + Z)) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    rw [LinearMap.add_apply, hRYX w (Submodule.mem_sup_right hw), hSZX w (Submodule.mem_sup_right hw)]
    simpa only [zero_add] using hw.symm
  have eqY : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Y) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Y w = 0 at hw
    simp only [LinearMap.add_apply, hRYX w (Submodule.mem_sup_left hw), hSY w hw, hw, zero_add]
  have eqZ : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Z) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Z w = 0 at hw
    simp only [LinearMap.add_apply, hRZ w hw, hSZX w (Submodule.mem_sup_left hw), hw, add_zero]
  have hRS : R + S = Y + Z := by
    ext w
    exact LinearMap.eqOn_sup (LinearMap.eqOn_sup eqX eqY) eqZ (cover ▸ Submodule.mem_top)
  let C := Y + R
  have hC : C = Z + S := by
    ext w
    exact binary_cross (congrArg (fun f : W →ₗ[F2] V => f w) hRS)
  have hY : Y = R + C := by
    ext w
    change Y w = R w + (Y w + R w)
    rw [add_left_comm, binary_add_self, add_zero]
  have hZ : Z = S + C := by
    rw [hC]
    ext w
    change Z w = S w + (Z w + S w)
    rw [add_left_comm, binary_add_self, add_zero]
  have rangeC : LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
    apply le_inf
    · exact (LinearMap.range_add_le Y R).trans (sup_le le_rfl (rangeR.trans inf_le_right))
    · rw [hC]
      exact (LinearMap.range_add_le Z S).trans (sup_le le_rfl (rangeS.trans inf_le_right))
  have kill : ∀ v, v ∈ LinearMap.range (Y + Z) → v ∈ LinearMap.range Y →
      v ∈ LinearMap.range Z → v = 0 := by
    intro v hx hy hz
    have h : v ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z := ⟨⟨hx, hy⟩, hz⟩
    rwa [triple] at h
  refine ⟨R, S, C, hRS.symm, hY, hZ, ?_, ?_, ?_, rangeR, rangeS, rangeC⟩
  · exact Submodule.disjoint_def.mpr (fun v hr hs => kill v (rangeR hr).1 (rangeR hr).2 (rangeS hs).2)
  · exact Submodule.disjoint_def.mpr (fun v hr hc => kill v (rangeR hr).1 (rangeR hr).2 (rangeC hc).2)
  · exact Submodule.disjoint_def.mpr (fun v hs hc => kill v (rangeS hs).1 (rangeC hc).1 (rangeS hs).2)

/-- Rank additivity needs image containment as well as disjointness. -/
theorem rank_add_of_disjoint [FiniteDimensional F2 V] (R S : W →ₗ[F2] V)
    (hd : Disjoint (LinearMap.range R) (LinearMap.range S))
    (hR : LinearMap.range R ≤ LinearMap.range (R + S))
    (hS : LinearMap.range S ≤ LinearMap.range (R + S)) :
    Module.finrank F2 (LinearMap.range (R + S)) =
      Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) := by
  have heq := le_antisymm (LinearMap.range_add_le R S) (sup_le hR hS)
  rw [heq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range R) (LinearMap.range S)
  have hb : LinearMap.range R ⊓ LinearMap.range S = ⊥ := hd.eq_bot
  rw [hb, finrank_bot, add_zero] at h
  exact h

/-- The cover F(X) \ F₂(X) ⊆ F₁(X), with all three rank-additive decompositions.
There is no bound on dimension, and both bad-event exclusions are discharged. -/
theorem outside_bad_rank_cover [FiniteDimensional F2 V] (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Module.finrank F2 (LinearMap.range (Y + Z)) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) ∧
      Module.finrank F2 (LinearMap.range Y) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range C) ∧
      Module.finrank F2 (LinearMap.range Z) =
        Module.finrank F2 (LinearMap.range S) + Module.finrank F2 (LinearMap.range C) := by
  obtain ⟨R, S, C, hX, hY, hZ, dRS, dRC, dSC, rR, rS, rC⟩ :=
    exists_disjoint_decomposition Y Z triple cover
  refine ⟨R, S, C, hX, hY, hZ, ?_, ?_, ?_⟩
  · rw [hX]
    exact rank_add_of_disjoint R S dRS
      (hX ▸ rR.trans inf_le_left) (hX ▸ rS.trans inf_le_left)
  · rw [hY]
    exact rank_add_of_disjoint R C dRC
      (hY ▸ rR.trans inf_le_right) (hY ▸ rC.trans inf_le_left)
  · rw [hZ]
    exact rank_add_of_disjoint S C dSC
      (hZ ▸ rS.trans inf_le_right) (hZ ▸ rC.trans inf_le_right)

end UniqueGamesTheorem.Appendix.DegreeCover

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_CompressionCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.CompressionCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

variable {U K C}

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K]

theorem natCard_linearMap [FiniteDimensional F2 C] : Nat.card (U →ₗ[F2] C) =
    2 ^ (finrank F2 U * finrank F2 C) := by
  let e : (Fin (finrank F2 U) → C) ≃ (U →ₗ[F2] C) :=
    ((Module.finBasis F2 U).constr F2).toEquiv
  calc
    Nat.card (U →ₗ[F2] C) = Nat.card C ^ finrank F2 U := by
      rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]
    _ = (2 ^ finrank F2 C) ^ finrank F2 U := by
      rw [Module.natCard_eq_pow_finrank (K := F2) (V := C)]
      simp [F2, Nat.card_eq_fintype_card]
    _ = 2 ^ (finrank F2 U * finrank F2 C) := by
      rw [← pow_mul, Nat.mul_comm]

theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

end UniqueGamesTheorem.Appendix.CompressionCount

end

section

namespace UniqueGamesTheorem.Appendix.CoordinateTransport

noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

theorem finrank_comp_equiv {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (q : F ≃ₗ[𝕜] G) (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (q.toLinearMap.comp Y).range = Module.finrank 𝕜 Y.range := by
  have h := finrank_range_transport (LinearEquiv.refl 𝕜 E) q Y
  exact h

end

end UniqueGamesTheorem.Appendix.CoordinateTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_AntecedentCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace UniqueGamesTheorem.Appendix.FullCompression

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.CoordinateTransport
open Module

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
/-- Every member of a compression fiber has rank `rank X + rank Z`. -/
theorem fiber_rank (X : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range)) (Y : Fiber X Z) :
    finrank F2 Y.val.range = finrank F2 X.range + finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  have h := CompressionCount.fiber_rank
    ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z)
    ((fiberEquiv X Z P hP C hC) Y)
  change finrank F2 (toBlocks X P hP C hC Y.val).range =
    finrank F2 X.range +
      finrank F2 ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z).range at h
  rw [finrank_toBlocks, finrank_comp_equiv] at h
  exact h

end

end UniqueGamesTheorem.Appendix.FullCompression

end

section

namespace UniqueGamesTheorem.Appendix.TotalPredecessorCount
open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_recovery (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) (x : E) :
    ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) = R.val x := by
  have hq : Y.quotKerEquivRange.symm (Y.rangeRestrict x) = Y.ker.mkQ x :=
    Y.quotKerEquivRange.symm_apply_apply (Y.ker.mkQ x)
  dsimp only [predecessorEnd,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [hq]
  rfl

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_injective (Y : E →ₗ[F2] F) :
    Function.Injective (predecessorEnd Y) := by
  intro R S h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  calc
    R.val x = ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) :=
      (predecessorEnd_recovery Y R x).symm
    _ = ((predecessorEnd Y S (Y.rangeRestrict x) : Y.range) : F) :=
      congrArg (fun P : Y.range →ₗ[F2] Y.range => (P (Y.rangeRestrict x) : F)) h
    _ = S.val x := predecessorEnd_recovery Y S x

omit [FiniteDimensional F2 F] in
theorem card_predecessors_le [Finite E] [Finite F] (Y : E →ₗ[F2] F) :
    Nat.card {R : E →ₗ[F2] F // RankBelow R Y} ≤
      2 ^ (finrank F2 Y.range ^ 2) := by
  classical
  let : Finite (Y.range →ₗ[F2] Y.range) :=
    Finite.of_injective (fun f : Y.range →ₗ[F2] Y.range => (f : Y.range → Y.range))
      DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective (predecessorEnd Y)
    (predecessorEnd_injective Y)
  rw [CompressionCount.natCard_linearMap] at h
  simpa only [pow_two] using h
end UniqueGamesTheorem.Appendix.TotalPredecessorCount

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.evaluationCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixCharacters

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear

theorem tracePair_ext_right {n m : Nat} {S T : Matrix (Fin m) (Fin n) F2}
    (h : ∀ X, tracePair X S = tracePair X T) : S = T :=
  Matrix.ext_iff_trace_mul_left.mpr h

theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl
  · rfl
  · have hf : (1 : ℂ) = -1 := by simpa using h
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · have hf : (1 : ℂ) = -1 := by simpa using h.symm
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · rfl

theorem binarySign_real (a : F2) : ((binarySign a).re : ℂ) = binarySign a := by
  unfold binarySign
  split <;> simp

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_eq_matrix_tracePair {n m : Nat}
    (bE : Module.Basis (Fin m) F2 E) (bF : Module.Basis (Fin n) F2 F)
    (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S =
      tracePair (LinearMap.toMatrix bE bF X) (LinearMap.toMatrix bF bE S) := by
  change LinearMap.trace F2 F (X.comp S) =
    Matrix.trace (LinearMap.toMatrix bE bF X * LinearMap.toMatrix bF bE S)
  rw [LinearMap.trace_eq_matrix_trace F2 bF, LinearMap.toMatrix_comp bF bE bF]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_real (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    ((linearTraceCharacter S X).re : ℂ) = linearTraceCharacter S X := binarySign_real _

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem linearTracePair_swap (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S = linearTracePair S X :=
  LinearMap.trace_comp_comm' S X

theorem linearTraceCharacter_swap (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = linearTraceCharacter X S := by
  simp only [linearTraceCharacter_apply, linearTracePair_swap X S]

/-- The actual trace pairing is nondegenerate in its dual-map argument. -/
theorem linearTracePair_ext_right {S T : F →ₗ[F2] E}
    (h : ∀ X, linearTracePair X S = linearTracePair X T) : S = T := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  apply (LinearMap.toMatrix bF bE).injective
  apply tracePair_ext_right
  intro X
  obtain ⟨X', rfl⟩ := (LinearMap.toMatrix bE bF).surjective X
  exact (linearTracePair_eq_matrix_tracePair bE bF X' S).symm.trans
    ((h X').trans (linearTracePair_eq_matrix_tracePair bE bF X' T))

theorem linearTraceCharacter_injective :
    Function.Injective (linearTraceCharacter (E := E) (F := F)) := by
  intro S T h
  apply linearTracePair_ext_right
  intro X
  apply binarySign_injective
  exact congrArg (fun ψ : AddChar (E →ₗ[F2] F) ℂ => ψ X) h

theorem linearTraceCharacter_eq_zero_iff (S : F →ₗ[F2] E) :
    linearTraceCharacter S = 0 ↔ S = 0 := by
  rw [← linearTraceCharacter_zero, linearTraceCharacter_injective.eq_iff]

theorem sum_linearTraceCharacter [Fintype (E →ₗ[F2] F)] (S : F →ₗ[F2] E) :
    ∑ X, linearTraceCharacter S X =
      if S = 0 then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  simp only [linearTraceCharacter_eq_zero_iff]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixCharacters

end

end

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open UniqueGamesTheorem.Fourier.MatrixCharacters

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [AddCommGroup G] in
theorem star_expect (f : G → ℂ) :
    star (𝔼 x, f x) = 𝔼 x, star (f x) := by
  simp [Fintype.expect_eq_sum_div_card]

theorem star_fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) :
    star (fourierCoeff f ψ) = 𝔼 x, star (f x) * ψ x := by
  rw [fourierCoeff, star_expect]
  simp [star_mul, mul_comm]

end FiniteGroup

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem card_linearMap_reverse :
    Fintype.card (F →ₗ[F2] E) = Fintype.card (E →ₗ[F2] F) := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  calc
    Fintype.card (F →ₗ[F2] E) =
        Fintype.card (Matrix (Fin (Module.finrank F2 E))
          (Fin (Module.finrank F2 F)) F2) :=
      Fintype.card_congr (LinearMap.toMatrix bF bE).toEquiv
    _ = Fintype.card (Matrix (Fin (Module.finrank F2 F))
          (Fin (Module.finrank F2 E)) F2) := by
      exact Fintype.card_congr
        { toFun := Matrix.transpose
          invFun := Matrix.transpose
          left_inv := Matrix.transpose_transpose
          right_inv := Matrix.transpose_transpose }
    _ = Fintype.card (E →ₗ[F2] F) :=
      (Fintype.card_congr (LinearMap.toMatrix bE bF).toEquiv).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearTraceCharacter_star (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    star (linearTraceCharacter S X) = linearTraceCharacter S X := by
  calc
    _ = star (((linearTraceCharacter S X).re : ℝ) : ℂ) :=
      congrArg star (linearTraceCharacter_real S X).symm
    _ = ((linearTraceCharacter S X).re : ℂ) := by simp
    _ = linearTraceCharacter S X := linearTraceCharacter_real S X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearMap_add_eq_zero_iff (X Y : E →ₗ[F2] F) :
    X + Y = 0 ↔ X = Y := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hself : Y + Y = 0 := by
    have h := congrArg (fun c : F2 => c • Y) htwo
    simpa only [add_smul, one_smul, zero_smul] using h
  have hneg : -Y = Y := neg_eq_iff_add_eq_zero.mpr hself
  rw [add_eq_zero_iff_eq_neg, hneg]

/-- Exact trace-character orthogonality with the frequency sum unnormalized. -/
theorem linear_character_kernel (X Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, star (linearTraceCharacter S X) * linearTraceCharacter S Y =
      if X = Y then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  calc
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter S (X + Y) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [linearTraceCharacter_star, AddChar.map_add_eq_mul]
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter (X + Y) S := by
      apply Finset.sum_congr rfl
      intro S _
      exact linearTraceCharacter_swap S (X + Y)
    _ = if X + Y = 0 then (Fintype.card (F →ₗ[F2] E) : ℂ) else 0 :=
      sum_linearTraceCharacter (X + Y)
    _ = _ := by rw [linearMap_add_eq_zero_iff, card_linearMap_reverse]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

/-- Fourier inversion obtained directly from the finite trace orthogonality sum. -/
theorem linear_complex_inversion (f : (E →ₗ[F2] F) → ℂ) (Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, fourierCoeff f (linearTraceCharacter S) *
      linearTraceCharacter S Y = f Y := by
  classical
  simp only [fourierCoeff]
  simp_rw [Finset.expect_mul, mul_assoc]
  rw [← Finset.expect_sum_comm]
  simp_rw [← Finset.mul_sum, linear_character_kernel]
  rw [Finset.expect_eq_sum_div_card]
  simp [mul_ite]

/-- Mixed Parseval with normalized primal expectation and unnormalized frequency sum. -/
theorem linear_complex_parseval (f g : (E →ₗ[F2] F) → ℂ) :
    ∑ S : F →ₗ[F2] E, star (fourierCoeff f (linearTraceCharacter S)) *
      fourierCoeff g (linearTraceCharacter S) = 𝔼 X, star (f X) * g X := by
  simp_rw [star_fourierCoeff, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro X _
  calc
    (∑ S : F →ₗ[F2] E, (star (f X) * linearTraceCharacter S X) *
        fourierCoeff g (linearTraceCharacter S)) =
        star (f X) * ∑ S : F →ₗ[F2] E,
          fourierCoeff g (linearTraceCharacter S) * linearTraceCharacter S X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = star (f X) * g X := by rw [linear_complex_inversion]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_complex (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    (linearCoeff f S : ℂ) =
      fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S) := by
  rw [linearCoeff, complex_ofReal_expect, fourierCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [Complex.ofReal_mul, linearTraceCharacter_real, linearTraceCharacter_star]

/-- Parseval for real functions and the real binary trace coefficients. -/
theorem linear_parseval_inner (f g : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S =
      𝔼 X, f X * g X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          star (fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S)) *
            fourierCoeff (fun X => (g X : ℂ)) (linearTraceCharacter S) := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [← linearCoeff_complex, ← linearCoeff_complex]
      simp
    _ = 𝔼 X, star (f X : ℂ) * (g X : ℂ) := linear_complex_parseval _ _
    _ = ((𝔼 X, f X * g X : ℝ) : ℂ) := by
      rw [complex_ofReal_expect]
      simp

theorem linear_parseval (f : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S ^ 2 = 𝔼 X, f X ^ 2 := by
  simpa only [pow_two] using linear_parseval_inner f f

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

section

/-! The degree-zero base case in the actual finite binary Fourier model. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.DegreeZero
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem rank_pos_of_ne_zero (Y : F →ₗ[F2] E) (hY : Y ≠ 0) :
    0 < Module.finrank F2 Y.range := by
  apply Nat.pos_of_ne_zero
  intro hr
  have hb : Y.range = ⊥ := Submodule.finrank_eq_zero.mp hr
  apply hY
  ext x
  have hx : Y x ∈ Y.range := ⟨x, rfl⟩
  rw [hb] at hx
  exact hx

end UniqueGamesTheorem.Appendix.DegreeZero

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixProducts

open scoped BigOperators
open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Multiplication of the real binary trace characters. -/
theorem linearTraceCharacter_re_add (S T : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    (linearTraceCharacter (S + T) X).re =
      (linearTraceCharacter S X).re * (linearTraceCharacter T X).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply]
  rw [← linearTraceCharacter_real S X, ← linearTraceCharacter_real T X]
  simp

variable [Fintype (E →ₗ[F2] F)]

/-- Multiplication by a trace character translates frequency. -/
theorem linearCoeff_mul_character (f : (E →ₗ[F2] F) → ℝ)
    (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * (linearTraceCharacter T X).re) S =
      linearCoeff f (S + T) := by
  simp only [linearCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [linearTraceCharacter_re_add]
  ac_rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (F →ₗ[F2] E)]

/-- Products transform to counting-measure convolution of normalized coefficients. -/
theorem linearCoeff_mul (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * g X) S =
      ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T) := by
  have hexpand : (fun X : E →ₗ[F2] F => f X * g X) =
      ∑ T : F →ₗ[F2] E, linearCoeff f T •
        (fun X => g X * (linearTraceCharacter T X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      f X * g X =
          (∑ T : F →ₗ[F2] E, linearCoeff f T * (linearTraceCharacter T X).re) * g X := by
        rw [linear_fourier_inversion]
      _ = ∑ T : F →ₗ[F2] E,
          linearCoeff f T * (g X * (linearTraceCharacter T X).re) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        ac_rfl
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_mul_character]

/-- The actual fourth moment equals the squared coefficient-convolution mass. -/
theorem expect_fourth_eq_sum_convolution_sq (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X ^ 4) =
      ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
  calc
    (𝔼 X, f X ^ 4) = 𝔼 X, (f X * f X) ^ 2 := by
      apply Finset.expect_congr rfl
      intro X _
      rw [← pow_two, ← pow_mul]
    _ = ∑ S : F →ₗ[F2] E, linearCoeff (fun X => f X * f X) S ^ 2 :=
      (linear_parseval (fun X => f X * f X)).symm
    _ = ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
      simp only [linearCoeff_mul, coefficientConvolution]

end UniqueGamesTheorem.Fourier.MatrixProducts

end

end

section

/-! The actual F1 witness bound in Lemma A.1. Coefficients remain signed;
absolute values occur only in the majorant. The two predecessor counts and
Cauchy–Schwarz give the factor `2^(6*d^2)`. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.F1Energy
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
local notation "G" => (E →ₗ[F2] F)
attribute [local instance] Classical.propDecidable

theorem rank_le_of_rankBelow {R Y : G} (h : RankBelow R Y) : rank R ≤ rank Y := by
  change rank Y = rank R + rank (Y - R) at h
  omega

theorem boundedSplit_rank (d : ℕ) (X : G) (R : BoundedSplit d X) : rank X ≤ 2*d := by
  have h := R.property.1
  change rank X = rank R.val + rank (X - R.val) at h
  simp only [sub_eq_add_neg, DegreeCover.binary_neg] at h
  have hR := R.property.2.1
  have hS := R.property.2.2
  omega

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- The checked geometric cover supplies exactly the F1 witness condition. -/
theorem good_of_trivial_intersections (X Y : G)
    (hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥)
    (hk : X.ker ⊔ Y.ker ⊔ (X+Y).ker = ⊤) : Good X Y := by
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  obtain ⟨R,S,C,hX,hY,hZ,hrX,hrY,hrZ⟩ :=
    DegreeCover.outside_bad_rank_cover Y (X+Y)
      (by simpa only [hc] using hi) (by simpa only [hc] using hk)
  have hXS : X = R+S := hc.symm.trans hX
  have hXR : X-R = S := by rw [hXS]; abel
  have hYR : Y-R = C := by rw [hY]; abel
  have hZS : (X+Y)-S = C := by rw [hZ]; abel
  have hSR : X+R = S := by simpa only [sub_eq_add_neg, DegreeCover.binary_neg] using hXR
  change rank (Y+(X+Y)) = rank R + rank S at hrX
  rw [hc] at hrX
  change rank Y = rank R + rank C at hrY
  change rank (X+Y) = rank S + rank C at hrZ
  refine ⟨R, ?_, ?_, ?_⟩
  · change rank X = rank R + rank (X-R)
    rw [hXR]
    exact hrX
  · change rank Y = rank R + rank (Y-R)
    rw [hYR]
    exact hrY
  · rw [hSR]
    change rank (X+Y) = rank S + rank ((X+Y)-S)
    rw [hZS]
    exact hrZ

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem sum_translate (R : G) (f : G → ℝ) :
    (∑ X, f (X+R)) = ∑ X, f X := Equiv.sum_comp (translate R) f

omit [FiniteDimensional F2 F] in
theorem card_bounded_splits_le (d : ℕ) (X : G) :
    Nat.card (BoundedSplit d X) ≤ 2^(4*d^2) := by
  classical
  by_cases h : Nonempty (BoundedSplit d X)
  · have hr := boundedSplit_rank d X (Classical.choice h)
    let inc : BoundedSplit d X → {R : G // RankBelow R X} :=
      fun R => ⟨R.val, R.property.1⟩
    have hinj : Function.Injective inc := by
      intro R S hRS
      exact Subtype.ext (congrArg (fun T : {R : G // RankBelow R X} => T.val) hRS)
    have hc := Nat.card_le_card_of_injective inc hinj
    have hp := TotalPredecessorCount.card_predecessors_le X
    change Nat.card {R : G // RankBelow R X} ≤ 2^(rank X^2) at hp
    have hs : rank X^2 ≤ 4*d^2 := by nlinarith
    exact hc.trans (hp.trans (Nat.pow_le_pow_right (by decide) hs))
  · have hz : Fintype.card (BoundedSplit d X) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun R => h ⟨R⟩⟩
    simp only [Nat.card_eq_fintype_card, hz, zero_le]

omit [FiniteDimensional F2 F] in
theorem card_predecessors_cast_le (d : ℕ) (Y : G) (hy : rank Y ≤ d) :
    (Fintype.card {R : G // RankBelow R Y} : ℝ) ≤ (2:ℝ)^(d^2) := by
  have h := TotalPredecessorCount.card_predecessors_le Y
  change Nat.card {R : G // RankBelow R Y} ≤ 2^(rank Y^2) at h
  have hs : rank Y^2 ≤ d^2 := by nlinarith
  have hp := h.trans (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.card_eq_fintype_card] at hp
  exact_mod_cast hp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_nonneg (a : G → ℝ) (R C : G) :
    0 ≤ predecessorCoefficient a R C := by
  unfold predecessorCoefficient
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem gram_nonneg (a : G → ℝ) (R S : G) : 0 ≤ gram a R S :=
  Finset.sum_nonneg (fun C _ => mul_nonneg
    (predecessorCoefficient_nonneg a R C) (predecessorCoefficient_nonneg a S C))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_sq (a : G → ℝ) (R C : G) :
    predecessorCoefficient a R C ^ 2 =
      if RankBelow R (R+C) then a (R+C)^2 else 0 := by
  unfold predecessorCoefficient
  split <;> simp only [sq_abs, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_eq (a : G → ℝ) :
    predecessorEnergy a =
      ∑ Y, (Fintype.card {R : G // RankBelow R Y} : ℝ) * a Y^2 := by
  unfold predecessorEnergy
  calc
    _ = ∑ R, ∑ Y, if RankBelow R Y then a Y^2 else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      simp only [predecessorCoefficient_sq]
      simpa only [add_comm] using
        sum_translate R (fun Y => if RankBelow R Y then a Y^2 else 0)
    _ = ∑ Y, ∑ R, if RankBelow R Y then a Y^2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← F1Gram.sum_subtype_eq (fun R => RankBelow R Y) (fun _ => a Y^2)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_nonneg (a : G → ℝ) : 0 ≤ predecessorEnergy a :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 F] in
theorem predecessor_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    predecessorEnergy a ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by
  rw [predecessor_energy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : rank Y ≤ d
  · exact mul_le_mul_of_nonneg_right (card_predecessors_cast_le d Y hY) (sq_nonneg _)
  · rw [hdegree Y (Nat.lt_of_not_ge hY)]
    simp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_nonneg (a : G → ℝ) (X : G) : 0 ≤ goodConvolution a X := by
  apply Finset.sum_nonneg
  intro Y _
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- Each supported good term has a bounded split witness. Its summand is
counted with shared residual C=Y+R; all other summands are nonnegative. -/
theorem good_term_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X Y : G) :
    (if Good X Y then |a Y| * |a (X+Y)| else 0) ≤
      ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) := by
  have hnonneg : 0 ≤ ∑ R : BoundedSplit d X,
      predecessorCoefficient a R.val (Y+R.val) *
        predecessorCoefficient a (X+R.val) (Y+R.val) :=
    Finset.sum_nonneg (fun R _ => mul_nonneg
      (predecessorCoefficient_nonneg a _ _) (predecessorCoefficient_nonneg a _ _))
  by_cases hg : Good X Y
  · rw [ite_eq_left hg]
    by_cases ha : a Y = 0
    · simpa only [ha, abs_zero, zero_mul] using hnonneg
    by_cases hb : a (X+Y) = 0
    · simpa only [hb, abs_zero, mul_zero] using hnonneg
    have hY : rank Y ≤ d := by
      by_contra hn
      exact ha (hdegree Y (Nat.lt_of_not_ge hn))
    have hZ : rank (X+Y) ≤ d := by
      by_contra hn
      exact hb (hdegree (X+Y) (Nat.lt_of_not_ge hn))
    obtain ⟨R,hRX,hRY,hSZ⟩ := hg
    let r : BoundedSplit d X := ⟨R,hRX,
      (rank_le_of_rankBelow hRY).trans hY, (rank_le_of_rankBelow hSZ).trans hZ⟩
    have h1 : R+(Y+R) = Y := by
      calc
        _ = (Y+R)+R := by abel
        _ = Y := add_self_cancel Y R
    have h2 : (X+R)+(Y+R) = X+Y := by
      calc
        _ = (X+Y)+(R+R) := by abel
        _ = X+Y := by rw [DegreeCover.binary_add_self, add_zero]
    have heq : predecessorCoefficient a r.val (Y+r.val) *
        predecessorCoefficient a (X+r.val) (Y+r.val) = |a Y| * |a (X+Y)| := by
      change predecessorCoefficient a R (Y+R) *
        predecessorCoefficient a (X+R) (Y+R) = _
      simp only [predecessorCoefficient, h1, h2, ite_eq_left hRY, ite_eq_left hSZ]
    rw [← heq]
    exact Finset.single_le_sum (fun (s : BoundedSplit d X) _ => mul_nonneg
      (predecessorCoefficient_nonneg a s.val (Y+s.val))
      (predecessorCoefficient_nonneg a (X+s.val) (Y+s.val)))
      (Finset.mem_univ r)
  · rw [ite_eq_right hg]
    exact hnonneg

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_le_gram (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) := by
  calc
    _ ≤ ∑ Y, ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) :=
      Finset.sum_le_sum (fun Y _ => good_term_le a d hdegree X Y)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R.val (fun C =>
        predecessorCoefficient a R.val C * predecessorCoefficient a (X+R.val) C)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_sq_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ^ 2 ≤ (2:ℝ)^(4*d^2) *
      ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
  have hg := goodConvolution_le_gram a d hdegree X
  have hn := goodConvolution_nonneg a X
  have hs : 0 ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) :=
    Finset.sum_nonneg (fun _ _ => gram_nonneg a _ _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : BoundedSplit d X => (1:ℝ)) (fun R => gram a R.val (X+R.val))
  have hcard : (Fintype.card (BoundedSplit d X) : ℝ) ≤ (2:ℝ)^(4*d^2) := by
    have h := card_bounded_splits_le d X
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ (∑ R : BoundedSplit d X, gram a R.val (X+R.val))^2 := by nlinarith
    _ ≤ (Fintype.card (BoundedSplit d X):ℝ) *
        ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by simpa using hc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem split_gram_energy_le (a : G → ℝ) (d : ℕ) :
    (∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2) ≤
      predecessorEnergy a ^ 2 := by
  calc
    _ ≤ ∑ X, ∑ R : G, gram a R (X+R)^2 := by
      apply Finset.sum_le_sum
      intro X _
      exact F1Gram.sum_comp_le (fun R : BoundedSplit d X => R.val)
        Subtype.val_injective (fun R => gram a R (X+R)^2) (fun _ => sq_nonneg _)
    _ = ∑ R, ∑ S, gram a R S^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R (fun S => gram a R S^2)
    _ ≤ predecessorEnergy a ^ 2 := F1Gram.gram_energy_le (predecessorCoefficient a)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, goodConvolution a X^2) ≤ (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
  have he := predecessor_energy_le a d hdegree
  have hn := predecessor_energy_nonneg a
  have hb : 0 ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by positivity
  calc
    _ ≤ (2:ℝ)^(4*d^2) *
        ∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun X _ => goodConvolution_sq_le a d hdegree X)
    _ ≤ (2:ℝ)^(4*d^2) * predecessorEnergy a^2 :=
      mul_le_mul_of_nonneg_left (split_gram_energy_le a d) (by positivity)
    _ ≤ (2:ℝ)^(4*d^2) * ((2:ℝ)^(d^2) * ∑ Y, a Y^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      omega

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- The complement of any bad event covered by `Good` is bounded without
changing the signs of the coefficients in the bad part. -/
theorem abs_complement_sum_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    |∑ Y, if bad Y then 0 else a Y * a (X+Y)| ≤ goodConvolution a X := by
  calc
    _ ≤ ∑ Y, |if bad Y then 0 else a Y * a (X+Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ goodConvolution a X := by
      apply Finset.sum_le_sum
      intro Y _
      by_cases hb : bad Y
      · simp only [ite_eq_left hb, abs_zero]
        split <;> positivity
      · simp only [ite_eq_right hb, ite_eq_left (hcover Y hb), abs_mul, le_refl]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem convolution_split_square_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 +
      2 * (∑ Y, if bad Y then a Y * a (X+Y) else 0)^2 := by
  let u : ℝ := ∑ Y, if bad Y then 0 else a Y * a (X+Y)
  let v : ℝ := ∑ Y, if bad Y then a Y * a (X+Y) else 0
  have hs : (∑ Y, a Y * a (X+Y)) = u+v := by
    dsimp only [u,v]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hb : bad Y <;> simp only [hb, ite_true, if_true, ite_false, if_false, add_zero, zero_add]
  have hu : |u| ≤ goodConvolution a X := abs_complement_sum_le a X bad hcover
  have hp := mul_nonneg (sub_nonneg.mpr hu)
    (add_nonneg (goodConvolution_nonneg a X) (abs_nonneg u))
  have hu2 : u^2 ≤ goodConvolution a X^2 := by nlinarith [sq_abs u]
  change (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 + 2*v^2
  rw [hs]
  nlinarith [sq_nonneg (u-v)]

omit [FiniteDimensional F2 F] in
theorem convolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (bad : G → G → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (∑ X, (∑ Y, a Y * a (X+Y))^2) ≤
      2 * ((2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
  calc
    _ ≤ ∑ X, (2 * goodConvolution a X^2 +
        2 * (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2) :=
      Finset.sum_le_sum (fun X _ => convolution_split_square_le a X (bad X) (hcover X))
    _ = 2 * (∑ X, goodConvolution a X^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (goodConvolution_energy_le a d hdegree)
        (show (0:ℝ) ≤ 2 by norm_num)) le_rfl

variable [Fintype (F →ₗ[F2] E)]
open UniqueGamesTheorem.Fourier.MatrixFourier UniqueGamesTheorem.Fourier.MatrixProducts

/-- The actual fourth-moment identity reduced to the remaining signed bad
convolution. Its geometric cover is supplied by `good_of_trivial_intersections`. -/
theorem fourth_moment_le_good_bad (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E, d < rank Y → linearCoeff f Y = 0)
    (bad : (F →ₗ[F2] E) → (F →ₗ[F2] E) → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (𝔼 X, f X^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 X, f X^2)^2) +
      2 * ∑ X, (∑ Y, if bad X Y then linearCoeff f Y * linearCoeff f (X+Y) else 0)^2 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  unfold coefficientConvolution
  simpa only [linear_parseval] using
    convolution_energy_le (linearCoeff f) d hdegree bad hcover

end UniqueGamesTheorem.Appendix.F1Energy

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Appendix.Restriction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

section ActualRestrictions

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- Trace compatibility on the actual quotient restriction. -/
theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair UniqueGamesTheorem.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in
/-- The complex character identity in (A.1), on actual binary linear maps. -/
theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro Y _
    rw [real_character_restriction]
    ring
  rw [hexpansion, linearCoeff_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_smul, linearCoeff_character]
  by_cases h : compressFrequency A B Y = Z
  · simp [h]
  · simp [h, Ne.symm h]

end ActualRestrictions

end UniqueGamesTheorem.Appendix.Restriction

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.Derivatives
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linearCoeff_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector P f) Y = if P Y then linearCoeff f Y else 0 := by
  classical
  unfold spectralProjector
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

variable [Finite E] [Finite F]

theorem linearCoeff_mapDerivative (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) (Z : X.ker →ₗ[F2] (E ⧸ X.range)) :
    linearCoeff (mapDerivative X f) Z =
      ∑ Y : F →ₗ[F2] E,
        if RankAdditivity.RankBelow X Y ∧
            Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0 := by
  classical
  unfold mapDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [rankProjector, linearCoeff_spectralProjector]
  have hp : (linearTraceCharacter Y (0 : E →ₗ[F2] F)).re = 1 := by simp
  rw [hp]
  by_cases hR : RankAdditivity.RankBelow X Y <;>
    by_cases hC : Restriction.compressFrequency X.range X.ker Y = Z <;> simp [hR, hC]

end UniqueGamesTheorem.Appendix.Derivatives

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.A1Reduction
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier UniqueGamesTheorem.Fourier.MatrixProducts
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem weakFourthSum_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ weakFourthSum d f := by
  apply Finset.sum_nonneg
  intro p _
  split
  · exact mul_nonneg (by positivity) (Finset.expect_nonneg (fun _ _ => by positivity))
  · exact le_rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem linearCoeff_weakProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector (fun Z => A ≤ Z.range ∧ Z.ker ≤ B) f) Y =
      BadConvolution.filteredCoefficient A B (linearCoeff f) Y := by
  simp only [linearCoeff_spectralProjector, BadConvolution.filteredCoefficient,
    BadConvolution.Incidence]
  rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
/-- Actual Parseval/product identity for each signed weakly selected piece. -/
theorem piece_fourth_moment (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ X : F →ₗ[F2] E, BadConvolution.pieceConvolution A B (linearCoeff f) X^2) =
      𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M^4 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  simp only [coefficientConvolution, BadConvolution.pieceConvolution,
    linearCoeff_weakProjector]

omit [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem actual_bad_cover (X Y : F →ₗ[F2] E) (hbad : ¬ BadConvolution.Bad X Y) :
    F1Energy.Good X Y := by
  apply F1Energy.good_of_trivial_intersections X Y
  · by_contra hi
    exact hbad (Or.inl hi)
  · by_contra hk
    exact hbad (Or.inr hk)

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem badConvolution_zero_of_degree_zero (a : (F →ₗ[F2] E) → ℝ)
    (ha : ∀ Y, 0 < Module.finrank F2 Y.range → a Y = 0) (X : F →ₗ[F2] E) :
    BadConvolution.badConvolution a X = 0 := by
  classical
  unfold BadConvolution.badConvolution
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : Y = 0
  · subst Y
    by_cases hX : X = 0
    · subst X
      simp [BadConvolution.Bad]
    · have hz := ha X (DegreeZero.rank_pos_of_ne_zero X hX)
      simp [hz]
  · have hz := ha Y (DegreeZero.rank_pos_of_ne_zero Y hY)
    simp [hz]

theorem badConvolution_energy_le_weakFourthSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2) ≤
      weakFourthSum d f := by
  by_cases hd : d = 0
  · subst d
    have hz : ∀ X, BadConvolution.badConvolution (linearCoeff f) X = 0 :=
      badConvolution_zero_of_degree_zero (linearCoeff f) hdegree
    simpa only [hz, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Finset.sum_const_zero] using weakFourthSum_nonneg 0 f
  · have h := BadConvolution.badConvolution_sq_sum_le (linearCoeff f) d (by omega) hdegree
    simpa only [weakFourthSum, piece_fourth_moment] using h

theorem fourth_moment_le_two (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * weakFourthSum d f := by
  have hcore : (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * ∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2 := by
    simpa only [BadConvolution.badConvolution] using
      F1Energy.fourth_moment_le_good_bad f d hdegree BadConvolution.Bad actual_bad_cover
  exact hcore.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (badConvolution_energy_le_weakFourthSum f d hdegree) (show (0:ℝ) ≤ 2 by norm_num)))

/-- Lemma A.1, Equation (A.6), for every degree d including zero. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) / 162 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 + weakFourthSum d f := by
  have h := fourth_moment_le_two f d hdegree
  have ha : 0 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 := by positivity
  have hb := weakFourthSum_nonneg d f
  apply (div_le_iff₀ (show (0:ℝ) < 162 by norm_num)).mpr
  nlinarith

end UniqueGamesTheorem.Appendix.A1Reduction

end

end

section

/-! Actual Fourier degree loss for both derivative operators. The support
cutoffs apply to genuine binary linear maps, including the case where the
total derivative order is larger than the original degree. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.DerivativeDegree

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem eq_zero_of_linearCoeff_zero {f : (E →ₗ[F2] F) → ℝ}
    (hf : ∀ Y, linearCoeff f Y = 0) : f = 0 := by
  funext M
  rw [← linear_fourier_inversion f M]
  simp [hf]

variable [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.compressedDualFintype
theorem hybridDerivative_coeff_zero_of_lt (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : d < frequencyRank Z + order A B) :
    linearCoeff (hybridDerivative A B T f) Z = 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hc : Restriction.compressFrequency A B Y = Z
  · rw [ite_eq_left hc]
    unfold hybridProjector
    rw [linearCoeff_spectralProjector]
    by_cases hY : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hY]
      have hr := Level.LinearRank.hybrid_rank_loss A B Y hY.1 hY.2
      have he : Level.LinearRank.compress A B Y = Z := by
        simpa only [Level.LinearRank.compress, Restriction.compressFrequency,
          LinearMap.comp_assoc] using hc
      rw [he] at hr
      have hr' : frequencyRank Z + order A B = frequencyRank Y := by
        simpa only [frequencyRank, order, Nat.add_assoc] using hr
      have hdY : d < frequencyRank Y := hZ.trans_eq hr'
      rw [hf Y hdY, zero_mul]
    · rw [ite_eq_right hY, zero_mul]
  · rw [ite_eq_right hc]

theorem degree_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) {d : ℕ} (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    DegreeAtMost (d - order A B) (hybridDerivative A B T f) := by
  intro Z hZ
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem hybridDerivative_eq_zero_of_lt_order (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B) : hybridDerivative A B T f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem mapDerivative_coeff_zero_of_lt (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : X.ker →ₗ[F2] (E ⧸ X.range))
    (hZ : d < frequencyRank Z + frequencyRank X) :
    linearCoeff (mapDerivative X f) Z = 0 := by
  rw [linearCoeff_mapDerivative]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : RankAdditivity.RankBelow X Y ∧
      Restriction.compressFrequency X.range X.ker Y = Z
  · rw [ite_eq_left hY]
    have hc : FullCompression.compression X Y = Z := by
      simpa only [FullCompression.compression, Restriction.compressFrequency] using hY.2
    have hr := FullCompression.fiber_rank X Z
      (⟨Y, hY.1, hc⟩ : FullCompression.Fiber X Z)
    apply hf Y
    unfold frequencyRank at *
    change Module.finrank F2 Y.range =
      Module.finrank F2 X.range + Module.finrank F2 Z.range at hr
    omega
  · rw [ite_eq_right hY]

theorem mapDerivative_eq_zero_of_lt_rank (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < frequencyRank X) : mapDerivative X f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_zero (X : F →ₗ[F2] E) :
    mapDerivative X (0 : (E →ₗ[F2] F) → ℝ) = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  rw [linearCoeff_mapDerivative]
  simp [linearCoeff]

/-- The support cutoff keeps the total order intact even when `order A B > d`. -/
theorem map_hybridDerivative_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    mapDerivative X (hybridDerivative A B T f) = 0 := by
  by_cases hAB : d < order A B
  · rw [hybridDerivative_eq_zero_of_lt_order A B T f hf hAB, mapDerivative_zero]
  · apply mapDerivative_eq_zero_of_lt_rank X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)
    unfold frequencyRank
    omega

theorem map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) = 0 := by
  simp_rw [map_hybridDerivative_eq_zero_of_lt_order_rank A B X _ f hf h]
  simp

end UniqueGamesTheorem.Appendix.DerivativeDegree

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

theorem tripleMoment_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleMoment p f = 0 :=
  DerivativeDegree.map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    p.1 p.2.1 p.2.2 f hf h

theorem tripleTerm_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleTerm d p f = 0 := by
  unfold tripleTerm
  rw [tripleMoment_eq_zero_of_lt_size p f hf h, mul_zero]

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

theorem positiveTripleSum_eq_bounded (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    positiveTripleSum d f = boundedPositiveTripleSum d f := by
  classical
  unfold positiveTripleSum boundedPositiveTripleSum
  rw [F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) => 0 < A13Index.size p)
      (fun p => tripleTerm d p f),
    F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) =>
        0 < A13Index.size p ∧ A13Index.size p ≤ d)
      (fun p => tripleTerm d p f)]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 0 < A13Index.size p
  · by_cases ht : A13Index.size p ≤ d
    · rw [ite_eq_left hp, ite_eq_left ⟨hp, ht⟩]
    · rw [ite_eq_left hp, ite_eq_right (fun h => ht h.2)]
      exact tripleTerm_eq_zero_of_lt_size p f hf (Nat.lt_of_not_ge ht)
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.1)]

/-- Equation A.13 with the literal positive-triple sum. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + positiveTripleSum d f := by
  have hbase := A1Reduction.degree_reduction f d (fun Y hY => hf Y hY)
  exact hbase.trans (add_le_add le_rfl (weakFourthSum_le_positiveTripleSum f d hf))

/-- Equation A.13 after removing terms whose actual derivative is zero. -/
theorem degree_reduction_truncated_oai (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f := by
  simpa only [positiveTripleSum_eq_bounded f d hf] using degree_reduction f d hf

end UniqueGamesTheorem.Appendix.A13Reduction

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated_oai.{u_1, u_2}
