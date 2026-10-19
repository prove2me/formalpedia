-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.Model.entropy_deficit_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:14:09.60746+00:00
-- url     : https://prove2.me/submissions/86223785-5c9d-4ec3-987c-84a2bdf382e9

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002
import Theorems.Thm_OAI_FiniteEntropySeparation_lowerSemicontinuous_freeFisher

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem trace_add {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A + B) = trace τ A + trace τ B := by
  simp [trace]

 theorem trace_smul {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (z : ℂ) (A : H →L[ℂ] H) : trace τ (z • A) = z * trace τ A := by
  simp [trace]

 theorem trace_sum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {α : Type u1} (s : Finset α) (A : α → H →L[ℂ] H) :
    trace τ (∑ a ∈ s, A a) = ∑ a ∈ s, trace τ (A a) := by
  simp [trace]

theorem ConjugateSystem.unique {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ η : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (hη : ConjugateSystem τ X η) : ξ = η := by
  funext i
  have hmem : ξ i - η i ∈ polynomialL2 τ X :=
    (polynomialL2 τ X).sub_mem (hξ i).1 (hη i).1
  have hker : polynomialL2 τ X ≤ (innerSL ℂ (ξ i - η i)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change inner ℂ (ξ i - η i) (wordEval X w τ.vacuum) = 0
      rw [inner_sub_left, (hξ i).2 w, (hη i).2 w, sub_self]
    · exact (innerSL ℂ (ξ i - η i)).isClosed_ker
  have hd : inner ℂ (ξ i - η i) (ξ i - η i) = 0 := hker hmem
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hd)

theorem freeFisher_eq_of_conjugate {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ENNReal.ofReal (∑ i, ‖ξ i‖ ^ 2) := by
  apply le_antisymm
  · exact iInf_le_of_le ξ (iInf_le_of_le hξ le_rfl)
  · refine le_iInf fun η => le_iInf fun hη => ?_
    rw [hξ.unique τ hη]

 theorem wordVector_mem_polynomialL2 {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (w : List (Fin n)) :
    wordEval X w τ.vacuum ∈ polynomialL2 τ X :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)

 theorem projectedConjugate_system {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    ConjugateSystem τ X (projectedConjugate τ X η) := by
  intro i
  refine ⟨(polynomialL2 τ X).starProjection_apply_mem _, fun w => ?_⟩
  have h := (polynomialL2 τ X).starProjection_inner_eq_zero (η i)
    (wordEval X w τ.vacuum) (wordVector_mem_polynomialL2 τ X w)
  rw [inner_sub_left, hη i w] at h
  exact (sub_eq_zero.mp h).symm

theorem freeFisher_le_testVectors {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    freeFisher τ X ≤ ENNReal.ofReal (∑ i, ‖η i‖ ^ 2) := by
  rw [freeFisher_eq_of_conjugate τ (projectedConjugate_system τ X η hη)]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) ((polynomialL2 τ X).norm_starProjection_apply_le _) _

 theorem conjugate_coordinate_pairing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) : inner ℂ (ξ i) (X i τ.vacuum) = 1 := by
  have h := (hξ i).2 [i]
  simpa [wordEval, derivativeMoment, wordMoment, trace_one] using h

theorem conjugate_norm_sq_lower {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) :
    1 / ‖X i τ.vacuum‖ ^ 2 ≤ ‖ξ i‖ ^ 2 := by
  have h : 1 ≤ ‖ξ i‖ * ‖X i τ.vacuum‖ := by
    simpa only [conjugate_coordinate_pairing τ hξ i, norm_one] using
      norm_inner_le_norm (𝕜 := ℂ) (ξ i) (X i τ.vacuum)
  have hp : 0 < ‖X i τ.vacuum‖ := by
    have hn := norm_nonneg (X i τ.vacuum)
    by_contra hh
    have hz : ‖X i τ.vacuum‖ = 0 := le_antisymm (not_lt.mp hh) hn
    rw [hz, mul_zero] at h
    linarith
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith [sq_nonneg (‖ξ i‖ * ‖X i τ.vacuum‖ - 1)]

omit [CompleteSpace H] in
 theorem commutatorKernel_cons {n : ℕ} (P : H →L[ℂ] H)
    (X : Fin n → H →L[ℂ] H) (i j : Fin n) (w : List (Fin n)) :
    commutatorKernel P X i (j :: w) =
      (if j = i then P * wordEval X w else 0) + X j * commutatorKernel P X i w := by
  simp only [commutatorKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

omit [CompleteSpace H] in
 theorem commutator_word {n : ℕ} (P a : H →L[ℂ] H) (X : Fin n → H →L[ℂ] H)
    (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • P else 0)
    (w : List (Fin n)) :
    a * wordEval X w = wordEval X w * a + c • commutatorKernel P X i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval X (j :: w) = X j * wordEval X w := by simp [wordEval]
    rw [hw, commutatorKernel_cons, ← mul_assoc, h, add_mul, mul_assoc, ih]
    by_cases hji : j = i <;>
      simp [hji, mul_add, mul_assoc, smul_add, _root_.add_assoc, _root_.add_comm,
        _root_.add_left_comm]

 theorem trace_vacuumRankOne_product {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A * vacuumRankOne τ * B) = trace τ A * trace τ B := by
  simp only [trace, vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
    map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) :
    trace τ (commutatorKernel (vacuumRankOne τ) X i w) = derivativeMoment τ X i w := by
  rw [commutatorKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_vacuumRankOne_product, wordMoment]

theorem commutator_integration_by_parts {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (a : H →L[ℂ] H) (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • vacuumRankOne τ else 0)
    (hz : a τ.vacuum = 0) (w : List (Fin n)) :
    inner ℂ (star a τ.vacuum) (wordEval X w τ.vacuum) = c * derivativeMoment τ X i w := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change trace τ (a * wordEval X w) = _
  rw [commutator_word _ _ _ _ _ h, trace_add, trace_smul, trace_commutatorKernel]
  have hzero : trace τ (wordEval X w * a) = 0 := by
    simp [trace, mul_apply_eq_comp, hz]
  rw [hzero, zero_add]

namespace Fock

open scoped lp
variable {ι : Type} [DecidableEq ι]

 theorem creation_commutes_rightCreation (i j : ι) :
    Commute (creation i) (rightCreation j) := by
  show creation i * rightCreation j = rightCreation j * creation i
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creation i (rightCreation j (lp.single 2 w z)) =
    rightCreation j (creation i (lp.single 2 w z))
  simp

 theorem rightAnnihilation_creation (i j : ι) :
    star (rightCreation i) * creation j = creation j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreation i) (creation j (lp.single 2 w z)) =
    creation j (star (rightCreation i) (lp.single 2 w z)) +
      (if i = j then vacuumProjection else 0) (lp.single 2 w z)
  induction w using List.reverseRecOn with
  | nil =>
    rw [creation_single, show [j] = [] ++ [j] from rfl, rightAnnihilation_single_append]
    by_cases h : i = j <;> simp [h]
  | append_singleton w k _ =>
    rw [creation_single, show j :: (w ++ [k]) = (j :: w) ++ [k] from rfl,
      rightAnnihilation_single_append]
    have hp : (if i = j then vacuumProjection else 0) (lp.single 2 (w ++ [k]) z) = 0 := by
      split_ifs <;> simp
    rw [hp, rightAnnihilation_single_append]
    by_cases h : i = k <;> simp [h]

theorem rightAnnihilation_semicircular (i j : ι) :
    star (rightCreation i) * semicircular j = semicircular j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  have h : star (rightCreation i) * star (creation j) =
      star (creation j) * star (rightCreation i) := by
    simpa only [star_mul] using congrArg star (creation_commutes_rightCreation j i).eq
  rw [semicircular, mul_add, add_mul, rightAnnihilation_creation, h]
  abel

 theorem derivativeKernel_cons {n : ℕ} (i j : Fin n) (w : List (Fin n)) :
    derivativeKernel i (j :: w) =
      (if j = i then vacuumProjection * wordEval semicircular w else 0) +
        semicircular j * derivativeKernel i w := by
  simp only [derivativeKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

 theorem rightAnnihilation_word {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    star (rightCreation i) * wordEval semicircular w =
      wordEval semicircular w * star (rightCreation i) + derivativeKernel i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval semicircular (j :: w) = semicircular j * wordEval semicircular w := by
      simp [wordEval]
    rw [hw, derivativeKernel_cons, ← mul_assoc, rightAnnihilation_semicircular,
      add_mul, mul_assoc, ih, mul_add]
    by_cases h : i = j <;> simp [h, eq_comm, mul_assoc, add_assoc, add_comm, add_left_comm]

 theorem trace_projection_product (A B : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (A * vacuumProjection * B) =
      trace (tracialVector ι) A * trace (tracialVector ι) B := by
  simp only [trace, tracialVector, vacuumProjection, mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply, map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_derivativeKernel {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (derivativeKernel i w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [derivativeKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_projection_product, wordMoment]

 theorem trace_semicircular_left (i : ι) (A : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (semicircular i * A) =
      trace (tracialVector ι) (star (rightCreation i) * A) := by
  simp only [trace, tracialVector, mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left (semicircular i),
    ← ContinuousLinearMap.adjoint_inner_left (star (rightCreation i))]
  simp only [← ContinuousLinearMap.star_eq_adjoint, star_star,
    (semicircular_selfAdjoint i).star_eq, basisVector,
    semicircular_single_nil, rightCreation_single, List.nil_append]

theorem semicircular_integration_by_parts {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (semicircular i * wordEval semicircular w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [trace_semicircular_left, rightAnnihilation_word, trace_add, trace_derivativeKernel]
  suffices trace (tracialVector (Fin n))
      (wordEval semicircular w * star (rightCreation i)) = 0 by rw [this, zero_add]
  simp [trace, tracialVector, basisVector, mul_apply_eq_comp]

end Fock

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem freeFisher_lt_top_iff {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) :
    freeFisher τ X < ⊤ ↔ ∃ ξ, ConjugateSystem τ X ξ := by
  constructor
  · intro h
    by_contra! hn
    have he : freeFisher τ X = ⊤ := by simp [freeFisher, hn]
    rw [he] at h
    exact lt_irrefl _ h
  · rintro ⟨ξ,hξ⟩
    rw [freeFisher_eq_of_conjugate τ hξ]
    exact ENNReal.ofReal_lt_top

 theorem exists_conjugate_of_fisher_le {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (c : ℝ)
    (h : freeFisher τ X ≤ ENNReal.ofReal c) : ∃ ξ, ConjugateSystem τ X ξ :=
  (freeFisher_lt_top_iff τ X).mp (h.trans_lt ENNReal.ofReal_lt_top)

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TracialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem leftGenerator_mem (k : Generator B N G) : leftGenerator k ∈ algebra B N G :=
  (mem_algebra_iff _).mpr (generators_commute k)

 theorem semicircularB_mem (b : B) : semicircularB (N := N) (G := G) b ∈ algebra B N G :=
  leftGenerator_mem (.inl b)
 theorem semicircularN_mem (i : N) : semicircularN (B := B) (G := G) i ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inl i))
 theorem unitaryG_mem (g : G) : unitaryG (B := B) (N := N) g ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inr g))

 theorem trace_unitaryG (g : G) :
    trace (tracialVector B N G) (unitaryG g) = if g = 1 then 1 else 0 := by
  change inner ℂ (basis empty) (unitaryG g (basis empty)) = _
  rw [unitaryG_basis]
  by_cases hg : g = 1 <;> simp [basis, leftG, empty, lp.inner_single_left, lp.single_apply, hg, eq_comm]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem vacuumBoundary_eq_rankOne :
    vacuumBoundary (B := B) (N := N) (G := G) = vacuumRankOne (tracialVector B N G) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change vacuumBoundary (lp.single 2 w z) = _
  rw [vacuumBoundary_single]
  by_cases hw : w = empty
  · subst w
    simp [vacuumRankOne, tracialVector, basis, lp.inner_single_left]
    simpa using (lp.single_smul (E := fun _ : Word B N G => ℂ) 2 (empty : Word B N G) z (1 : ℂ))
  · simp [hw, vacuumRankOne, tracialVector, basis, lp.inner_single_left, lp.single_apply, Ne.symm hw]

 theorem rightAnnihilationN_semicircularN (i j : N) :
    star (rightCreationN (B := B) (G := G) i) * semicircularN j =
      semicircularN j * star (rightCreationN i) + if i = j then
        vacuumRankOne (tracialVector B N G) else 0 := by
  have h : Commute (creationN (B := B) (G := G) j) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftN_rightN j i)
  have hs := h.star_star.symm.eq
  rw [semicircularN, mul_add, add_mul, rightAnnihilationN_creationN, hs,
    vacuumBoundary_eq_rankOne]
  abel

 theorem rightAnnihilationN_commutes_semicircularB (i : N) (b : B) :
    Commute (star (rightCreationN (G := G) i)) (semicircularB b) := by
  have h : Commute (creationB (G := G) b) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftB_rightN b i)
  exact (creationB_commutes_rightAnnihilationN b i).symm.add_right h.star_star.symm

 theorem rightAnnihilationN_background {i : N} {J : Set N} (hi : i ∉ J)
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    Commute (star (rightCreationN i)) T := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨j,hj,rfl⟩)
    · exact rightAnnihilationN_commutes_semicircularB i b
    · exact (unitaryG_commutes_rightAnnihilationN g i).symm
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      show _ * _ = _ * _
      simpa [hij] using rightAnnihilationN_semicircularN (B := B) (G := G) i j
  | algebraMap z => exact (Algebra.commute_algebraMap_left z _).symm
  | add T U _ _ hT hU => exact hT.add_right hU
  | mul T U _ _ hT hU => exact hT.mul_right hU

theorem heat_freeFisher_le {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    freeFisher (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) ≤
      ENNReal.ofReal ((n : ℝ) / u) := by
  let Z := heatTuple X (fun i => semicircularN (σ i)) u
  let η : Fin n → Space B N G := fun i =>
    ((Real.sqrt u)⁻¹ : ℂ) • basis (leftN (σ i) empty)
  have hc (i j : Fin n) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
    change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
    rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
      rightAnnihilationN_semicircularN]
    change _ = (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) *
      star (rightCreationN (σ i)) +
      if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0
    by_cases hij : j = i
    · subst j
      simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
      congr 1
      exact smul_add _ _ _
    · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
      simp only [hij, hneq, ↓reduceIte, add_zero, add_mul, smul_mul_assoc]
  have hu' : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have hη (i : Fin n) (w : List (Fin n)) :
      inner ℂ (η i) (wordEval Z w (tracialVector B N G).vacuum) =
        derivativeMoment (tracialVector B N G) Z i w := by
    have h := commutator_integration_by_parts (tracialVector B N G) Z
      (star (rightCreationN (σ i))) i (Real.sqrt u) (hc i)
      (by simp [tracialVector, basis, empty]) w
    simp only [star_star, tracialVector, basis, rightCreationN_single] at h
    have he : rightN (σ i) (empty : Word B N G) = leftN (σ i) empty := by
      simp [rightN_eq_append, empty, leftN, push, append]
    rw [he] at h
    change inner ℂ (((Real.sqrt u : ℂ)⁻¹) • lp.single 2 (leftN (σ i) empty) 1)
      (wordEval Z w (lp.single 2 empty 1)) = _
    rw [inner_smul_left, h]
    simp [hu', tracialVector, basis]
  refine (freeFisher_le_testVectors (tracialVector B N G) Z η hη).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnorm (i : Fin n) : ‖η i‖ ^ 2 = u⁻¹ := by
    simp [η, norm_smul, basis, norm_inv,
      lp.norm_single (E := fun _ : Word B N G => ℂ) (p := 2),
      abs_of_nonneg (Real.sqrt_nonneg u), inv_pow, Real.sq_sqrt (le_of_lt hu)]
  simp [hnorm, div_eq_mul_inv]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem continuous_heatTuple {n : ℕ} (X S : Fin n → H →L[ℂ] H) (i : Fin n) :
    Continuous (fun u : ℝ => heatTuple X S u i) := by
  unfold heatTuple
  fun_prop

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem heat_conjugates_exist {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    ∃ ξ, ConjugateSystem (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u) ξ :=
  exists_conjugate_of_fisher_le _ _ (n/u) (heat_freeFisher_le J X hX σ hσ hs u hu)

 theorem heat_freeFisher_measurable {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    Measurable (fun u : Set.Ioi (0 : ℝ) => freeFisher (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u.val)) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_freeFisher (tracialVector B N G)
  · intro i
    exact (continuous_heatTuple X (fun i => semicircularN (σ i)) i).comp continuous_subtype_val
  · intro u
    exact heat_conjugates_exist J X hX σ hσ hs u.val u.property

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

 theorem conv_sum_splits (f g : Series α) (w : List α) :
    conv f g w = ∑ k ∈ range (w.length+1), f (w.take k) * g (w.drop k) := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [conv_cons, ih, List.length_cons]
    conv_rhs => rw [sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons, deriv_apply]
    ring

 theorem conv_add_left (f g h : Series α) : conv (f+g) h = conv f h + conv g h := by
  funext w
  simp only [conv_sum_splits, Pi.add_apply, add_mul, sum_add_distrib]
 theorem conv_add_right (f g h : Series α) : conv f (g+h) = conv f g + conv f h := by
  funext w
  simp only [conv_sum_splits, Pi.add_apply, mul_add, sum_add_distrib]
 theorem conv_smul_left (c : ℂ) (f g : Series α) : conv (c • f) g = c • conv f g := by
  funext w
  simp only [conv_sum_splits, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]
 theorem conv_smul_right (c : ℂ) (f g : Series α) : conv f (c • g) = c • conv f g := by
  funext w
  simp only [conv_sum_splits, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro k _
  ring
@[simp] theorem conv_zero_left (f : Series α) : conv 0 f = 0 := by
  funext w
  simp [conv_sum_splits]
@[simp] theorem conv_zero_right (f : Series α) : conv f 0 = 0 := by
  funext w
  simp [conv_sum_splits]
 theorem deriv_conv (a : α) (f g : Series α) :
    deriv a (conv f g) = f [] • deriv a g + conv (deriv a f) g := rfl

@[simp] theorem conv_unit_left (f : Series α) : conv unit f = f := by
  funext w
  cases w <;> simp [conv, deriv_unit]

 theorem conv_assoc (f g h : Series α) : conv (conv f g) h = conv f (conv g h) := by
  funext w
  induction w generalizing f g h with
  | nil => simp [mul_assoc]
  | cons a w ih =>
    simp only [conv_cons, conv_nil, deriv_conv, conv_add_left, conv_smul_left,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih]
    ring

 theorem conv_neg_left (f g : Series α) : conv (-f) g = -conv f g := by
  simpa using conv_smul_left (-1) f g
 theorem conv_neg_right (f g : Series α) : conv f (-g) = -conv f g := by
  simpa using conv_smul_right (-1) f g
 theorem conv_sub_left (f g h : Series α) : conv (f-g) h = conv f h - conv g h := by
  simp [sub_eq_add_neg, conv_add_left, conv_neg_left]
 theorem conv_sub_right (f g h : Series α) : conv f (g-h) = conv f g - conv f h := by
  simp [sub_eq_add_neg, conv_add_right, conv_neg_right]

 theorem conv_agree {n : ℕ} {f f' g g' : Series α} (hf : Agree n f f') (hg : Agree n g g') :
    Agree n (conv f g) (conv f' g') := by
  intro w hw
  simp only [conv_sum_splits]
  apply sum_congr rfl
  intro k hk
  rw [hf _ (by simp only [List.length_take]; omega),
    hg _ (by simp only [List.length_drop]; omega)]

theorem length_induction {P : List α → Prop} (w : List α)
    (h : ∀ w, (∀ v, v.length < w.length → P v) → P w) : P w :=
  (measure List.length).wf.induction w h

 theorem subst_cons (M f : Series α) (a : α) (w : List α) :
    subst M f (a::w) = conv M (subst M (deriv a f)) w := by
  rw [subst, conv_sum_splits]
 theorem deriv_subst (M f : Series α) (a : α) :
    deriv a (subst M f) = conv M (subst M (deriv a f)) := by
  funext w
  exact subst_cons M f a w

 theorem subst_add (M f g : Series α) : subst M (f+g) = subst M f + subst M g := by
  funext w
  induction w using length_induction generalizing f g with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.add_apply]
      simp_rw [show deriv a (f+g) = deriv a f + deriv a g from rfl]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_add]

 theorem subst_smul (M f : Series α) (c : ℂ) : subst M (c • f) = c • subst M f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.smul_apply, smul_eq_mul]
      simp_rw [show deriv a (c • f) = c • deriv a f from rfl]
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_left_comm]

@[simp] theorem subst_zero (M : Series α) : subst M 0 = 0 := by
  have h := subst_smul M 0 0
  simpa using h
@[simp] theorem subst_unit (M : Series α) : subst M unit = unit := by
  funext w
  cases w with
  | nil => simp
  | cons a w => simp [subst_cons]

 theorem subst_mul (M f g : Series α) : subst M (conv f g) = conv (subst M f) (subst M g) := by
  funext w
  induction w using length_induction generalizing f g with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [subst_cons, deriv_conv, subst_add, subst_smul, conv_add_right, conv_smul_right]
      rw [conv_cons, subst_nil, subst_cons, deriv_subst, conv_assoc]
      change f [] * _ + _ = f [] * _ + _
      congr 1
      apply conv_agree (n := w.length) (fun _ _ => rfl) (fun v hv => ?_) w le_rfl
      exact ih v (by simp ; omega) _ _

 theorem subst_neg (M f : Series α) : subst M (-f) = -subst M f := by
  simpa using subst_smul M f (-1)
 theorem subst_sub (M f g : Series α) : subst M (f-g) = subst M f - subst M g := by
  simp [sub_eq_add_neg, subst_add, subst_neg]

 theorem subst_unit_left (f : Series α) : subst unit f = f := by
  funext w
  induction w generalizing f with
  | nil => simp
  | cons a w ih => rw [subst_cons, conv_unit_left, ih]; rfl

theorem subst_comp (L M f : Series α) :
    subst L (subst M f) = subst (conv L (subst L M)) f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [subst_cons, deriv_subst, subst_mul, ← conv_assoc, subst_cons]
      apply conv_agree (n := w.length) (fun _ _ => rfl) (fun v hv => ?_) w le_rfl
      exact ih v (by simp ; omega) _

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

 theorem Agree.mono {n m : ℕ} {f g : Series α} (h : Agree n f g) (hmn : m ≤ n) :
    Agree m f g := fun w hw => h w (hw.trans hmn)
 theorem Agree.refl (n : ℕ) (f : Series α) : Agree n f f := fun _ _ => rfl
 theorem Agree.symm {n : ℕ} {f g : Series α} (h : Agree n f g) : Agree n g f :=
  fun w hw => (h w hw).symm
 theorem Agree.trans {n : ℕ} {f g h : Series α} (hfg : Agree n f g) (hgh : Agree n g h) :
    Agree n f h := fun w hw => (hfg w hw).trans (hgh w hw)
 theorem agree_add {n : ℕ} {f f' g g' : Series α} (hf : Agree n f f') (hg : Agree n g g') :
    Agree n (f+g) (f'+g') := fun w hw => by simp only [Pi.add_apply, hf w hw, hg w hw]
 theorem agree_deriv {n : ℕ} {f g : Series α} (h : Agree (n+1) f g) (a : α) :
    Agree n (deriv a f) (deriv a g) := fun w hw => h (a::w) (by simp; omega)

 theorem subst_agree {n : ℕ} {M M' f g : Series α} (hM : Agree n M M') (hf : Agree n f g) :
    Agree n (subst M f) (subst M' g) := by
  induction n generalizing M M' f g with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    simpa using hf [] (by simp)
  | succ n ih =>
    intro w hw
    cases w with
    | nil => simpa using hf [] (by simp)
    | cons a w =>
      simp only [subst_cons]
      exact conv_agree (hM.mono (by omega))
        (ih (hM.mono (by omega)) (agree_deriv hf a)) w (by simp at hw; omega)

 theorem subst_agree_left_step {n : ℕ} {M M' : Series α} (hM : Agree n M M') (f : Series α) :
    Agree (n+1) (subst M f) (subst M' f) := by
  intro w hw
  cases w with
  | nil => simp
  | cons a w =>
    simp only [subst_cons]
    exact conv_agree hM (subst_agree hM (Agree.refl _ _)) w (by simp at hw; omega)

 theorem conv_left_cancel {M f g : Series α} (hM : M [] = 1)
    (h : conv M f = conv M g) : f = g := by
  funext w
  induction w using length_induction with
  | h w ih =>
    cases w with
    | nil => simpa [hM] using congrFun h []
    | cons a w =>
      have ht := congrFun h (a::w)
      simp only [conv_cons, hM, one_mul] at ht
      have hsmall : conv (deriv a M) f w = conv (deriv a M) g w := by
        apply conv_agree (Agree.refl w.length _) (fun v hv => ih v (by simp; omega)) w le_rfl
      rw [hsmall] at ht
      exact add_right_cancel ht

 theorem subst_injective {M : Series α} (hM : M [] = 1) : Function.Injective (subst M) := by
  intro f g h
  funext w
  induction w generalizing f g with
  | nil => simpa using congrFun h []
  | cons a w ih =>
    apply ih
    apply conv_left_cancel hM
    change conv M (subst M (deriv a f)) = conv M (subst M (deriv a g))
    rw [← deriv_subst, ← deriv_subst, h]

 theorem inverse_cons (f : Series α) (a : α) (w : List α) :
    inverse f (a::w) = -conv (deriv a f) (inverse f) w := by
  rw [inverse, conv_sum_splits]
  rfl
 theorem conv_inverse {f : Series α} (hf : f [] = 1) : conv f (inverse f) = unit := by
  funext w
  cases w with
  | nil => simp [hf]
  | cons a w => simp [inverse_cons, hf]
 theorem inverse_conv {f : Series α} (hf : f [] = 1) : conv (inverse f) f = unit := by
  apply conv_left_cancel hf
  rw [← conv_assoc, conv_inverse hf, conv_unit_left, conv_unit_right]
 theorem inverse_unique {f g : Series α} (hf : f [] = 1) (hg : conv f g = unit) :
    g = inverse f := conv_left_cancel hf (hg.trans (conv_inverse hf).symm)
 theorem momentIter_step {R : Series α} (hR : R [] = 0) (n : ℕ) :
    Agree n (momentIter R (n+1)) (momentIter R n) := by
  induction n with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    simp [momentIter, hR]
  | succ n ih =>
    exact agree_add (Agree.refl _ _) (subst_agree_left_step ih R)
 theorem momentIter_stable {R : Series α} (hR : R [] = 0) {n m : ℕ} (hnm : n ≤ m) :
    Agree n (momentIter R m) (momentIter R n) := by
  induction m, hnm using Nat.le_induction with
  | base => exact Agree.refl _ _
  | succ m hnm ih => exact ((momentIter_step hR m).mono hnm).trans ih

 theorem moments_agree {R : Series α} (hR : R [] = 0) (n : ℕ) :
    Agree n (moments R) (momentIter R n) := by
  intro w hw
  exact ((momentIter_stable hR hw) w le_rfl).symm
 theorem moments_eq {R : Series α} (hR : R [] = 0) : moments R = unit + subst (moments R) R := by
  funext w
  have h := (moments_agree hR (w.length+1)) w (by omega)
  rw [h, momentIter]
  apply congrArg (fun z : ℂ => unit w + z)
  exact ((subst_agree_left_step (moments_agree hR w.length) R) w (by omega)).symm
 theorem moments_unique {R M : Series α} (hR : R [] = 0)
    (hM : M = unit + subst M R) : M = moments R := by
  have hn (n : ℕ) : Agree n M (momentIter R n) := by
    induction n with
    | zero =>
      intro w hw
      have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
      subst w
      have h := congrFun hM []
      simpa [momentIter, hR] using h
    | succ n ih =>
      rw [hM]
      exact agree_add (Agree.refl _ _) (subst_agree_left_step ih R)
  funext w
  exact hn w.length w le_rfl

 theorem cumulants_equation {M : Series α} (hM : M [] = 1) :
    M = unit + subst M (cumulants M) := by
  let J := moments (-boolean M)
  have hB : (-boolean M) [] = 0 := by simp
  have hJ : J = unit - subst J (boolean M) := by
    simpa only [subst_neg, sub_eq_add_neg] using moments_eq hB
  have hJM : conv J (subst J M) = unit := by
    have hJI : J = subst J (inverse M) := by
      calc
        J = unit - subst J (boolean M) := hJ
        _ = subst J (inverse M) := by rw [boolean, subst_sub, subst_unit]; abel
    calc
      conv J (subst J M) = conv (subst J (inverse M)) (subst J M) :=
        congrArg (fun A => conv A (subst J M)) hJI
      _ = unit := by rw [← subst_mul, inverse_conv hM, subst_unit]
  have hsubst : subst J (subst M (cumulants M)) = inverse J - unit := by
    rw [subst_comp, hJM, subst_unit_left]
    rfl
  apply subst_injective (moments_nil _)
  rw [subst_add, subst_unit, hsubst]
  have hMI : subst J M = inverse J := inverse_unique (moments_nil _) hJM
  rw [hMI]
  abel

 theorem cumulants_unique {M R : Series α} (hM : M [] = 1)
    (h : M = unit + subst M R) : R = cumulants M := by
  apply subst_injective hM
  have he := cumulants_equation hM
  exact add_left_cancel (h.symm.trans he)

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1} [Fintype α]

 theorem degreeNorm_sq (f : Series α) (n : ℕ) :
    degreeNorm f n ^ 2 = ∑ w : List.Vector α n, ‖f w.val‖ ^ 2 := by
  exact EuclideanSpace.norm_sq_eq _
 theorem degreeVector_add (f g : Series α) (n : ℕ) :
    degreeVector (f+g) n = degreeVector f n + degreeVector g n := rfl
 theorem degreeVector_smul (c : ℂ) (f : Series α) (n : ℕ) :
    degreeVector (c • f) n = c • degreeVector f n := rfl
 theorem degreeNorm_add_le (f g : Series α) (n : ℕ) :
    degreeNorm (f+g) n ≤ degreeNorm f n + degreeNorm g n := by
  unfold degreeNorm
  rw [degreeVector_add]
  exact norm_add_le _ _
@[simp] theorem degreeNorm_smul (c : ℂ) (f : Series α) (n : ℕ) :
    degreeNorm (c • f) n = ‖c‖ * degreeNorm f n := by
  unfold degreeNorm
  rw [degreeVector_smul]
  exact norm_smul _ _
 theorem degreeNorm_congr {f g : Series α} (n : ℕ)
    (h : ∀ w, w.length = n → f w = g w) : degreeNorm f n = degreeNorm g n := by
  apply congrArg norm
  ext w : 1
  exact h w.val w.prop
 theorem degreeNorm_le_of_coeff {f g : Series α} {n : ℕ}
    (h : ∀ w, w.length = n → ‖f w‖ ≤ ‖g w‖) : degreeNorm f n ≤ degreeNorm g n := by
  apply (sq_le_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  rw [degreeNorm_sq, degreeNorm_sq]
  exact sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _) (h w.val w.prop) 2
 theorem degreeNorm_sum_le {ι : Type u3} (s : Finset ι) (f : ι → Series α) (n : ℕ) :
    degreeNorm (∑ i ∈ s, f i) n ≤ ∑ i ∈ s, degreeNorm (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (degreeNorm_add_le _ _ _).trans (add_le_add_right ih _)

 theorem degreeNorm_tensor (f g : Series α) (m n : ℕ) :
    degreeNorm (fun w => f (w.take m) * g (w.drop m)) (m+n) =
      degreeNorm f m * degreeNorm g n := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (mul_nonneg (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _))).mp
  rw [mul_pow, degreeNorm_sq, degreeNorm_sq, degreeNorm_sq]
  have h := (vectorSplit (α := α) m n).sum_comp
    (fun v : List.Vector α m × List.Vector α n => ‖f v.1.val‖ ^ 2 * ‖g v.2.val‖ ^ 2)
  calc
    _ = ∑ v : List.Vector α (m+n), ‖f (v.val.take m)‖^2 * ‖g (v.val.drop m)‖^2 := by
      simp only [norm_mul, mul_pow]
    _ = ∑ v : List.Vector α m × List.Vector α n, ‖f v.1.val‖^2 * ‖g v.2.val‖^2 := h
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

 theorem degreeNorm_conv_le (f g : Series α) (n : ℕ) :
    degreeNorm (conv f g) n ≤ ∑ k ∈ range (n+1), degreeNorm f k * degreeNorm g (n-k) := by
  have h : degreeNorm (conv f g) n =
      degreeNorm (∑ k ∈ range (n+1), fun w => f (w.take k) * g (w.drop k)) n := by
    apply degreeNorm_congr
    intro w hw
    simp only [conv_sum_splits, hw, Finset.sum_apply]
  rw [h]
  apply (degreeNorm_sum_le _ _ _).trans
  apply sum_le_sum
  intro k hk
  have hn : k + (n-k) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk))
  simpa only [hn] using le_of_eq (degreeNorm_tensor f g k (n-k))

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.VectorSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem vdegreeNorm_sq {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (n : ℕ) :
    vdegreeNorm f n ^ 2 = ∑ w : List.Vector α n, ‖f w.val‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _
 theorem vdegreeNorm_congr {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : VSeries α E} (n : ℕ)
    (h : ∀ w, w.length = n → f w = g w) : vdegreeNorm f n = vdegreeNorm g n := by
  apply congrArg norm
  ext w : 1
  exact h w.val w.prop
 theorem vdegreeNorm_zero_degree (f : VSeries α E) : vdegreeNorm f 0 = ‖f []‖ := by
  apply (sq_eq_sq₀ (vdegreeNorm_nonneg _ _) (norm_nonneg _)).mp
  rw [vdegreeNorm_sq]
  simp only [show ∀ w : List.Vector α 0, w.val = [] from fun w => List.length_eq_zero_iff.mp w.prop]
  simp
 theorem vdegreeNorm_add_le {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f g : VSeries α E) (n : ℕ) :
    vdegreeNorm (f+g) n ≤ vdegreeNorm f n + vdegreeNorm g n := by
  change ‖vdegreeVector f n + vdegreeVector g n‖ ≤ _
  exact norm_add_le _ _
 theorem vdegreeNorm_sum_le {ι : Type u1} (s : Finset ι) (f : ι → VSeries α E) (n : ℕ) :
    vdegreeNorm (∑ i ∈ s, f i) n ≤ ∑ i ∈ s, vdegreeNorm (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (vdegreeNorm_add_le _ _ _).trans (add_le_add_right ih _)
 theorem vdegreeNorm_tensor (f : Series α) (g : VSeries α E) (m n : ℕ) :
    vdegreeNorm (fun w => f (w.take m) • g (w.drop m)) (m+n) =
      degreeNorm f m * vdegreeNorm g n := by
  apply (sq_eq_sq₀ (vdegreeNorm_nonneg _ _) (mul_nonneg (degreeNorm_nonneg _ _) (vdegreeNorm_nonneg _ _))).mp
  rw [mul_pow, vdegreeNorm_sq, degreeNorm_sq, vdegreeNorm_sq]
  have h := (vectorSplit (α := α) m n).sum_comp
    (fun v : List.Vector α m × List.Vector α n => ‖f v.1.val‖ ^ 2 * ‖g v.2.val‖ ^ 2)
  calc
    _ = ∑ v : List.Vector α (m+n), ‖f (v.val.take m)‖^2 * ‖g (v.val.drop m)‖^2 := by
      simp only [norm_smul, mul_pow]
    _ = ∑ v : List.Vector α m × List.Vector α n, ‖f v.1.val‖^2 * ‖g v.2.val‖^2 := h
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

 theorem vdegreeNorm_conv_le (M : Series α) (f : VSeries α E) (n : ℕ) :
    vdegreeNorm (vconv M f) n ≤ ∑ k ∈ range (n+1), degreeNorm M k * vdegreeNorm f (n-k) := by
  have h : vdegreeNorm (vconv M f) n =
      vdegreeNorm (∑ k ∈ range (n+1), fun w => M (w.take k) • f (w.drop k)) n := by
    apply vdegreeNorm_congr
    intro w hw
    simp only [vconv, hw, Finset.sum_apply]
  rw [h]
  apply (vdegreeNorm_sum_le _ _ _).trans
  apply sum_le_sum
  intro k hk
  have hn : k + (n-k) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk))
  simpa only [hn] using le_of_eq (vdegreeNorm_tensor M f k (n-k))

 theorem vsubst_cons {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Series α) (f : VSeries α E) (a : α) (w : List α) :
    vsubst M f (a::w) = vconv M (vsubst M (fun v => f (a::v))) w := by rw [vsubst, vconv]
 theorem vsubst_scalar (M f : Series α) : vsubst M f = subst M f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [vsubst, subst]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      rfl

 theorem vdegreeNorm_bundleDeriv (f : VSeries α E) (n : ℕ) :
    vdegreeNorm (bundleDeriv f) n = vdegreeNorm f (n+1) := by
  apply (sq_eq_sq₀ (vdegreeNorm_nonneg _ _) (vdegreeNorm_nonneg _ _)).mp
  rw [vdegreeNorm_sq, vdegreeNorm_sq]
  simp only [PiLp.norm_sq_eq_of_L2, bundleDeriv_apply]
  rw [sum_comm]
  calc
    _ = ∑ v : α × List.Vector α n, ‖f (v.1 :: v.2.val)‖ ^ 2 :=
      (Fintype.sum_prod_type (fun v : α × List.Vector α n => ‖f (v.1 :: v.2.val)‖ ^ 2)).symm
    _ = _ := (vectorCons n).sum_comp (fun w : List.Vector α (n+1) => ‖f w.val‖^2)

 theorem vsubst_apply (M : Series α) (f : VSeries α (PiLp 2 (fun _ : α => E)))
    (w : List α) (a : α) :
    vsubst M f w a = vsubst M (fun v => f v a) w := by
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [vsubst, vsubst]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
      apply sum_congr rfl
      intro k hk
      congr 1
      exact ih _ (by simp) _

 theorem vsubst_bundleDeriv (M : Series α) (f : VSeries α E) (w : List α) (a : α) :
    vsubst M (bundleDeriv f) w a = vsubst M (fun v => f (a::v)) w :=
  vsubst_apply M (bundleDeriv f) w a

 theorem vdegreeNorm_subst_succ (M : Series α) (f : VSeries α E) (n : ℕ) :
    vdegreeNorm (vsubst M f) (n+1) =
      vdegreeNorm (vconv M (vsubst M (bundleDeriv f))) n := by
  rw [← vdegreeNorm_bundleDeriv]
  apply vdegreeNorm_congr
  intro w hw
  ext a : 1
  simp only [bundleDeriv_apply, vsubst_cons, vconv, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    vsubst_bundleDeriv]

 theorem substBound_nonneg {b a : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (ha : ∀ k, 0 ≤ a k) (n : ℕ) :
    0 ≤ substBound b a n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases n with
    | zero => simpa only [substBound] using ha 0
    | succ n =>
      rw [substBound]
      exact sum_nonneg fun k hk => mul_nonneg (hb k) (ih (n-k) (by omega) (fun j => ha (j+1)))

 theorem vsubst_norm_le (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      (M : Series α) (f : VSeries α E),
      vdegreeNorm (vsubst M f) n ≤ substBound (degreeNorm M) (vdegreeNorm f) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ M f
    cases n with
    | zero => simp [vdegreeNorm_zero_degree, substBound]
    | succ n =>
      rw [vdegreeNorm_subst_succ, substBound]
      apply (vdegreeNorm_conv_le _ _ _).trans
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (degreeNorm_nonneg _ _)
      have h := ih (n-k) (by omega) M (bundleDeriv f)
      have he : vdegreeNorm (bundleDeriv f) = fun j => vdegreeNorm f (j+1) :=
        funext (vdegreeNorm_bundleDeriv f)
      rw [he] at h
      exact h

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset

 theorem truncEval_nonneg {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r) (N : ℕ) :
    0 ≤ truncEval a r N := sum_nonneg fun n _ => mul_nonneg (pow_nonneg hr _) (ha n)
 theorem truncEval_mono {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r)
    {N K : ℕ} (hNK : N ≤ K) : truncEval a r N ≤ truncEval a r K := by
  apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
  intro n _ _
  exact mul_nonneg (pow_nonneg hr _) (ha n)
 theorem truncEval_le {a b : ℕ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hab : ∀ n, a n ≤ b n) (N : ℕ) : truncEval a r N ≤ truncEval b r N :=
  sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hab n) (pow_nonneg hr n)
 theorem truncEval_succ_shift (a : ℕ → ℝ) (r : ℝ) (N : ℕ) :
    truncEval a r (N+1) = a 0 + r * truncEval (fun n => a (n+1)) r N := by
  unfold truncEval
  rw [sum_range_succ']
  simp only [pow_zero, one_mul, mul_sum, pow_succ]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro n _
  ring

 theorem triangle_le_rectangle (f : ℕ → ℕ → ℝ) (hf : ∀ i j, 0 ≤ f i j) (N : ℕ) :
    (∑ n ∈ range (N+1), ∑ k ∈ range (n+1), f k (n-k)) ≤
      ∑ k ∈ range (N+1), ∑ j ∈ range (N+1), f k j := by
  let s := (range (N+1) ×ˢ range (N+1)).filter (fun v : ℕ × ℕ => v.1+v.2 ≤ N)
  rw [sum_sigma']
  calc
    _ = ∑ v ∈ s, f v.1 v.2 := by
      apply sum_bij (fun x _ => (x.2, x.1-x.2))
      · intro x hx
        obtain ⟨hx1,hx2⟩ := mem_sigma.mp hx
        simp only [mem_range] at hx1 hx2
        simp only [s, mem_filter, mem_product, mem_range]
        omega
      · intro x hx y hy he
        obtain ⟨hx1,hx2⟩ := mem_sigma.mp hx
        obtain ⟨hy1,hy2⟩ := mem_sigma.mp hy
        simp only [mem_range] at hx1 hx2 hy1 hy2
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        rcases x with ⟨xn,xk⟩
        rcases y with ⟨yn,yk⟩
        dsimp at h1 h2 hx1 hx2 hy1 hy2
        have hxy : xn = yn := by omega
        subst yn
        subst yk
        rfl
      · intro y hy
        simp only [s, mem_filter, mem_product, mem_range] at hy
        refine ⟨⟨y.1+y.2,y.1⟩, ?_, ?_⟩
        · simp only [mem_sigma, mem_range]; omega
        · apply Prod.ext <;> simp
      · intro x hx; rfl
    _ ≤ ∑ v ∈ range (N+1) ×ˢ range (N+1), f v.1 v.2 := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _ => hf v.1 v.2)
    _ = _ := sum_product _ _ _

 theorem truncEval_conv_le {a b : ℕ → ℝ} {r : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hr : 0 ≤ r) (N : ℕ) :
    truncEval (scalarConv a b) r N ≤ truncEval a r N * truncEval b r N := by
  unfold truncEval
  rw [sum_mul_sum]
  calc
    _ = ∑ n ∈ range (N+1), ∑ k ∈ range (n+1), (r^k*a k)*(r^(n-k)*b (n-k)) := by
      apply sum_congr rfl
      intro n hn
      rw [scalarConv, mul_sum]
      apply sum_congr rfl
      intro k hk
      have hkn : k+(n-k)=n := Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk))
      have hp : r^n = r^k*r^(n-k) := by rw [← pow_add, hkn]
      rw [hp]; ring
    _ ≤ _ := by
      exact triangle_le_rectangle (fun k j => (r^k*a k)*(r^j*b j))
        (fun k j => mul_nonneg (mul_nonneg (pow_nonneg hr _) (ha k))
          (mul_nonneg (pow_nonneg hr _) (hb j))) N

 theorem substBound_trunc_le {b a : ℕ → ℝ} {r B : ℝ}
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r)
    (N : ℕ) (hB : truncEval b r N ≤ B) :
    truncEval (substBound b a) r N ≤ ∑ k ∈ range (N+1), a k * (r*B)^k := by
  have hB0 : 0 ≤ B := (truncEval_nonneg hb hr N).trans hB
  induction N generalizing a with
  | zero => simp [substBound]
  | succ N ih =>
    have hBN : truncEval b r N ≤ B := (truncEval_mono hb hr (by omega)).trans hB
    have ha' : ∀ n, 0 ≤ a (n+1) := fun n => ha (n+1)
    have hi := ih ha' hBN
    have ht : (fun n => substBound b a (n+1)) = scalarConv b (substBound b (fun n => a (n+1))) := by
      funext n
      rw [substBound, scalarConv]
    rw [truncEval_succ_shift, show substBound b a 0 = a 0 by rw [substBound], ht]
    calc
      _ ≤ a 0 + r * (truncEval b r N * truncEval (substBound b (fun n => a (n+1))) r N) := by
        gcongr
        exact truncEval_conv_le hb (substBound_nonneg hb ha') hr N
      _ ≤ a 0 + r * (B * ∑ k ∈ range (N+1), a (k+1) * (r*B)^k) := by
        apply add_le_add_right (mul_le_mul_of_nonneg_left _ hr)
        exact mul_le_mul hBN hi (truncEval_nonneg (substBound_nonneg hb ha') hr N) hB0
      _ = _ := by
        conv_rhs => rw [sum_range_succ']
        simp only [pow_zero, mul_one, pow_succ, mul_sum]
        rw [add_comm]
        congr 1
        apply sum_congr rfl
        intro k hk
        ring

variable {α : Type} [Fintype α]
 theorem seriesWeight_nonneg (f : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    0 ≤ seriesWeight f r N := truncEval_nonneg (degreeNorm_nonneg f) hr N
 theorem seriesWeight_conv_le (f g : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (conv f g) r N ≤ seriesWeight f r N * seriesWeight g r N := by
  apply (truncEval_le hr (degreeNorm_conv_le f g) N).trans
  exact truncEval_conv_le (degreeNorm_nonneg f) (degreeNorm_nonneg g) hr N
 theorem seriesWeight_subst_le (M f : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (subst M f) r N ≤
      ∑ k ∈ range (N+1), degreeNorm f k * (r * seriesWeight M r N)^k := by
  apply (truncEval_le hr (fun k => ?_) N).trans
  · exact substBound_trunc_le (degreeNorm_nonneg M) (degreeNorm_nonneg f) hr N le_rfl
  · have h := vsubst_norm_le k M f
    change degreeNorm (vsubst M f) k ≤ substBound (degreeNorm M) (degreeNorm f) k at h
    rw [vsubst_scalar] at h
    exact h

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [Fintype α]

@[simp] theorem degreeNorm_nil (f : Series α) : degreeNorm f 0 = ‖f []‖ :=
  vdegreeNorm_zero_degree f
@[simp] theorem degreeNorm_unit_pos {n : ℕ} (hn : 0 < n) : degreeNorm (unit : Series α) n = 0 := by
  apply (degreeNorm_congr (g := 0) n ?_).trans (degreeNorm_zero n)
  intro w hw
  cases w with
  | nil => simp at hw; omega
  | cons a w => rfl
 theorem degreeNorm_sub_unit_pos (f : Series α) {n : ℕ} (hn : 0 < n) :
    degreeNorm (f-unit) n = degreeNorm f n := by
  apply degreeNorm_congr
  intro w hw
  cases w with
  | nil => simp at hw; omega
  | cons a w => simp
 theorem seriesWeight_add_le (f g : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (f+g) r N ≤ seriesWeight f r N + seriesWeight g r N := by
  unfold seriesWeight truncEval
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (degreeNorm_add_le f g k) (pow_nonneg hr k)
 theorem seriesWeight_agree {f g : Series α} {N : ℕ} (h : Agree N f g) (r : ℝ) :
    seriesWeight f r N = seriesWeight g r N := by
  unfold seriesWeight truncEval
  apply sum_congr rfl
  intro k hk
  congr 1
  exact degreeNorm_congr k (fun w hw => h w (by simp only [mem_range] at hk; omega))
 theorem seriesWeight_split {f : Series α} (hf : f [] = 1) (r : ℝ) (N : ℕ) :
    seriesWeight f r N = 1 + seriesWeight (f-unit) r N := by
  unfold seriesWeight truncEval
  rw [sum_range_succ', sum_range_succ']
  simp only [degreeNorm_nil, hf, norm_one, pow_zero, one_mul, Pi.sub_apply, unit_nil, sub_self, norm_zero, add_zero]
  simp only [degreeNorm_sub_unit_pos f (Nat.zero_lt_succ _)]
  ring
@[simp] theorem seriesWeight_unit (r : ℝ) (N : ℕ) : seriesWeight (unit : Series α) r N = 1 := by
  unfold seriesWeight truncEval
  rw [sum_range_succ']
  simp
 theorem inverse_tail_identity {α : Type} [Fintype α] {M : Series α} (hM : M [] = 1) :
    inverse M - unit = -(M-unit) - conv (M-unit) (inverse M-unit) := by
  rw [conv_sub_left, conv_sub_right, conv_sub_right, conv_inverse hM, conv_unit_left,
    conv_unit_right, conv_unit_left]
  abel
 theorem inverse_tail_weight {M : Series α} (hM : M [] = 1) {r a : ℝ} (hr : 0 ≤ r)
    (_ha : 0 ≤ a) (ha1 : a < 1) (N : ℕ) (h : seriesWeight (M-unit) r N ≤ a) :
    seriesWeight (inverse M-unit) r N ≤ a/(1-a) := by
  have hb := seriesWeight_nonneg (inverse M-unit) hr N
  have hie : seriesWeight (inverse M-unit) r N ≤
      seriesWeight (M-unit) r N + seriesWeight (M-unit) r N * seriesWeight (inverse M-unit) r N := by
    conv_lhs => rw [inverse_tail_identity hM]
    calc
      _ ≤ seriesWeight (-(M-unit)) r N + seriesWeight (-conv (M-unit) (inverse M-unit)) r N :=
        seriesWeight_add_le _ _ hr N
      _ ≤ _ := by simpa only [seriesWeight_neg] using
        add_le_add le_rfl (seriesWeight_conv_le (M-unit) (inverse M-unit) hr N)
  apply (le_div_iff₀ (by linarith : 0 < 1-a)).mpr
  have hh := mul_le_mul_of_nonneg_right h hb
  nlinarith
 theorem seriesWeight_coeff_le (f : Series α) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    r^n * degreeNorm f n ≤ seriesWeight f r n := by
  exact single_le_sum (fun k _ => mul_nonneg (pow_nonneg hr k) (degreeNorm_nonneg f k))
    (mem_range.mpr (by omega))
 theorem degreeNorm_le_of_weight {f : Series α} {r : ℝ} (hr : 0 < r)
    (h : ∀ N, seriesWeight f r N ≤ 1) (n : ℕ) : degreeNorm f n ≤ (r⁻¹)^n := by
  have hn := (seriesWeight_coeff_le f hr.le n).trans (h n)
  rw [inv_pow, ← one_div]
  apply (le_div_iff₀ (pow_pos hr n)).mpr
  simpa only [mul_comm] using hn

 theorem seriesWeight_mono_radius (f : Series α) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (N : ℕ) :
    seriesWeight f r N ≤ seriesWeight f s N := by
  unfold seriesWeight truncEval
  apply sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrs k) (degreeNorm_nonneg f k)
 theorem geom_tail_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ k ∈ range (N+1), q^k) - 1 ≤ q/(1-q) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
  have he := geom_sum_mul_neg q (N+1)
  have hp := pow_nonneg hq (N+1)
  nlinarith
 theorem weight_le_geom {f : Series α} (hf : f [] = 0) {A r : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hq : r*A < 1)
    (hb : ∀ n, 0 < n → degreeNorm f n ≤ A^n) (N : ℕ) :
    seriesWeight f r N ≤ (r*A)/(1-r*A) := by
  apply le_trans (b := (∑ k ∈ range (N+1), (r*A)^k) - 1) ?_
    (geom_tail_le (mul_nonneg hr hA) hq N)
  unfold seriesWeight truncEval
  rw [sum_range_succ', sum_range_succ']
  simp only [degreeNorm_nil, hf, norm_zero, pow_zero, mul_zero, add_zero]
  rw [add_sub_cancel_right]
  apply sum_le_sum
  intro k hk
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (hb (k+1) (by omega)) (pow_nonneg hr _)
 theorem subst_weight_le (M f : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (subst M f) r N ≤ seriesWeight f (r*seriesWeight M r N) N := by
  apply (seriesWeight_subst_le M f hr N).trans_eq
  exact sum_congr rfl (fun k _ => mul_comm _ _)
 theorem moments_tail_weight {R : Series α} (hR : R [] = 0) {r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (h : ∀ N, seriesWeight R (2*r) N ≤ a) (N : ℕ) :
    seriesWeight (moments R-unit) r N ≤ a := by
  have hi (j : ℕ) (K : ℕ) : seriesWeight (momentIter R j-unit) r K ≤ a := by
    induction j with
    | zero => simpa [momentIter, seriesWeight, truncEval] using ha
    | succ j ih =>
      have hM : seriesWeight (momentIter R j) r K ≤ 2 := by
        rw [seriesWeight_split (momentIter_nil hR j)]
        linarith
      have ht : momentIter R (j+1)-unit = subst (momentIter R j) R := by
        rw [momentIter]; abel
      rw [ht]
      apply (subst_weight_le _ _ hr K).trans
      apply (seriesWeight_mono_radius R
        (mul_nonneg hr (seriesWeight_nonneg _ hr _))
        (by nlinarith : r*seriesWeight (momentIter R j) r K ≤ 2*r) K).trans
      exact h K
  apply le_of_eq_of_le (b := seriesWeight (momentIter R N-unit) r N) ?_ (hi N N)
  exact seriesWeight_agree (fun w hw => by simp only [Pi.sub_apply, moments_agree hR N w hw]) r

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SemicircularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α]

 theorem deriv_letter (i j : α) : deriv j (letter i) = if j=i then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : j=i <;> simp [deriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : j=i <;> simp [deriv, letter, unit, h]
 theorem subst_letter_cons (M : Series α) (i j : α) (w : List α) :
    subst M (letter i) (j::w) = if j=i then M w else 0 := by
  rw [subst_cons, deriv_letter]
  split_ifs <;> simp
 theorem deriv_quadratic (i : α) : deriv i (quadratic : Series α) = letter i := by
  funext w
  cases w with
  | nil => rfl
  | cons a w => cases w <;> rfl

 theorem quadratic_subst_derivative {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    subst M quadratic (i::w) = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [subst_cons, deriv_quadratic, conv_sum_splits, sum_range_succ]
  simp only [List.take_length, List.drop_length, subst_nil, letter_nil, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => M (w.take k) * subst M (letter i) (w.drop k))]
  apply sum_congr rfl
  intro k hk
  rw [List.drop_eq_getElem_cons k.isLt, subst_letter_cons]
  split_ifs <;> simp

 theorem fockMoments_eq (p : ℕ) : fockMoments p = unit + subst (fockMoments p) quadratic := by
  funext w
  cases w with
  | nil => simp [fockMoments]
  | cons i w =>
    simp only [Pi.add_apply, unit_cons, zero_add, quadratic_subst_derivative]
    exact Fock.semicircular_integration_by_parts i w
 theorem fockMoments_moments (p : ℕ) : fockMoments p = moments quadratic :=
    moments_unique quadratic_nil (fockMoments_eq p)

variable [Fintype α]
 theorem degreeNorm_succ_sq {α : Type} [DecidableEq α] [Fintype α] (f : Series α) (n : ℕ) :
    degreeNorm f (n+1)^2 = ∑ a : α, degreeNorm (deriv a f) n ^ 2 := by
  rw [degreeNorm_sq]
  have he := (vectorCons (α := α) n).sum_comp
    (fun w : List.Vector α (n+1) => ‖f w.val‖^2)
  rw [← he, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a ha
  exact (degreeNorm_sq (deriv a f) n).symm
 theorem degreeNorm_letter_one (i : α) : degreeNorm (letter i) 1 = 1 := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (by norm_num : (0:ℝ) ≤ 1)).mp
  rw [degreeNorm_succ_sq]
  simp only [deriv_letter, degreeNorm_nil, ite_apply, unit_nil, Pi.zero_apply]
  calc
    _ = ∑ a : α, if a=i then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro a ha
      split_ifs <;> norm_num
    _ = _ := by simp
 theorem degreeNorm_quadratic_sq : degreeNorm (quadratic : Series α) 2 ^ 2 = Fintype.card α := by
  rw [degreeNorm_succ_sq]
  simp [deriv_quadratic, degreeNorm_letter_one]
 theorem degreeNorm_quadratic_other {n : ℕ} (hn : n ≠ 2) :
    degreeNorm (quadratic : Series α) n = 0 := by
  apply (degreeNorm_congr (g := 0) n ?_).trans (degreeNorm_zero n)
  intro w hw
  cases w with
  | nil => rfl
  | cons a w =>
    cases w with
    | nil => rfl
    | cons b w =>
      cases w with
      | nil => simp at hw; omega
      | cons c w => rfl
 theorem degreeNorm_quadratic : degreeNorm (quadratic : Series α) 2 = Real.sqrt (Fintype.card α) := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (Real.sqrt_nonneg _)).mp
  rw [degreeNorm_quadratic_sq, Real.sq_sqrt (by positivity)]
 theorem quadratic_weight_le {r : ℝ} (_hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (quadratic : Series α) r N ≤ r^2 * Real.sqrt (Fintype.card α) := by
  unfold seriesWeight truncEval
  calc
    _ = ∑ k ∈ range (N+1), if k=2 then r^2 * Real.sqrt (Fintype.card α) else 0 := by
      apply sum_congr rfl
      intro k hk
      by_cases h : k = 2
      · subst k; simp [degreeNorm_quadratic]
      · simp [h, degreeNorm_quadratic_other h]
    _ ≤ _ := by simp only [sum_ite_eq']; split_ifs <;> first | exact le_rfl | positivity

 theorem fockMoments_norm_le {p : ℕ} (hp : 0 < p) (n : ℕ) :
    degreeNorm (fockMoments p) n ≤ (2 * Real.sqrt (Real.sqrt p))^n := by
  let q := Real.sqrt (Real.sqrt p)
  have hq : 0 < q := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hp))
  have hq2 : q^2 = Real.sqrt p := Real.sq_sqrt (Real.sqrt_nonneg _)
  let r := (2*q)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hw (N : ℕ) : seriesWeight (quadratic : Series (Fin p)) (2*r) N ≤ 1 := by
    apply (quadratic_weight_le (by positivity) N).trans
    simp only [Fintype.card_fin]
    rw [← hq2]
    dsimp [r]
    field_simp
    norm_num
  have hm (N : ℕ) : seriesWeight (moments (quadratic : Series (Fin p))-unit) r N ≤ 1 :=
    moments_tail_weight quadratic_nil hr.le (by norm_num) le_rfl hw N
  cases n with
  | zero => simp [fockMoments]
  | succ n =>
    rw [fockMoments_moments]
    have hh := degreeNorm_le_of_weight hr hm (n+1)
    rw [degreeNorm_sub_unit_pos _ (by omega)] at hh
    simpa [r, q] using hh

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CyclicSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

 theorem rightDeriv_conv {α : Type} [DecidableEq α] [Fintype α] (i : α) (f g : Series α) :
    rightDeriv i (conv f g) = conv f (rightDeriv i g) + g [] • rightDeriv i f := by
  funext w
  induction w generalizing f with
  | nil => simp [rightDeriv, deriv, conv]; ring
  | cons a w ih =>
    change f [] * g ((a::w)++[i]) + conv (deriv a f) g (w++[i]) =
      (f [] * g ((a::w)++[i]) + conv (deriv a f) (rightDeriv i g) w) +
      g [] * f ((a::w)++[i])
    have h := ih (deriv a f)
    change conv (deriv a f) g (w++[i]) = _ at h
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rightDeriv_apply, deriv_apply, List.cons_append]
    ring
 theorem rightDeriv_sub {α : Type} [DecidableEq α] [Fintype α] (i : α) (f g : Series α) :
    rightDeriv i (f-g) = rightDeriv i f - rightDeriv i g := rfl
 theorem rightDeriv_smul {α : Type} [DecidableEq α] [Fintype α] (i : α) (c : ℂ) (f : Series α) :
    rightDeriv i (c • f) = c • rightDeriv i f := rfl
 theorem rightDeriv_sum {α : Type} [DecidableEq α] [Fintype α] {β : Type u1} (s : Finset β) (f : β → Series α) (i : α) :
    rightDeriv i (∑ b ∈ s, f b) = ∑ b ∈ s, rightDeriv i (f b) := by
  funext w
  simp [rightDeriv]
 theorem rightDeriv_letter {α : Type} [DecidableEq α] [Fintype α] (i j : α) : rightDeriv i (letter j) = if i=j then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : i=j <;> simp [rightDeriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : i=j <;> simp [rightDeriv, letter, unit, h]
 theorem series_ext_right {α : Type} [DecidableEq α] [Fintype α] {f g : Series α} (hn : f [] = g [])
    (h : ∀ i, rightDeriv i f = rightDeriv i g) : f = g := by
  funext w
  induction w using List.reverseRecOn with
  | nil => exact hn
  | append_singleton w i _ => exact congrFun (h i) w

 theorem rightDeriv_assemble (f : α → Series α) (j : α) :
    rightDeriv j (rightAssemble f) = f j := by
  rw [rightAssemble, rightDeriv_sum]
  simp only [rightDeriv_conv, rightDeriv_letter, letter_nil, zero_smul, add_zero]
  have hh (i : α) : conv (f i) (if j=i then unit else 0) = if j=i then f i else 0 := by
    split_ifs <;> simp
  simp_rw [hh]
  simp
 theorem assemble_rightDeriv (f : Series α) :
    rightAssemble (fun i => rightDeriv i f) = f - f [] • unit := by
  apply series_ext_right
  · simp
  · intro i
    simp [rightDeriv_assemble, rightDeriv_sub, rightDeriv_smul]
 theorem Cyclic.assemble {f : Series α} (hf : Cyclic f) :
    rightAssemble (fun i => deriv i f) = f - f [] • unit := by
  have hh : (fun i => deriv i f) = (fun i => rightDeriv i f) := funext hf
  rw [hh, assemble_rightDeriv]
 theorem cyclic_of_assemble {f : Series α} (h : rightAssemble (fun i => deriv i f) = f - f [] • unit) :
    Cyclic f := by
  intro i
  have hh := congrArg (rightDeriv i) h
  simpa [rightDeriv_assemble, rightDeriv_sub, rightDeriv_smul] using hh

 theorem conv_sum_left {α : Type} [DecidableEq α] [Fintype α] {β : Type u2} (s : Finset β) (f : β → Series α) (g : Series α) :
    conv (∑ b ∈ s, f b) g = ∑ b ∈ s, conv (f b) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, conv_add_left, ih]
 theorem conv_sum_right {α : Type} [DecidableEq α] [Fintype α] {β : Type u3} (s : Finset β) (f : Series α) (g : β → Series α) :
    conv f (∑ b ∈ s, g b) = ∑ b ∈ s, conv f (g b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, conv_add_right, ih]
 theorem subst_sum {α : Type} [DecidableEq α] [Fintype α] {β : Type u4} (s : Finset β) (M : Series α) (f : β → Series α) :
    subst M (∑ b ∈ s, f b) = ∑ b ∈ s, subst M (f b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, subst_add, ih]
 theorem subst_letter {α : Type} [DecidableEq α] [Fintype α] (M : Series α) (i : α) : subst M (letter i) = conv (letter i) M := by
  funext w
  cases w with
  | nil => simp
  | cons j w => simp only [subst_letter_cons, conv_cons, letter_nil, zero_mul, zero_add,
      deriv_letter]; split_ifs <;> simp
 theorem subst_rightAssemble (M : Series α) (f : α → Series α) :
    subst M (rightAssemble f) = conv (rightAssemble (fun i => subst M (f i))) M := by
  simp only [rightAssemble, subst_sum, conv_sum_left, subst_mul, subst_letter, conv_assoc]

 theorem cyclic_cumulants {M : Series α} (hM : M [] = 1) (hc : Cyclic M) :
    Cyclic (cumulants M) := by
  let R := cumulants M
  have he : M = unit + subst M R := cumulants_equation hM
  have hd (i : α) : deriv i M = conv M (subst M (deriv i R)) := by
    funext w
    have h := congrFun he (i::w)
    simpa [subst_cons] using h
  have hi (i : α) : rightDeriv i (inverse M) = -subst M (deriv i R) := by
    have hh := congrArg (rightDeriv i) (inverse_conv hM)
    rw [rightDeriv_conv, rightDeriv_unit, hM, one_smul, ← hc i, hd i,
      ← conv_assoc, inverse_conv hM, conv_unit_left] at hh
    exact eq_neg_of_add_eq_zero_right hh
  have hinv : rightAssemble (fun i => subst M (deriv i R)) = unit - inverse M := by
    apply series_ext_right
    · simp
    · intro i
      simp [rightDeriv_assemble, rightDeriv_sub, hi]
  apply cyclic_of_assemble
  simp only [cumulants_nil, zero_smul, sub_zero]
  apply subst_injective hM
  rw [subst_rightAssemble, hinv, conv_sub_left, conv_unit_left, inverse_conv hM]
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he.symm)).symm

 theorem cyclic_moments {R : Series α} (hR : R [] = 0) (hc : Cyclic R) :
    Cyclic (moments R) := by
  let M := moments R
  have hM : M [] = 1 := moments_nil R
  have he : M = unit + subst M R := moments_eq hR
  let A := rightAssemble (fun i => subst M (deriv i R))
  have hr : subst M R = conv A M := by
    have h := hc.assemble
    rw [hR, zero_smul, sub_zero] at h
    rw [← h, subst_rightAssemble]
  have ha : unit - A = inverse M := by
    have hp : conv (unit - A) M = unit := by
      rw [conv_sub_left, conv_unit_left]
      rw [hr] at he
      exact sub_eq_iff_eq_add.mpr he
    calc
      unit - A = conv (unit - A) (conv M (inverse M)) := by rw [conv_inverse hM, conv_unit_right]
      _ = inverse M := by rw [← conv_assoc, hp, conv_unit_left]
  intro i
  have hi : rightDeriv i (inverse M) = -subst M (deriv i R) := by
    rw [← ha, rightDeriv_sub, rightDeriv_unit, sub_eq_add_neg, zero_add]
    change -rightDeriv i (rightAssemble _) = _
    rw [rightDeriv_assemble]
  have hh := congrArg (rightDeriv i) (conv_inverse hM)
  rw [rightDeriv_conv, rightDeriv_unit, inverse_nil, one_smul, hi, conv_neg_right] at hh
  have hh' : rightDeriv i M = conv M (subst M (deriv i R)) := by
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; simpa [add_comm] using hh)
  rw [hh']
  funext w
  have h := congrFun he (i::w)
  simpa [subst_cons] using h

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.LinearSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

 theorem reparam_cons {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) (w : List β) :
    reparam c f (b::w) = ∑ a, c a b * reparam c (deriv a f) w := rfl
 theorem deriv_reparam {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) :
    deriv b (reparam c f) = ∑ a, c a b • reparam c (deriv a f) := by
  funext w; simp [deriv_apply, reparam_cons]
 theorem reparam_add {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f g : Series α) :
    reparam c (f+g) = reparam c f + reparam c g := by
  funext w
  induction w generalizing f g with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, Pi.add_apply,
      show ∀ a, deriv a (f+g) = deriv a f + deriv a g from fun _ => rfl, ih]
    simp [mul_add, sum_add_distrib]
 theorem reparam_smul {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (z : ℂ) (f : Series α) :
    reparam c (z • f) = z • reparam c f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, Pi.smul_apply, smul_eq_mul,
      show ∀ a, deriv a (z • f) = z • deriv a f from fun _ => rfl, ih]
    simp [mul_left_comm, mul_sum]
@[simp] theorem reparam_zero (c : α → β → ℂ) : reparam c 0 = 0 := by
  simpa using reparam_smul c 0 0
 theorem reparam_sum {δ : Type u1} (s : Finset δ) (c : α → β → ℂ) (f : δ → Series α) :
    reparam c (∑ d ∈ s, f d) = ∑ d ∈ s, reparam c (f d) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert d s hd ih => simp [sum_insert hd, reparam_add, ih]
@[simp] theorem reparam_unit (c : α → β → ℂ) : reparam c unit = unit := by
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    have hh (a : α) : deriv a (unit : Series α) = 0 := rfl
    simp [reparam_cons, hh]
 theorem reparam_conv (c : α → β → ℂ) (f g : Series α) :
    reparam c (conv f g) = conv (reparam c f) (reparam c g) := by
  funext w
  induction w generalizing f g with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, deriv_conv, reparam_add, reparam_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, ih, mul_add, sum_add_distrib]
    rw [conv_cons, reparam_nil, reparam_cons, deriv_reparam, conv_sum_left]
    simp only [conv_smul_left, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp [mul_left_comm, mul_sum]
 theorem rightDeriv_reparam {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) :
    rightDeriv b (reparam c f) = ∑ a, c a b • reparam c (rightDeriv a f) := by
  funext w
  induction w generalizing f with
  | nil => simp [rightDeriv, reparam_cons]
  | cons d w ih =>
    simp only [rightDeriv_apply, List.cons_append, reparam_cons, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    have hh (a : α) : reparam c (deriv a f) (w++[b]) =
        ∑ j, c j b * reparam c (rightDeriv j (deriv a f)) w := by
      simpa only [rightDeriv_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ih (deriv a f)
    simp_rw [hh, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro j _
    have he : rightDeriv a (deriv j f) = deriv j (rightDeriv a f) := rfl
    rw [he]
    ring
 theorem Cyclic.reparam {f : Series α} (hf : Cyclic f) (c : α → β → ℂ) :
    Cyclic (reparam c f) := by
  intro b
  rw [deriv_reparam, rightDeriv_reparam]
  apply sum_congr rfl
  intro a _
  rw [hf a]
 theorem reparam_subst (c : α → β → ℂ) (M f : Series α) :
    reparam c (subst M f) = subst (reparam c M) (reparam c f) := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [reparam_cons, subst_cons, deriv_reparam, subst_sum, conv_sum_right]
      simp only [deriv_subst, reparam_conv, subst_smul, conv_smul_right,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply sum_congr rfl
      intro a _
      congr 1
      apply conv_agree (n := w.length) (Agree.refl _ _) (fun v hv => ?_) w le_rfl
      exact ih v (by simp; omega) (deriv a f)
 theorem reparam_moments (c : α → β → ℂ) {R : Series α} (hR : R [] = 0) :
    reparam c (moments R) = moments (reparam c R) := by
  apply moments_unique (by simpa using hR)
  have hh := congrArg (reparam c) (moments_eq hR)
  simpa only [reparam_add, reparam_unit, reparam_subst] using hh
 theorem restrict_conv {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (e : β → α) (f g : Series α) :
    restrict e (conv f g) = conv (restrict e f) (restrict e g) := by
  funext w
  simp only [restrict, conv_sum_splits, List.length_map, ← List.map_take, ← List.map_drop]
 theorem restrict_subst (e : β → α) (M f : Series α) :
    restrict e (subst M f) = subst (restrict e M) (restrict e f) := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp [restrict]
    | cons b w =>
      change subst M f (e b :: w.map e) = _
      rw [subst_cons, subst_cons]
      change restrict e (conv M (subst M (deriv (e b) f))) w = _
      rw [restrict_conv]
      apply conv_agree (n := w.length) (Agree.refl _ _) (fun v hv => ?_) w le_rfl
      exact ih v (by simp; omega) (deriv (e b) f)
 theorem restrict_moments (e : β → α) {R : Series α} (hR : R [] = 0) :
    restrict e (moments R) = moments (restrict e R) := by
  apply moments_unique (show (restrict e R) [] = 0 from hR)
  funext w
  have hh := congrFun (moments_eq hR) (w.map e)
  simp only [Pi.add_apply] at hh
  change moments R (w.map e) = _
  rw [hh]
  congr 1
  · cases w <;> rfl
  · exact congrFun (restrict_subst e _ _) w
end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EmbeddedSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

 theorem deriv_liftSeries (e : α → β) (f : Series α) (b : β) :
    deriv b (liftSeries e f) = ∑ a, (if e a=b then (1:ℂ) else 0) • liftSeries e (deriv a f) :=
  deriv_reparam _ _ _
 theorem deriv_liftSeries_image (e : α → β) (he : Function.Injective e) (f : Series α) (a : α) :
    deriv (e a) (liftSeries e f) = liftSeries e (deriv a f) := by
  rw [deriv_liftSeries]
  simp only [he.eq_iff, ite_smul, one_smul, zero_smul]
  simp
 theorem deriv_liftSeries_out (e : α → β) (f : Series α) (b : β)
    (hb : ∀ a, e a ≠ b) : deriv b (liftSeries e f) = 0 := by
  rw [deriv_liftSeries]
  simp [hb]
 theorem liftSeries_letter (e : α → β) (a : α) : liftSeries e (letter a) = letter (e a) := by
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    rw [liftSeries, reparam_cons]
    simp only [deriv_letter, apply_ite (reparam _), reparam_unit, reparam_zero]
    simp only [ite_apply, Pi.zero_apply, mul_ite, mul_zero]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
    cases w with
    | nil => simp [letter, eq_comm]
    | cons d w => cases w <;> simp [letter]
 theorem restrict_liftSeries (e : α → β) (he : Function.Injective e) (f : Series α) :
    restrict e (liftSeries e f) = f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons a w ih =>
    change deriv (e a) (liftSeries e f) (w.map e) = f (a::w)
    rw [deriv_liftSeries_image e he]
    exact ih (deriv a f)
 theorem restrict_liftSeries_disjoint (e : α → β) (d : γ → β)
    (hd : ∀ i j, e i ≠ d j) (f : Series α) (hf : f [] = 0) :
    (fun w : List γ => liftSeries e f (w.map d)) = 0 := by
  funext w
  cases w with
  | nil => exact hf
  | cons a w =>
    change deriv (d a) (liftSeries e f) (w.map d) = 0
    rw [deriv_liftSeries_out e f (d a) (fun i => hd i a)]
    rfl

variable [DecidableEq γ] [Fintype γ]
 theorem reparam_liftSeries (e : α → β) (c : β → γ → ℂ) (f : Series α) :
    reparam c (liftSeries e f) = reparam (fun a d => c (e a) d) f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons d w ih =>
    rw [reparam_cons, reparam_cons]
    simp only [deriv_liftSeries, reparam_sum, reparam_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [ih]
 theorem reparam_identity (f : Series α) : reparam (fun a b : α => if a=b then 1 else 0) f = f := by
  funext w
  have h := congrFun (restrict_liftSeries (id : α → α) Function.injective_id f) w
  change reparam (fun a b : α => if a=b then 1 else 0) f (w.map id) = f w at h
  simpa only [List.map_id] using h
 theorem reparam_scalar (z : ℂ) (f : Series α) (w : List α) :
    reparam (fun a b : α => if a=b then z else 0) f w = z^w.length * f w := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [reparam_cons]
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
    rw [ih]
    simp [deriv_apply, pow_succ, mul_assoc, mul_left_comm]
 theorem reparam_scalar_quadratic (z : ℂ) :
    reparam (fun a b : α => if a=b then z else 0) quadratic = z^2 • quadratic := by
  funext w
  rw [reparam_scalar]
  cases w with
  | nil => simp
  | cons a w =>
    cases w with
    | nil => simp [quadratic]
    | cons b w => cases w <;> simp [quadratic]

 theorem Cyclic.append {α : Type} [DecidableEq α] [Fintype α] {f : Series α} (hf : Cyclic f) (u v : List α) :
    f (u++v) = f (v++u) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    have hh := congrFun (hf a) (u++v)
    change f (a::(u++v)) = f ((u++v)++[a]) at hh
    simp only [List.cons_append, hh, List.append_assoc]
    rw [ih]
    simp
 theorem cyclic_quadratic {α : Type} [DecidableEq α] [Fintype α] : Cyclic (quadratic : Series α) := by
  intro a
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    cases w with
    | nil => simp [deriv, rightDeriv, quadratic, eq_comm]
    | cons d w => cases w <;> rfl
 theorem deriv_moments {α : Type} [DecidableEq α] [Fintype α] {R : Series α} (hR : R [] = 0) (i : α) :
    deriv i (moments R) = conv (moments R) (subst (moments R) (deriv i R)) := by
  funext w
  have hh := congrFun (moments_eq hR) (i::w)
  simpa [subst_cons] using hh

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordLinearLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem wordEval_mem {M : VonNeumannAlgebra H} {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) (w : List (Fin n)) : wordEval X w ∈ M := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih => simpa [wordEval] using M.mul_mem (hX i) ih
 theorem wordMoment_cyclic {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) : Cyclic (wordMoment τ X) := by
  intro i
  funext w
  change trace τ ((i::w).map X).prod = trace τ ((w++[i]).map X).prod
  simpa [trace, wordEval, List.map_cons, List.prod_cons, List.map_append, List.prod_append] using
    τ.tracial (X i) (hX i) (wordEval X w) (wordEval_mem X hX w)
 theorem wordMoment_restrict {M : VonNeumannAlgebra H} (τ : TracialVector M) {n m : ℕ}
    (X : Fin n → H →L[ℂ] H) (e : Fin m → Fin n) :
    restrict e (wordMoment τ X) = wordMoment τ (fun i => X (e i)) := by
  funext w
  simp [FreeSeries.restrict, wordMoment, wordEval, List.map_map, Function.comp_def]

 theorem reparam_wordMoment {M : VonNeumannAlgebra H} (τ : TracialVector M) {n m : ℕ}
    (X : Fin n → H →L[ℂ] H) (c : Fin n → Fin m → ℂ) :
    reparam c (wordMoment τ X) = wordMoment τ (fun b => ∑ a, c a b • X a) := by
  let Y := fun b => ∑ a, c a b • X a
  have hh (w : List (Fin m)) (A : H →L[ℂ] H) :
      reparam c (fun v => trace τ (A * wordEval X v)) w = trace τ (A * wordEval Y w) := by
    induction w generalizing A with
    | nil => simp [wordEval]
    | cons b w ih =>
      rw [reparam_cons]
      have hf (a : Fin n) : deriv a (fun v => trace τ (A * wordEval X v)) =
          (fun v => trace τ ((A * X a) * wordEval X v)) := by
        funext v; simp [FreeSeries.deriv, wordEval, mul_assoc]
      simp only [hf, ih]
      change _ = trace τ (A * (Y b * wordEval Y w))
      rw [← mul_assoc]
      dsimp only [Y]
      rw [Finset.mul_sum, Finset.sum_mul, trace_sum]
      apply sum_congr rfl
      intro a _
      simp only [mul_smul_comm, smul_mul_assoc, trace_smul]
  funext w
  change reparam c (fun v => trace τ (wordEval X v)) w = trace τ (wordEval Y w)
  simpa only [one_mul] using hh w 1

 theorem pairDerivative_eq {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    conv M (subst M (letter i)) w = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [← deriv_quadratic i, ← subst_cons]
  exact quadratic_subst_derivative M i w
 theorem derivativeMoment_series {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) :
    (fun w => derivativeMoment τ X i w) =
      conv (wordMoment τ X) (subst (wordMoment τ X) (letter i)) := by
  funext w
  rw [pairDerivative_eq]
  rfl
 theorem pairDerivative_congr {α : Type} [DecidableEq α] [Fintype α]
    {M N : Series α} {k : ℕ} (h : Agree k M N) (i : α) :
    Agree k (conv M (subst M (letter i))) (conv N (subst N (letter i))) :=
  conv_agree h (subst_agree h (Agree.refl _ _))

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Signal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

theorem norm_sum_sq_orthogonal {H : Type u1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type u2} [Fintype ι] (x : ι → H)
    (h : ∀ i j, i ≠ j → inner ℂ (x i) (x j) = 0) :
    ‖∑ i, x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
  have hs (i : ι) : inner ℂ (x i) (∑ j, x j) = inner ℂ (x i) (x i) := by
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hji => h i j (Ne.symm hji)) (by simp)
  simp_rw [hs]
  simp only [map_sum, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

namespace FreeTensor

variable {B N A : Type} [DecidableEq B] [DecidableEq N] [AddCommGroup A]
  [Fintype A] [DecidableEq A]

omit [Fintype A] in
 theorem groupUnitary_add (a b : A) :
    groupUnitary (B := B) (N := N) (a + b) = groupUnitary a * groupUnitary b :=
  unitaryG_mul _ _

 theorem groupUnitary_mul_characterProjection (a : A) (ψ : AddChar A ℂ) :
    groupUnitary (B := B) (N := N) a * characterProjection ψ = ψ a • characterProjection ψ := by
  unfold characterProjection
  rw [mul_smul_comm, Finset.mul_sum, smul_comm (ψ a)]
  congr 1
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addLeft a)
  intro b
  rw [mul_smul_comm]
  change ψ (-b) • (groupUnitary (B := B) (N := N) a * groupUnitary b) =
    ψ a • (ψ (-(a + b)) • groupUnitary (a + b))
  simp only [← groupUnitary_add, smul_smul]
  congr 1
  rw [neg_add, AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel]
  simp

 theorem characterProjection_mul (ψ φ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ * characterProjection φ =
      if ψ = φ then characterProjection ψ else 0 := by
  classical
  rw [characterProjection, smul_mul_assoc, Finset.sum_mul]
  simp only [smul_mul_assoc, groupUnitary_mul_characterProjection, smul_smul,
    ← Finset.sum_smul]
  have hs : (∑ a : A, ψ (-a) * φ a) = if ψ = φ then (Fintype.card A : ℂ) else 0 := by
    have he (a : A) : ψ (-a) * φ a = (-ψ + φ) a := by
      simp [AddChar.add_apply, AddChar.neg_apply, AddChar.map_neg_eq_inv]
    simp_rw [he]
    rw [AddChar.sum_eq_ite]
    congr 1
    exact propext neg_add_eq_zero
  rw [hs]
  by_cases h : ψ = φ
  · subst φ
    simp [Fintype.card_ne_zero, characterProjection]
  · simp only [h, ↓reduceIte, mul_zero,
      zero_smul ℂ (characterProjection (B := B) (N := N) φ)]

 theorem sum_characterProjection :
    ∑ ψ : AddChar A ℂ, characterProjection (B := B) (N := N) ψ = 1 := by
  classical
  unfold characterProjection
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero]
  simp [smul_smul, Fintype.card_ne_zero]

omit [Fintype A] in
 theorem trace_groupUnitary (a : A) :
    trace (tracialVector B N (Multiplicative A)) (groupUnitary a) = if a = 0 then 1 else 0 := by
  rw [trace_unitaryG]
  rfl

 theorem trace_characterProjection (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A)) (characterProjection ψ) =
      (Fintype.card A : ℂ)⁻¹ := by
  rw [characterProjection, trace_smul, trace_sum]
  simp [trace_smul, trace_groupUnitary]

 theorem spectralSignal_selfAdjoint (y : AddChar A ℂ → ℝ) :
    IsSelfAdjoint (spectralSignal (B := B) (N := N) y) := by
  show star _ = _
  simp [spectralSignal,
    star_sum (R := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A))]

 theorem spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    spectralSignal (B := B) (N := N) y ^ k = ∑ ψ, ((y ψ : ℂ) ^ k) • characterProjection ψ := by
  classical
  induction k with
  | zero => simpa using (sum_characterProjection (B := B) (N := N) (A := A)).symm
  | succ k ih =>
    rw [pow_succ, ih, spectralSignal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [smul_mul_assoc, Finset.mul_sum]
    simp only [mul_smul_comm, characterProjection_mul]
    simp only [smul_ite, smul_zero (M := ℂ) (A := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A)),
      Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, smul_smul, pow_succ]

 theorem trace_spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    trace (tracialVector B N (Multiplicative A)) (spectralSignal y ^ k) =
      (Fintype.card A : ℂ)⁻¹ * ∑ ψ, (y ψ : ℂ) ^ k := by
  rw [spectralSignal_pow, trace_sum]
  simp only [trace_smul, trace_characterProjection, ← Finset.sum_mul]
  exact mul_comm _ _

 theorem characterProjection_orthogonal (ψ φ : AddChar A ℂ) (h : ψ ≠ φ)
    (v w : Space B N (Multiplicative A)) :
    inner ℂ (characterProjection ψ v) (characterProjection φ w) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    star_characterProjection, ← mul_apply_eq_comp, characterProjection_mul, ite_eq_right (Ne.symm h)]
  simp

 theorem spectralSignal_norm_le (y : AddChar A ℂ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ ψ, |y ψ| ≤ R) : ‖spectralSignal (B := B) (N := N) y‖ ≤ R := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  have hx : ∑ ψ : AddChar A ℂ, characterProjection ψ x = x := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun T : Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A) => T x)
        (sum_characterProjection (B := B) (N := N) (A := A))
  have hn : ∑ ψ : AddChar A ℂ, ‖characterProjection ψ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← norm_sum_sq_orthogonal _ (fun ψ φ h => characterProjection_orthogonal ψ φ h x x), hx]
  have hn' : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 =
      ∑ ψ : AddChar A ℂ, |y ψ| ^ 2 * ‖characterProjection ψ x‖ ^ 2 := by
    simp only [spectralSignal, sum_apply, smul_apply]
    rw [norm_sum_sq_orthogonal _ (by
      intro ψ φ h
      simp [characterProjection_orthogonal ψ φ h x x])]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hsq : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 ≤ R ^ 2 * ‖x‖ ^ 2 := by
    rw [hn', ← hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ψ _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (hy ψ) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  simpa only [mul_pow] using hsq

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem signalSlice_semicircular [Group G] (g : G) (b : B) :
    (semicircularB b).comp (signalSlice (N := N) g) =
      (signalSlice g).comp (Fock.semicircular b) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircularB b (signalSlice g (lp.single 2 w z)) =
    signalSlice g (Fock.semicircular b (lp.single 2 w z))
  rw [signalSlice_single]
  cases w with
  | nil => simp [semicircularB, creationB_single, annihilationB_single, removeB, leftB]
  | cons c w =>
    simp only [semicircularB, add_apply, creationB_single, annihilationB_single, removeB,
      Fock.semicircular_single_cons, map_add, signalSlice_single, leftB]
    by_cases h : b = c <;> simp [h]

 theorem signalSlice_word (g : G) (w : List B) :
    ((w.map (semicircularB (N := N) (G := G))).prod).comp (signalSlice g) =
      (signalSlice g).comp ((w.map Fock.semicircular).prod) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G => T x) ih
    have hc := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G =>
      T ((w.map Fock.semicircular).prod x)) (signalSlice_semicircular (N := N) g b)
    simp only [ContinuousLinearMap.comp_apply] at hi hc
    simpa only [ContinuousLinearMap.comp_apply, List.map_cons, List.prod_cons,
      mul_apply_eq_comp, hi] using hc

 theorem signalSlice_vacuum_coefficient (g : G) (x : Fock.Space B) :
    inner ℂ (basis (empty : Word B N G)) (signalSlice g x) =
      if g = 1 then inner ℂ (Fock.basisVector []) x else 0 := by
  have h : (innerSL ℂ (basis (empty : Word B N G))).comp (signalSlice g) =
      if g = 1 then innerSL ℂ (Fock.basisVector ([] : List B)) else 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro v
    apply ContinuousLinearMap.ext
    intro z
    by_cases hg : g = 1 <;> by_cases hv : v = [] <;>
      simp [hg, hv, basis, empty, Fock.basisVector, lp.inner_single_left, lp.single_apply, eq_comm]
  have hx := congrArg (fun f : Fock.Space B →L[ℂ] ℂ => f x) h
  by_cases hg : g = 1 <;> simpa [hg] using hx

theorem tensor_word_moment (w : List B) (g : G) :
    trace (tracialVector B N G) ((w.map semicircularB).prod * unitaryG g) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        (if g = 1 then 1 else 0) := by
  change inner ℂ (basis (empty : Word B N G))
    (((w.map (semicircularB (N := N) (G := G))).prod * unitaryG (B := B) (N := N) g) (basis empty)) = _
  rw [mul_apply_eq_comp, unitaryG_basis]
  have hv : basis (leftG g (empty : Word B N G)) = signalSlice g (Fock.basisVector []) := by
    simp [leftG, empty]
  rw [hv, ← ContinuousLinearMap.comp_apply, signalSlice_word,
    ContinuousLinearMap.comp_apply, signalSlice_vacuum_coefficient]
  by_cases hg : g = 1 <;> simp [hg, trace, Fock.tracialVector]

 theorem unitaryG_commutes_creationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (creationB b) := by
  apply LabelHilbert.lift_commute
  intro w
  rfl

 theorem unitaryG_commutes_semicircularB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (semicircularB b) := by
  apply (unitaryG_commutes_creationB g b).add_right
  simpa using (unitaryG_commutes_creationB (N := N) g⁻¹ b).star_star

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NoiseTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G]

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem noise_basis_orthonormal : Orthonormal ℂ (fun w : List N =>
    basis (noiseWord (B := B) (G := G) w)) := by
  rw [orthonormal_iff_ite]
  intro v w
  by_cases h : v = w
  · subst w
    simp [basis, ]
  · have h' : noiseWord (B := B) (G := G) v ≠ noiseWord w :=
      fun hh => h (noiseWord_injective hh)
    simp [basis, lp.inner_single_left, lp.single_apply, h, h']

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EquidiscreteSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

 theorem equidiscreteAtom_rev {p : ℕ} (hp : 2 ≤ p) (l : Fin p) :
    equidiscreteAtom p l.rev = -equidiscreteAtom p l := by
  have hd : (p : ℝ) - 1 ≠ 0 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hl : (l.rev.val : ℝ) = (p : ℝ) - 1 - l.val := by
    have hn : l.rev.val + 1 + l.val = p := by simp [Fin.rev]; omega
    have hr : (l.rev.val : ℝ) + 1 + l.val = p := by exact_mod_cast hn
    linarith
  unfold equidiscreteAtom
  rw [hl]
  field_simp
  ; ring

 theorem sum_equidiscreteAtom {p : ℕ} (hp : 2 ≤ p) : ∑ l : Fin p, equidiscreteAtom p l = 0 := by
  have hs := Equiv.sum_comp (Fin.revPerm (n := p)) (equidiscreteAtom p)
  simp only [Fin.revPerm_apply, equidiscreteAtom_rev hp, Finset.sum_neg_distrib] at hs
  linarith

 theorem equidiscreteAtom_abs_le {p : ℕ} (hp : 2 ≤ p) (l : Fin p) :
    |equidiscreteAtom p l| ≤ 1 := by
  have hd : 0 < (p : ℝ) - 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hl : (l.val : ℝ) ≤ (p : ℝ) - 1 := by
    have hn : l.val + 1 ≤ p := l.isLt
    exact_mod_cast (show (l.val : ℤ) ≤ (p : ℤ) - 1 by omega)
  rw [abs_le, equidiscreteAtom]
  constructor
  · have h := div_nonneg (show 0 ≤ 2 * (l.val : ℝ) by positivity) hd.le
    linarith
  · have h : 2 * (l.val : ℝ) / ((p : ℝ) - 1) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
    linarith

namespace FreeTensor
variable {B N : Type} [DecidableEq B] [DecidableEq N] (p : ℕ) [NeZero p]

 theorem equidiscreteSignal_selfAdjoint : IsSelfAdjoint (equidiscreteSignal (B := B) (N := N) p) :=
  spectralSignal_selfAdjoint _

 theorem equidiscreteSignal_norm_le (hp : 2 ≤ p) :
    ‖equidiscreteSignal (B := B) (N := N) p‖ ≤ 1 :=
  spectralSignal_norm_le _ 1 zero_le_one (fun _character => equidiscreteAtom_abs_le hp _)

 theorem equidiscreteSignal_moments (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p))) (equidiscreteSignal p ^ k) =
      (p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k := by
  rw [equidiscreteSignal, trace_spectralSignal_pow]
  simp only [ZMod.card]
  congr 1
  exact (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)

 theorem trace_equidiscreteSignal (hp : 2 ≤ p) :
    trace (tracialVector B N (Multiplicative (ZMod p))) (equidiscreteSignal p) = 0 := by
  have h := equidiscreteSignal_moments (B := B) (N := N) p 1
  simpa [← Complex.ofReal_sum, sum_equidiscreteAtom hp] using h

 theorem characterProjection_mem_background {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (J : Set N) (ψ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).smul_mem
  apply (backgroundAlgebra J).sum_mem
  intro a _
  apply (backgroundAlgebra J).smul_mem
  exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨Multiplicative.ofAdd a,rfl⟩))

 theorem equidiscreteSignal_mem_background (J : Set N) :
    equidiscreteSignal (B := B) (N := N) p ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).sum_mem
  intro ψ _
  exact (backgroundAlgebra J).smul_mem (characterProjection_mem_background J ψ) _

 theorem characterProjection_commutes_B {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (ψ : AddChar A ℂ) (b : B) :
    Commute (characterProjection (B := B) (N := N) ψ) (semicircularB b) := by
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  exact (unitaryG_commutes_semicircularB (Multiplicative.ofAdd a) b).smul_left _

 theorem equidiscreteSignal_commutes_B (b : B) :
    Commute (equidiscreteSignal (B := B) (N := N) p) (semicircularB b) := by
  apply Commute.sum_left
  intro ψ _
  exact (characterProjection_commutes_B ψ b).smul_left _

 theorem tensor_characterProjection_moment {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (w : List B) (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A))
      ((w.map semicircularB).prod * characterProjection ψ) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) * (Fintype.card A : ℂ)⁻¹ := by
  simp only [characterProjection, mul_smul_comm, Finset.mul_sum, trace_smul, trace_sum,
    groupUnitary, tensor_word_moment]
  have hi (a : A) : (Multiplicative.ofAdd a = (1 : Multiplicative A)) ↔ a = 0 := Iff.rfl
  simp only [hi]
  simp
  ring

 theorem tensor_equidiscrete_moment (w : List B) (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p)))
      ((w.map semicircularB).prod * equidiscreteSignal p ^ k) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        ((p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k) := by
  rw [equidiscreteSignal, spectralSignal_pow, Finset.mul_sum, trace_sum]
  simp only [mul_smul_comm, trace_smul, tensor_characterProjection_moment, ZMod.card]
  rw [← Finset.sum_mul]
  have hs := (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)
  change _ = _ at hs
  rw [hs]
  ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ActualTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem semicircularB_selfAdjoint [Group G] (b : B) : IsSelfAdjoint (semicircularB (N := N) (G := G) b) :=
  IsSelfAdjoint.add_star_self (creationB (N := N) (G := G) b)
 theorem semicircularN_selfAdjoint (i : N) : IsSelfAdjoint (semicircularN (B := B) (G := G) i) :=
  IsSelfAdjoint.add_star_self (creationN (B := B) (G := G) i)

 theorem backgroundAlgebra_le (J : Set N) :
    backgroundAlgebra (B := B) (G := G) J ≤ (algebra B N G).toStarSubalgebra.toSubalgebra := by
  apply Algebra.adjoin_le
  rintro _ ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,_,rfl⟩)
  · exact semicircularB_mem b
  · exact unitaryG_mem g
  · exact semicircularN_mem i

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

end FreeTensor

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem initialIndex_injective [NeZero p] : Function.Injective (initialIndex p) := Fin.castAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_injective [NeZero p] : Function.Injective (auxiliaryIndex p) := Fin.natAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_fresh [NeZero p] (i : Fin (p+1)) : auxiliaryIndex p i ∉ oldNoise p := by
  rintro ⟨j,h⟩
  have hv := congrArg Fin.val h
  simp only [initialIndex, auxiliaryIndex, Fin.val_castAdd, Fin.val_natAdd] at hv
  have hj := j.isLt
  omega

 theorem C_selfAdjoint (i : Fin (p+1)) : IsSelfAdjoint (C p i) := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_selfAdjoint p
  | cast i => rw [C_castSucc]; exact semicircularB_selfAdjoint i

 theorem C_mem_background (J : Set (Fin ((p+1)+(p+1)))) (i : Fin (p+1)) :
    C p i ∈ backgroundAlgebra J := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_mem_background p J
  | cast i => rw [C_castSucc]; exact semicircularB_mem_background J i

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MixedGaussianSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}
 theorem leftIndex_injective : Function.Injective (leftIndex (n := n)) := Fin.castAdd_injective n n
 theorem rightIndex_injective : Function.Injective (rightIndex (n := n)) := Fin.natAdd_injective n n
 theorem leftIndex_ne_rightIndex (i j : Fin n) : leftIndex i ≠ rightIndex j := by
  intro h
  have hh := congrArg Fin.val h
  simp [leftIndex, rightIndex] at hh
  have hi := i.isLt
  omega
 theorem joint_cases (j : Fin (n+n)) : (∃i, j=leftIndex i) ∨ (∃i, j=rightIndex i) := by
  induction j using Fin.addCases with
  | left i => exact Or.inl ⟨i,rfl⟩
  | right i => exact Or.inr ⟨i,rfl⟩
 theorem gaussianJointR_noise_deriv (R : Series (Fin n)) (i : Fin n) :
    FreeSeries.deriv (rightIndex i) (gaussianJointR R) = letter (rightIndex i) := by
  change FreeSeries.deriv (rightIndex i) (liftSeries leftIndex R) +
    FreeSeries.deriv (rightIndex i) (liftSeries rightIndex quadratic) = _
  rw [deriv_liftSeries_out _ _ _ (fun j => leftIndex_ne_rightIndex j i),
    deriv_liftSeries_image _ rightIndex_injective, deriv_quadratic, liftSeries_letter, zero_add]
 theorem gaussianJointR_restrict (R : Series (Fin n)) : restrict leftIndex (gaussianJointR R) = R := by
  have hh := restrict_liftSeries_disjoint (rightIndex (n := n)) leftIndex
    (fun i j => (leftIndex_ne_rightIndex j i).symm) (quadratic : Series (Fin n)) quadratic_nil
  have hl := restrict_liftSeries (leftIndex (n := n)) leftIndex_injective R
  funext w
  exact (congrArg₂ (·+·) (congrFun hl w) (congrFun hh w)).trans (add_zero _)
 theorem gaussianJointR_cyclic {R : Series (Fin n)} (hR : Cyclic R) : Cyclic (gaussianJointR R) := by
  have hL := hR.reparam (fun a b => if leftIndex a=b then (1:ℂ) else 0)
  have hN := (cyclic_quadratic (α := Fin n)).reparam (fun a b => if rightIndex a=b then (1:ℂ) else 0)
  intro i
  change FreeSeries.deriv i (liftSeries leftIndex R) + FreeSeries.deriv i (liftSeries rightIndex quadratic) =
    rightDeriv i (liftSeries leftIndex R) + rightDeriv i (liftSeries rightIndex quadratic)
  exact congrArg₂ (·+·) (hL i) (hN i)
 theorem word_left_or_noise (w : List (Fin (n+n))) :
    (∃ v : List (Fin n), w=v.map leftIndex) ∨ (∃u i v, w=u++rightIndex i::v) := by
  induction w with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons a w ih =>
    rcases joint_cases a with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · rcases ih with ⟨v,rfl⟩ | ⟨u,j,v,rfl⟩
      · exact Or.inl ⟨i::v,rfl⟩
      · exact Or.inr ⟨leftIndex i::u,j,v,rfl⟩
    · exact Or.inr ⟨[],i,w,rfl⟩

theorem mixed_gaussian_unique {M N : Series (Fin (n+n))}
    (hM : Cyclic M) (hN : Cyclic N) (hleft : restrict leftIndex M = restrict leftIndex N)
    (hm : ∀ i, FreeSeries.deriv (rightIndex i) M = conv M (subst M (letter (rightIndex i))))
    (hn : ∀ i, FreeSeries.deriv (rightIndex i) N = conv N (subst N (letter (rightIndex i)))) : M=N := by
  funext w
  induction w using length_induction with
  | h w ih =>
    rcases word_left_or_noise w with ⟨v,rfl⟩ | ⟨u,i,v,rfl⟩
    · exact congrFun hleft v
    · rw [hM.append u _, hN.append u _]
      change FreeSeries.deriv (rightIndex i) M (v++u) = FreeSeries.deriv (rightIndex i) N (v++u)
      rw [hm, hn]
      exact pairDerivative_congr (fun z hz => ih z (by simp at hz ⊢; omega)) _ (v++u) le_rfl
 theorem moments_cumulants {α : Type} [DecidableEq α] [Fintype α] {M : Series α} (hM : M [] = 1) :
    moments (cumulants M) = M := (moments_unique (cumulants_nil M) (cumulants_equation hM)).symm
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem jointTuple_mem (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (j : Fin (n+n)) :
    jointTuple X σ j ∈ algebra B N G := by
  rcases joint_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [jointTuple_left]; exact backgroundAlgebra_le J (hX i)
  · rw [jointTuple_right]; exact semicircularN_mem _
 theorem jointTuple_noise_deriv (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) (i : Fin n) :
    FreeSeries.deriv (rightIndex i) (wordMoment (tracialVector B N G) (jointTuple X σ)) =
      conv (wordMoment (tracialVector B N G) (jointTuple X σ))
        (subst (wordMoment (tracialVector B N G) (jointTuple X σ)) (letter (rightIndex i))) := by
  let Z := jointTuple X σ
  let τ := tracialVector B N G
  have hc (j : Fin (n+n)) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) + if j=rightIndex i then (1:ℂ) • vacuumRankOne τ else 0 := by
    rcases joint_cases j with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · simpa [Z, leftIndex_ne_rightIndex] using (rightAnnihilationN_background (hs i) (hX k)).eq
    · have he : σ i = σ k ↔ rightIndex k = rightIndex i := by
        rw [hσ.eq_iff, rightIndex_injective.eq_iff, eq_comm]
      simpa [Z, he] using rightAnnihilationN_semicircularN (B := B) (G := G) (σ i) (σ k)
  funext w
  rw [← derivativeMoment_series]
  have h := commutator_integration_by_parts τ Z (star (rightCreationN (σ i)))
    (rightIndex i) 1 hc (by simp [τ, tracialVector, basis, empty]) w
  simp only [star_star, one_mul] at h
  have hv : rightCreationN (σ i) τ.vacuum = semicircularN (σ i) τ.vacuum := by
    simp [τ, tracialVector, semicircularN, basis, rightCreationN_single, creationN_single,
      annihilationN_single, removeN, rightN_eq_append, empty, append, leftN, push]
  rw [hv, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (semicircularN_selfAdjoint (B := B) (G := G) (σ i)).star_eq] at h
  change trace τ (semicircularN (σ i) * wordEval Z w) = _ at h
  simpa [FreeSeries.deriv, wordMoment, wordEval, Z] using h

 theorem joint_moments_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    wordMoment (tracialVector B N G) (jointTuple X σ) =
      moments (gaussianJointR (cumulants (wordMoment (tracialVector B N G) X))) := by
  let τ := tracialVector B N G
  let M := wordMoment τ X
  have hM : M [] = 1 := by simp [M]
  have hC : Cyclic M := wordMoment_cyclic τ X (fun i => backgroundAlgebra_le J (hX i))
  let R := gaussianJointR (cumulants M)
  have hR : R [] = 0 := gaussianJointR_nil _ (cumulants_nil M)
  apply mixed_gaussian_unique
  · exact wordMoment_cyclic τ _ (jointTuple_mem J X hX σ)
  · exact cyclic_moments hR (gaussianJointR_cyclic (cyclic_cumulants hM hC))
  · rw [restrict_moments leftIndex hR, gaussianJointR_restrict, moments_cumulants hM, wordMoment_restrict]
    congr 1
    funext i
    exact jointTuple_left X σ i
  · exact jointTuple_noise_deriv J X hX σ hσ hs
  · intro i
    rw [deriv_moments hR, gaussianJointR_noise_deriv]
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatCumulants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}

 theorem heatCoefficients_R (u : ℝ) (hu : 0 ≤ u) (R : Series (Fin n)) :
    reparam (heatCoefficients u) (gaussianJointR R) = R + (u : ℂ) • quadratic := by
  rw [gaussianJointR, reparam_add, reparam_liftSeries, reparam_liftSeries]
  simp only [heatCoefficients_left, heatCoefficients_right, reparam_identity, reparam_scalar_quadratic]
  congr 2
  exact_mod_cast Real.sq_sqrt hu
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem heat_linear_tuple (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (σ : Fin n → N) (u : ℝ) :
    (fun i => ∑ j, heatCoefficients u j i • jointTuple X σ j) =
      heatTuple X (fun i => semicircularN (σ i)) u := by
  funext i
  rw [Fin.sum_univ_add]
  change (∑ j : Fin n, heatCoefficients u (leftIndex j) i • jointTuple X σ (leftIndex j)) +
    (∑ j : Fin n, heatCoefficients u (rightIndex j) i • jointTuple X σ (rightIndex j)) = _
  simp only [heatCoefficients_left, heatCoefficients_right, jointTuple_left,
    jointTuple_right, ite_smul, one_smul,
    zero_smul ℂ (A := Space B N G →L[ℂ] Space B N G), Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, heatTuple]

theorem heat_moments_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) :
    wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) =
      moments (cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic) := by
  rw [← heat_linear_tuple X σ u, ← reparam_wordMoment,
    joint_moments_cumulants J X hX σ hσ hs,
    reparam_moments (heatCoefficients u) (gaussianJointR_nil _ (cumulants_nil _)),
    heatCoefficients_R u hu]
 theorem heat_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) :
    cumulants (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u)) =
      cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic := by
  let R := cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic
  have hR : R [] = 0 := by simp [R]
  rw [heat_moments_cumulants J X hX σ hσ hs u hu]
  exact (cumulants_unique (moments_nil _) (moments_eq hR)).symm
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.OptionSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β : Type} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
theorem deriv_ignore_none [DecidableEq α] [Fintype α] (f : Series α) : deriv none (ignoreLetter f) = ignoreLetter f := rfl

omit [DecidableEq α] [Fintype α] in
theorem deriv_ignore_some [DecidableEq α] [Fintype α] (f : Series α) (a : α) :
    deriv (some a) (ignoreLetter f) = ignoreLetter (deriv a f) := rfl
 theorem ignoreLetter_norm_sq (f : Series α) (n : ℕ) :
    degreeNorm (ignoreLetter f) n^2 =
      ∑ k ∈ range (n+1), (n.choose k : ℝ) * degreeNorm f k^2 := by
  induction n generalizing f with
  | zero => simp [degreeNorm_nil, ignoreLetter]
  | succ n ih =>
    rw [degreeNorm_succ_sq, Fintype.sum_option, deriv_ignore_none, ih]
    simp only [deriv_ignore_some, ih]
    rw [sum_comm]
    simp only [← mul_sum, ← degreeNorm_succ_sq]
    exact (Finset.sum_choose_succ_mul (fun k _ => degreeNorm f k^2) n).symm
 theorem ignoreLetter_norm_le {f : Series α} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ n, degreeNorm f n ≤ A^n) (n : ℕ) :
    degreeNorm (ignoreLetter f) n ≤ (A+1)^n := by
  apply (sq_le_sq₀ (degreeNorm_nonneg _ _) (pow_nonneg (by linarith) _)).mp
  rw [ignoreLetter_norm_sq]
  calc
    _ ≤ ∑ k ∈ range (n+1), (n.choose k : ℝ) * (A^k)^2 := by
      apply sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (degreeNorm_nonneg _ _) (hf k) 2) (by positivity)
    _ = (A^2+1)^n := by
      rw [add_pow]
      apply sum_congr rfl
      intro k hk
      rw [one_pow, mul_one, ← pow_mul, ← pow_mul, Nat.mul_comm k 2, mul_comm]
    _ ≤ ((A+1)^2)^n := pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]

omit [DecidableEq α] in
theorem degreeNorm_equiv [DecidableEq α] [Fintype β] (e : α ≃ β) (f : Series β) (n : ℕ) :
    degreeNorm (fun w => f (w.map e)) n = degreeNorm f n := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  rw [degreeNorm_sq, degreeNorm_sq]
  exact (vectorMap e n).sum_comp (fun w : List.Vector β n => ‖f w.val‖^2)

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
variable {α : Type} [Fintype α]

theorem cumulants_norm_le {M : Series α} (hM : M [] = 1) {A : ℝ} (hA : 0 < A)
    (h : ∀ n, 0 < n → degreeNorm M n ≤ A^n) (n : ℕ) :
    degreeNorm (cumulants M) n ≤ (32*A)^n := by
  let B := 4*A
  have hB : 0 < B := by dsimp [B]; positivity
  let r := B⁻¹
  have hr : 0 < r := inv_pos.mpr hB
  have hrA : r*A = 1/4 := by dsimp [r, B]; field_simp
  have hw (N : ℕ) : seriesWeight (M-unit) r N ≤ 1/3 := by
    have hz : (M-unit : Series α) [] = 0 := by simp [hM]
    have hb (m : ℕ) (hm : 0 < m) : degreeNorm (M-unit) m ≤ A^m := by
      rw [degreeNorm_sub_unit_pos M hm]
      exact h m hm
    have hh := weight_le_geom hz hA.le hr.le (by rw [hrA]; norm_num) hb N
    norm_num [hrA] at hh ⊢
    exact hh
  have hwB (N : ℕ) : seriesWeight (boolean M) r N ≤ 1/2 := by
    have he : boolean M = -(inverse M-unit) := by unfold boolean; abel
    rw [he, seriesWeight_neg]
    have hh := inverse_tail_weight hM hr.le (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (1:ℝ)/3 < 1) N (hw N)
    norm_num at hh ⊢
    exact hh
  have hBn (m : ℕ) : degreeNorm (boolean M) m ≤ B^m := by
    have hh := degreeNorm_le_of_weight hr (fun N => (hwB N).trans (by norm_num)) m
    simpa [r] using hh
  let t := (8*B)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have htB : (2*t)*B = 1/4 := by dsimp [t]; field_simp ; ring
  have hneg : (-boolean M) [] = 0 := by simp
  have hnegW (N : ℕ) : seriesWeight (-boolean M) (2*t) N ≤ 1/3 := by
    have hh := weight_le_geom hneg hB.le (by positivity : 0 ≤ 2*t)
      (by rw [htB]; norm_num) (fun m _ => by simpa using hBn m) N
    norm_num [htB] at hh ⊢
    exact hh
  have hJ (N : ℕ) : seriesWeight (moments (-boolean M)-unit) t N ≤ 1/3 :=
    moments_tail_weight hneg ht.le (by norm_num) (by norm_num) hnegW N
  have hR (N : ℕ) : seriesWeight (cumulants M) t N ≤ 1 := by
    have hh := inverse_tail_weight (moments_nil (-boolean M)) ht.le
      (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (1:ℝ)/3 < 1) N (hJ N)
    change seriesWeight (cumulants M) t N ≤ _ at hh
    norm_num at hh
    exact hh.trans (by norm_num)
  have hh := degreeNorm_le_of_weight ht hR n
  norm_num [t, B, ← mul_assoc] at hh
  exact hh

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries

section Product
variable {α A : Type} [DecidableEq α] [Monoid A]
 theorem option_word_product (B : α → A) (Y : A) (h : ∀ i, Commute Y (B i)) (w : List (Option α)) :
    (w.map (optionTuple B Y)).prod = ((w.filterMap id).map B).prod * Y^(w.count none) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a with
    | none =>
      simp only [List.map_cons, List.prod_cons, optionTuple, List.filterMap_cons, id_eq, ih]
      have hc := Commute.list_prod_right ((w.filterMap id).map B) Y (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact h i)
      simp only [List.count_cons_self]
      change Y * (((w.filterMap id).map B).prod * Y ^ w.count none) = _
      rw [← mul_assoc, hc.eq, mul_assoc, pow_succ']
      rfl
    | some i => simp [optionTuple, ih, mul_assoc]
end Product

section TraceNorm
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem norm_trace_le_opNorm {M : VonNeumannAlgebra H} (τ : TracialVector M) (A : H →L[ℂ] H) :
    ‖trace τ A‖ ≤ ‖A‖ := by
  apply (norm_inner_le_norm _ _).trans
  simpa only [τ.norm_vacuum, one_mul, mul_one] using A.le_opNorm τ.vacuum
end TraceNorm

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem signal_option_product (w : List (Option (Fin p))) :
    wordEval (C p) (w.map (optionFin p)) =
      ((w.filterMap id).map (semicircularB (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)))).prod *
        equidiscreteSignal p ^ (w.count none) := by
  unfold wordEval
  rw [List.map_map]
  have hf : (fun a => C p (optionFin p a)) = optionTuple semicircularB (equidiscreteSignal p) := by
    funext a
    cases a <;> simp [optionTuple]
  change (w.map (fun a => C p (optionFin p a))).prod = _
  rw [hf]
  exact option_word_product _ _ (equidiscreteSignal_commutes_B p) w
 theorem signal_option_moments (w : List (Option (Fin p))) :
    signalMoments p (w.map (optionFin p)) = fockMoments p (w.filterMap id) *
      trace (τ p) (equidiscreteSignal p ^ (w.count none)) := by
  unfold signalMoments wordMoment
  rw [signal_option_product, tensor_equidiscrete_moment, equidiscreteSignal_moments]
  rfl
 theorem signal_option_coeff_norm_le (hp : 2 ≤ p) (w : List (Option (Fin p))) :
    ‖signalMoments p (w.map (optionFin p))‖ ≤ ‖ignoreLetter (fockMoments p) w‖ := by
  rw [signal_option_moments, norm_mul]
  change _ ≤ ‖fockMoments p (w.filterMap id)‖
  let : Nontrivial (H p) := ⟨⟨basis empty, 0, by
    intro h
    have he := congrArg (fun f : H p => f empty) h
    simp [basis, lp.single_apply] at he⟩⟩
  have hy : ‖trace (τ p) (equidiscreteSignal p ^ (w.count none))‖ ≤ 1 := by
    apply (norm_trace_le_opNorm _ _).trans
    apply (norm_pow_le _ _).trans
    exact (pow_le_pow_left₀ (norm_nonneg _) (equidiscreteSignal_norm_le p hp) _).trans_eq (one_pow _)
  exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (mul_one _)
 theorem signalMoments_norm_le (hp : 2 ≤ p) (n : ℕ) :
    degreeNorm (signalMoments p) n ≤ (4*Real.sqrt (Real.sqrt p))^n := by
  rw [← degreeNorm_equiv (optionFin p) (signalMoments p) n]
  apply (degreeNorm_le_of_coeff (fun w _ => signal_option_coeff_norm_le p hp w)).trans
  apply (ignoreLetter_norm_le (by positivity) (fockMoments_norm_le (by omega)) n).trans
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hq1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt p) := by
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hp1)
  exact pow_le_pow_left₀ (by positivity) (by linarith) _
 theorem signalCumulants_norm_le (hp : 2 ≤ p) (n : ℕ) :
    degreeNorm (cumulants (signalMoments p)) n ≤ (128*Real.sqrt (Real.sqrt p))^n := by
  have hM : signalMoments p [] = 1 := by simp [signalMoments]
  have hA : 0 < 4*Real.sqrt (Real.sqrt (p:ℝ)) := by
    have hp' : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hh := cumulants_norm_le hM hA (fun m _ => signalMoments_norm_le p hp m) n
  norm_num [← mul_assoc] at hh
  exact hh
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem inner_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) (v : H) :
    inner ℂ v (commutatorKernel (vacuumRankOne τ) X i w τ.vacuum) =
      ∑ r : Fin w.length, if w[r.val] = i then
        inner ℂ v (wordEval X (w.take r.val) τ.vacuum) *
          wordMoment τ X (w.drop (r.val + 1)) else 0 := by
  rw [commutatorKernel, sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · simp only [vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      map_smul, inner_smul_right, wordMoment, trace]
    exact mul_comm _ _
  · simp

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem rightAnnihilationN_heat {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i j : Fin n) :
    star (rightCreationN (σ i)) * heatTuple X (fun k => semicircularN (σ k)) u j =
      heatTuple X (fun k => semicircularN (σ k)) u j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
  change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
  rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
    rightAnnihilationN_semicircularN]
  dsimp [heatTuple]
  by_cases hij : j = i
  · subst j
    simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
    congr 1
    exact smul_add _ _ _
  · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
    simp only [ite_eq_right hij, ite_eq_right hneq, add_zero, add_mul, smul_mul_assoc]

theorem wick_testing {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (js w : List (Fin n)) :
    inner ℂ (basis (noiseWord ((js.map σ).reverse)))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
  let Z := heatTuple X (fun k => semicircularN (σ k)) u
  change inner ℂ _ (wordEval Z w _) = _ * reverseDerivativeMoment _ Z js w
  induction js generalizing w with
  | nil => simp [reverseDerivativeMoment, wordMoment, trace, tracialVector]
  | cons i js ih =>
    have hvec : basis (noiseWord (((i :: js).map σ).reverse)) =
        rightCreationN (σ i) (basis (noiseWord ((js.map σ).reverse)) : Space B N G) := by
      simp only [List.map_cons, List.reverse_cons, basis, rightCreationN_single, rightN_noiseWord]
    rw [hvec, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint]
    have hc := commutator_word (vacuumRankOne (tracialVector B N G))
      (star (rightCreationN (σ i))) Z i (Real.sqrt u : ℂ)
      (rightAnnihilationN_heat J X hX σ hσ hs u i) w
    have hc' := congrArg (fun T : Space B N G →L[ℂ] Space B N G =>
      T (tracialVector B N G).vacuum) hc
    have hz : star (rightCreationN (σ i)) (tracialVector B N G).vacuum = 0 := by
      simp [tracialVector, basis, empty]
    simp only [mul_apply_eq_comp, hz, map_zero, add_apply, zero_add, smul_apply] at hc'
    rw [hc', inner_smul_right, inner_commutatorKernel]
    simp_rw [ih]
    rw [reverseDerivativeMoment, List.length_cons, pow_succ, Finset.mul_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MonomialSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]
 theorem deriv_monomial (a b : α) (v : List α) :
    FreeSeries.deriv b (monomial (a::v)) = if b=a then monomial v else 0 := by
  funext w
  by_cases h : b=a <;> simp [FreeSeries.deriv, monomial, h]
 theorem monomial_append (v q : List α) : monomial (v++q) = conv (monomial v) (monomial q) := by
  funext w
  induction v generalizing w with
  | nil => simp
  | cons a v ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [conv_cons, monomial_cons_nil, zero_mul, zero_add, deriv_monomial]
      by_cases h : b=a
      · subst b; simpa [monomial] using ih w
      · simp [h, monomial]
 theorem monomial_single (i : α) : monomial [i] = letter i := by
  funext w
  cases w with
  | nil => rfl
  | cons a w => cases w <;> simp [monomial, letter]
 theorem conv_subst_letter (F M : Series α) (i : α) (w : List α) :
    conv F (subst M (letter i)) w = ∑ r : Fin w.length, if w[r.val] = i then
      F (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [conv_sum_splits, sum_range_succ]
  simp only [List.take_length, List.drop_length, subst_nil, letter_nil, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => F (w.take k) * subst M (letter i) (w.drop k))]
  apply sum_congr rfl
  intro k hk
  rw [List.drop_eq_getElem_cons k.isLt, subst_letter_cons]
  split_ifs <;> simp

variable [Fintype α]
 theorem monomial_expansion (f : Series α) (d : ℕ) :
    Agree d f (∑ v ∈ wordBall d, f v • monomial v) := by
  intro w hw
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w]
  · simp [monomial]
  · intro v hv hne; simp [monomial, Ne.symm hne]
  · intro hn; exact (hn ((mem_wordBall w d).mpr hw)).elim

omit [Fintype α] in
theorem monomial_large_agree [Fintype α] (v : List α) (d : ℕ) (h : d < v.length) :
    Agree d (monomial v) 0 := by
  intro w hw
  have hn : w ≠ v := by intro he; subst w; omega
  simp [monomial, hn]
 theorem conv_subst_monomial_large (M : Series α) (v w : List α) (h : w.length < v.length) :
    conv M (subst M (monomial v)) w = 0 := by
  have he := conv_agree (Agree.refl w.length M)
    (subst_agree (Agree.refl _ M) (monomial_large_agree v w.length h)) w le_rfl
  simpa using he
 theorem conv_subst_hasSum (M f : Series α) (w : List α) :
    HasSum (fun v => f v * conv M (subst M (monomial v)) w) (conv M (subst M f) w) := by
  have he := conv_agree (Agree.refl w.length M)
    (subst_agree (Agree.refl _ M) (monomial_expansion f w.length)) w le_rfl
  rw [subst_sum, conv_sum_right] at he
  simp only [subst_smul, conv_smul_right, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [he]
  apply hasSum_sum_of_ne_finset_zero
  intro v hv
  rw [conv_subst_monomial_large M v w (by simpa using hv), mul_zero]
end FreeSeries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem reverseDerivativeMoment_monomial {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (js w : List (Fin n)) :
    reverseDerivativeMoment τ X js w =
      conv (wordMoment τ X) (subst (wordMoment τ X) (monomial js.reverse)) w := by
  induction js generalizing w with
  | nil => simp [reverseDerivativeMoment]
  | cons i js ih =>
    rw [List.reverse_cons, monomial_append, subst_mul, ← conv_assoc, monomial_single,
      conv_subst_letter, reverseDerivativeMoment]
    apply sum_congr rfl
    intro r hr
    split_ifs <;> simp [ih]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem polynomialL2_ext {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {x y : H}
    (hx : x ∈ polynomialL2 τ X) (hy : y ∈ polynomialL2 τ X)
    (h : ∀ w, inner ℂ x (wordEval X w τ.vacuum) = inner ℂ y (wordEval X w τ.vacuum)) : x = y := by
  have hmem := (polynomialL2 τ X).sub_mem hx hy
  have hker : polynomialL2 τ X ≤ (innerSL ℂ (x - y)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨w,rfl⟩
      change inner ℂ (x-y) (wordEval X w τ.vacuum) = 0
      rw [inner_sub_left, h w, sub_self]
    · exact (innerSL ℂ (x-y)).isClosed_ker
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hker hmem))

 theorem polynomialL2_eq_projection {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {x y : H}
    (hx : x ∈ polynomialL2 τ X)
    (h : ∀ w, inner ℂ x (wordEval X w τ.vacuum) = inner ℂ y (wordEval X w τ.vacuum)) :
    x = (polynomialL2 τ X).starProjection y := by
  apply polynomialL2_ext τ X hx ((polynomialL2 τ X).starProjection_apply_mem y)
  intro w
  have hp := (polynomialL2 τ X).starProjection_inner_eq_zero y
    (wordEval X w τ.vacuum) (wordVector_mem_polynomialL2 τ X w)
  rw [inner_sub_left, ← h w] at hp
  exact sub_eq_zero.mp hp

 theorem norm_le_of_polynomial_testing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {x y : H}
    (hx : x ∈ polynomialL2 τ X)
    (h : ∀ w, inner ℂ x (wordEval X w τ.vacuum) = inner ℂ y (wordEval X w τ.vacuum)) :
    ‖x‖ ≤ ‖y‖ := by
  rw [polynomialL2_eq_projection τ X hx h]
  exact (polynomialL2 τ X).norm_starProjection_apply_le y

 theorem conjugate_residual_norm_sq {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) (v : ℝ)
    (hv : ‖X i τ.vacuum‖ ^ 2 = v) :
    ‖X i τ.vacuum - (v : ℂ) • ξ i‖ ^ 2 = v ^ 2 * ‖ξ i‖ ^ 2 - v := by
  have hp : inner ℂ (X i τ.vacuum) (ξ i) = 1 := by
    rw [← inner_conj_symm, conjugate_coordinate_pairing τ hξ i]
    simp
  rw [norm_sub_sq (𝕜 := ℂ), hv, inner_smul_right, hp, mul_one, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  change v - 2 * v + v ^ 2 * ‖ξ i‖ ^ 2 = _
  ring

theorem fisher_residual_bound {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (v : Fin n → ℝ) (u : ℝ) (hu : 0 < u)
    (hv : ∀ i, ‖X i τ.vacuum‖ ^ 2 = v i) (hvu : ∀ i, u ≤ v i)
    (R : Fin n → H)
    (hR : ∀ i w, inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) -
        (v i : ℂ) * derivativeMoment τ X i w = inner ℂ (R i) (wordEval X w τ.vacuum)) :
    0 ≤ (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ∧
      (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ≤ (u ^ 2)⁻¹ * ∑ i, ‖R i‖ ^ 2 := by
  have hvp (i : Fin n) : 0 < v i := hu.trans_le (hvu i)
  have hl (i : Fin n) : (v i)⁻¹ ≤ ‖ξ i‖ ^ 2 := by
    simpa only [hv i, one_div] using conjugate_norm_sq_lower τ hξ i
  have hn (i : Fin n) : ‖X i τ.vacuum - (v i : ℂ) • ξ i‖ ≤ ‖R i‖ := by
    apply norm_le_of_polynomial_testing τ X
    · apply (polynomialL2 τ X).sub_mem
      · simpa [wordEval] using wordVector_mem_polynomialL2 τ X [i]
      · exact (polynomialL2 τ X).smul_mem _ (hξ i).1
    · intro w
      simpa only [inner_sub_left, inner_smul_left, map_ofNat, Complex.conj_ofReal,
        (hξ i).2 w] using hR i w
  have hi (i : Fin n) : ‖ξ i‖ ^ 2 - (v i)⁻¹ ≤ (u ^ 2)⁻¹ * ‖R i‖ ^ 2 := by
    have hs : (v i) ^ 2 * ‖ξ i‖ ^ 2 - v i ≤ ‖R i‖ ^ 2 := by
      rw [← conjugate_residual_norm_sq τ hξ i (v i) (hv i)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hn i) 2
    have huv : u ^ 2 ≤ (v i) ^ 2 := pow_le_pow_left₀ hu.le (hvu i) 2
    have hd : 0 ≤ ‖ξ i‖ ^ 2 - (v i)⁻¹ := sub_nonneg.mpr (hl i)
    have hmult := mul_le_mul_of_nonneg_right huv hd
    rw [mul_comm ((u ^ 2)⁻¹), ← div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    have ha : (v i) ^ 2 * (v i)⁻¹ = v i := by
      rw [pow_two, mul_assoc, mul_inv_cancel₀ (hvp i).ne', mul_one]
    calc
      _ = u ^ 2 * (‖ξ i‖ ^ 2 - (v i)⁻¹) := mul_comm _ _
      _ ≤ (v i) ^ 2 * (‖ξ i‖ ^ 2 - (v i)⁻¹) := hmult
      _ = (v i) ^ 2 * ‖ξ i‖ ^ 2 - v i := by rw [mul_sub, ha]
      _ ≤ _ := hs
  constructor
  · exact sub_nonneg.mpr (Finset.sum_le_sum (fun i _ => hl i))
  · rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hi i

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem noiseWickIsometry_norm_sq {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (a : LabelHilbert.Space (List (Fin n))) :
    ‖noiseWickIsometry (B := B) (G := G) σ hσ a‖ ^ 2 = ∑' js, ‖a js‖ ^ 2 := by
  rw [LinearIsometry.norm_map]
  convert lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a using 1 <;> norm_cast

 theorem noiseWickIsometry_hasSum {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (a : LabelHilbert.Space (List (Fin n))) :
    HasSum (fun js => a js • (basis (noiseWord ((js.map σ).reverse)) : Space B N G))
      (noiseWickIsometry σ hσ a) := by
  simpa only [LinearIsometry.coe_toContinuousLinearMap, noiseWickIsometry_single] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) a).mapL
      (noiseWickIsometry (B := B) (G := G) σ hσ).toContinuousLinearMap

 theorem noiseWickIsometry_inner_hasSum {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (a : LabelHilbert.Space (List (Fin n)))
    (x : Space B N G) :
    HasSum (fun js => conj (a js) * inner ℂ (basis (noiseWord ((js.map σ).reverse))) x)
      (inner ℂ (noiseWickIsometry σ hσ a) x) := by
  have h := ((noiseWickIsometry_hasSum (B := B) (G := G) σ hσ a).mapL (innerSL ℂ x))
  have hc := Complex.hasSum_conj'.mpr h
  simpa only [innerSL_apply_apply, inner_smul_right, map_mul, inner_conj_symm] using hc

theorem wick_series_testing {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (a : LabelHilbert.Space (List (Fin n))) (w : List (Fin n)) :
    inner ℂ (noiseWickIsometry σ hσ a)
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      ∑' js, conj (a js) * (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
  have h := noiseWickIsometry_inner_hasSum σ hσ a
    (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
      (tracialVector B N G).vacuum)
  simp only [wick_testing J X hX σ hσ hs u, ← mul_assoc] at h
  exact h.tsum_eq.symm

 theorem fisher_wick_series_bound {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (hu : 0 < u)
    (ξ : Fin n → Space B N G)
    (hξ : ConjugateSystem (tracialVector B N G)
      (heatTuple X (fun k => semicircularN (σ k)) u) ξ)
    (v : Fin n → ℝ)
    (hv : ∀ i, ‖heatTuple X (fun k => semicircularN (σ k)) u i
      (tracialVector B N G).vacuum‖ ^ 2 = v i)
    (hvu : ∀ i, u ≤ v i)
    (a : Fin n → LabelHilbert.Space (List (Fin n)))
    (hseries : ∀ i w,
      inner ℂ (heatTuple X (fun k => semicircularN (σ k)) u i
        (tracialVector B N G).vacuum)
        (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
          (tracialVector B N G).vacuum) -
        (v i : ℂ) * derivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) i w =
      ∑' js, conj (a i js) * (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w) :
    0 ≤ (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ∧
      (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ≤
        (u ^ 2)⁻¹ * ∑ i, ∑' js, ‖a i js‖ ^ 2 := by
  have hr (i : Fin n) (w : List (Fin n)) :=
    (hseries i w).trans (wick_series_testing J X hX σ hσ hs u (a i) w).symm
  simpa only [noiseWickIsometry_norm_sq] using
    fisher_residual_bound (tracialVector B N G) hξ v u hu hv hvu
      (fun i => noiseWickIsometry σ hσ (a i)) hr

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]
 theorem residual_heat (R : Series α) (v : α → ℝ) (u : ℝ) (i : α) :
    residual (R + (u : ℂ) • quadratic) (fun i => v i + u) i = residual R v i := by
  funext w
  simp only [residual, Pi.sub_apply, FreeSeries.deriv_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_add]
  have hq := congrFun (deriv_quadratic (α := α) i) w
  change quadratic (i::w) = letter i w at hq
  rw [hq]
  ring
 theorem cumulant_residual_identity (M : Series α) (hM : M [] = 1) (v : α → ℝ) (i : α) :
    conv M (subst M (residual (cumulants M) v i)) =
      FreeSeries.deriv i M - (v i : ℂ) • conv M (subst M (letter i)) := by
  rw [residual, subst_sub, subst_smul, conv_sub_right, conv_smul_right]
  congr 1
  have he := congrArg (FreeSeries.deriv i) (cumulants_equation hM)
  have he' : FreeSeries.deriv i M = FreeSeries.deriv i (subst M (cumulants M)) := by
    funext w
    simpa only [FreeSeries.deriv_apply, Pi.add_apply, unit_cons, zero_add] using congrFun he w
  rw [he', deriv_subst]
end FreeSeries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem series_reverseDerivative_hasSum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (f : Series (Fin n)) (w : List (Fin n)) :
    HasSum (fun js => f js.reverse * reverseDerivativeMoment τ X js w)
      (conv (wordMoment τ X) (subst (wordMoment τ X) f) w) := by
  let F : List (Fin n) → ℂ := fun js => f js *
    conv (wordMoment τ X) (subst (wordMoment τ X) (monomial js)) w
  have hs : HasSum (F ∘ (reverseEquiv (α := Fin n)))
      (conv (wordMoment τ X) (subst (wordMoment τ X) f) w) :=
    (reverseEquiv (α := Fin n)).hasSum_iff.mpr (conv_subst_hasSum (wordMoment τ X) f w)
  apply hs.congr_fun
  intro js
  change f js.reverse * reverseDerivativeMoment τ X js w =
    f js.reverse * conv (wordMoment τ X)
      (subst (wordMoment τ X) (monomial js.reverse)) w
  rw [reverseDerivativeMoment_monomial]
 theorem inner_selfAdjoint_word {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) = wordMoment τ X (i::w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (hX i).star_eq]
  rfl
 theorem cumulant_residual_hasSum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i))
    (v : Fin n → ℝ) (i : Fin n) (w : List (Fin n)) :
    HasSum (fun js => residual (cumulants (wordMoment τ X)) v i js.reverse *
      reverseDerivativeMoment τ X js w)
      (inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) -
        (v i : ℂ) * derivativeMoment τ X i w) := by
  have hs := series_reverseDerivative_hasSum τ X (residual (cumulants (wordMoment τ X)) v i) w
  rw [cumulant_residual_identity _ (by simp), Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, FreeSeries.deriv_apply, ← derivativeMoment_series, ← inner_selfAdjoint_word τ X hX] at hs
  exact hs

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}

 theorem heat_cumulant_residual_hasSum (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (hsa : ∀ i, IsSelfAdjoint (X i))
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) (v : Fin n → ℝ) (i : Fin n) (w : List (Fin n)) :
    HasSum (fun js => residual (cumulants (wordMoment (tracialVector B N G) X)) v i js.reverse *
      reverseDerivativeMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) js w)
      (inner ℂ (heatTuple X (fun i => semicircularN (σ i)) u i (tracialVector B N G).vacuum)
        (wordEval (heatTuple X (fun i => semicircularN (σ i)) u) w (tracialVector B N G).vacuum) -
        ((v i + u : ℝ) : ℂ) * derivativeMoment (tracialVector B N G)
          (heatTuple X (fun i => semicircularN (σ i)) u) i w) := by
  have he := cumulant_residual_hasSum (tracialVector B N G)
    (heatTuple X (fun i => semicircularN (σ i)) u)
    (heatTuple_selfAdjoint X _ hsa (fun i => semicircularN_selfAdjoint _) u)
    (fun i => v i + u) i w
  rw [heat_cumulants J X hX σ hσ hs u hu] at he
  simp only [residual_heat] at he
  exact he
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TwoNoiseFisher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_sq_sqrt_pair [CompleteSpace H] {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = 0) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(Real.sqrt a : ℂ) • x + (Real.sqrt b : ℂ) • y‖ ^ 2 = a + b := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, hxy]
  simp [norm_smul, hx, hy,
    Real.norm_eq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb,
    abs_of_nonneg (Real.sqrt_nonneg a), abs_of_nonneg (Real.sqrt_nonneg b)]

end General

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem noise_basis_test {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (basis (noiseWord [σ i]))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) * derivativeMoment (tracialVector B N G)
        (heatTuple X (fun k => semicircularN (σ k)) u) i w := by
  simpa only [List.map_cons, List.map_nil, List.reverse_singleton, List.length_singleton, pow_one,
    reverseDerivativeMoment, derivativeMoment] using wick_testing J X hX σ hσ hs u [i] w

 theorem semicircularN_vacuum (i : N) :
    semicircularN i (tracialVector B N G).vacuum = basis (noiseWord [i]) := by
  simp [semicircularN, tracialVector, basis, creationN_single, annihilationN_single,
    removeN, empty, noiseWord_cons, noiseWord_nil]
end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem noiseVector₀_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₀ p i‖ = 1 := by
  simp [noiseVector₀, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]

omit [NeZero p] in
theorem noiseVector₁_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₁ p i‖ = 1 := by
  simp [noiseVector₁, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]
 theorem noiseVector_orthogonal (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (noiseVector₁ p j) = 0 := by
  have hneq : [initialIndex p i] ≠ [auxiliaryIndex p j] := by
    intro he
    have he' : initialIndex p i = auxiliaryIndex p j := List.cons.inj he |>.1
    exact auxiliaryIndex_fresh p j ⟨i,he'⟩
  exact noise_basis_orthonormal.inner_eq_zero hneq

 theorem noiseVector₀_C (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₀] using ht
 theorem noiseVector₁_C (i j : Fin (p+1)) : inner ℂ (noiseVector₁ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (auxiliaryIndex p)
    (auxiliaryIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₁] using ht

 theorem doublyNoised_vacuum (h s : ℝ) (i : Fin (p+1)) :
    doublyNoised p h s i (τ p).vacuum = C p i (τ p).vacuum +
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) := by
  change (C p i (τ p).vacuum + (Real.sqrt h : ℂ) •
    semicircularN (initialIndex p i) (τ p).vacuum) +
    (Real.sqrt s : ℂ) • semicircularN (auxiliaryIndex p i) (τ p).vacuum = _
  rw [semicircularN_vacuum, semicircularN_vacuum]
  simp only [noiseVector₀, noiseVector₁, add_assoc]

 theorem doublyNoised_variance (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (i : Fin (p+1)) :
    ‖doublyNoised p h s i (τ p).vacuum‖ ^ 2 = ‖C p i (τ p).vacuum‖ ^ 2 + h+s := by
  have hc : inner ℂ (C p i (τ p).vacuum)
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) = 0 := by
    rw [← inner_conj_symm, inner_add_left, inner_smul_left, inner_smul_left,
      noiseVector₀_C, noiseVector₁_C]
    simp
  rw [doublyNoised_vacuum, norm_add_sq (𝕜 := ℂ), hc,
    norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs]
  simp
  ring

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem cumulants_one [DecidableEq α] (M : Series α) (hM : M [] = 1) (i : α) :
    cumulants M [i] = M [i] := by
  have he := congrFun (cumulants_equation hM) [i]
  simpa [subst_cons, hM, conv_nil] using he.symm
 theorem cumulants_two (M : Series α) (hM : M [] = 1) (i j : α) :
    cumulants M [i,j] = M [i,j] - M [i] * M [j] := by
  have he := congrFun (cumulants_equation hM) [i,j]
  simp only [Pi.add_apply, unit_cons, zero_add, subst_cons, conv_cons, hM, one_mul,
    subst_nil, conv_nil, FreeSeries.deriv_apply] at he
  rw [cumulants_one M hM i] at he
  linear_combination -he
 theorem residual_short {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (i : α) (w : List α) (hw : w.length < 2) : residual R v i w = 0 := by
  cases w with
  | nil => simp [residual, hc]
  | cons j w =>
    have : w = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hw; omega)
    subst w
    simp [residual, hv, letter]
 theorem residual_long (R : Series α) (v : α → ℝ) (i : α) (w : List α) (hw : 2 ≤ w.length) :
    residual R v i w = R (i::w) := by
  cases w with
  | nil => simp at hw
  | cons j w =>
    cases w with
    | nil => simp at hw
    | cons k w => simp [residual, letter]
end FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem variance_nonneg (i : Fin (p+1)) : 0 ≤ variance p i := sq_nonneg _

omit [NeZero p] in
theorem fockMoments_one [NeZero p] (i : Fin p) : fockMoments p [i] = 0 := by
  have he := congrFun (fockMoments_eq p) [i]
  simpa [subst_cons, conv_nil, quadratic] using he

omit [NeZero p] in
theorem fockMoments_two [NeZero p] (i j : Fin p) : fockMoments p [i,j] = if j=i then 1 else 0 := by
  have he := congrFun (fockMoments_eq p) [i,j]
  simp only [Pi.add_apply, unit_cons, zero_add, subst_cons, conv_cons, subst_nil, conv_nil,
    FreeSeries.deriv_apply, quadratic] at he
  simpa [fockMoments] using he
 theorem C_centered (hp : 2 ≤ p) (i : Fin (p+1)) : signalMoments p [i] = 0 := by
  induction i using Fin.lastCases with
  | last =>
    simpa [signalMoments, wordMoment, wordEval] using
      (trace_equidiscreteSignal (B := Fin p) (N := Fin ((p+1)+(p+1))) p hp)
  | cast i =>
    have he := signal_option_moments p [some i]
    simpa [fockMoments_one] using he
 theorem C_offDiagonal (i j : Fin (p+1)) (hij : j ≠ i) : signalMoments p [i,j] = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      have he := signal_option_moments p [none, some j]
      simpa [fockMoments_one] using he
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      have he := signal_option_moments p [some i, none]
      simpa [fockMoments_one] using he
    | cast j =>
      have hj : j ≠ i := fun h => hij (congrArg Fin.castSucc h)
      have he := signal_option_moments p [some i, some j]
      simpa [fockMoments_two, hj] using he
 theorem C_covariance (i j : Fin (p+1)) :
    signalMoments p [i,j] = if j=i then (variance p i : ℂ) else 0 := by
  by_cases hj : j=i
  · subst j
    rw [ite_eq_left rfl]
    have he := inner_selfAdjoint_word (τ p) (C p) (C_selfAdjoint p) i [i]
    simpa [signalMoments, wordEval, variance, inner_self_eq_norm_sq_to_K] using he.symm
  · rw [ite_eq_right hj]; exact C_offDiagonal p i j hj
 theorem signalCumulants_centered (hp : 2 ≤ p) (i : Fin (p+1)) :
    cumulants (signalMoments p) [i] = 0 := by
  rw [cumulants_one _ (by simp [signalMoments]), C_centered p hp]
 theorem signalCumulants_covariance (hp : 2 ≤ p) (i j : Fin (p+1)) :
    cumulants (signalMoments p) [i,j] = if j=i then (variance p i : ℂ) else 0 := by
  rw [cumulants_two _ (by simp [signalMoments]), C_centered p hp, zero_mul, sub_zero, C_covariance]
 theorem variance_last_le_one (hp : 2 ≤ p) : variance p (Fin.last p) ≤ 1 := by
  have he := (C p (Fin.last p)).le_opNorm (τ p).vacuum
  rw [(τ p).norm_vacuum, mul_one, C_last] at he
  have hn := equidiscreteSignal_norm_le (B := Fin p) (N := Fin ((p+1)+(p+1))) p hp
  unfold variance
  rw [C_last]
  nlinarith [norm_nonneg (equidiscreteSignal p (τ p).vacuum)]
 theorem variance_castSucc (i : Fin p) : variance p i.castSucc = 1 := by
  have he := C_covariance p i.castSucc i.castSucc
  have ht := signal_option_moments p [some i,some i]
  simp only [List.map_cons, List.map_nil, optionFin_some, List.filterMap_cons, List.filterMap_nil,
    id_eq, fockMoments_two, ite_true] at ht
  simp at ht
  rw [ite_eq_left rfl, ht] at he
  exact_mod_cast he.symm
 theorem variance_le_one (hp : 2 ≤ p) (i : Fin (p+1)) : variance p i ≤ 1 := by
  induction i using Fin.lastCases with
  | last => exact variance_last_le_one p hp
  | cast i => rw [variance_castSucc]
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [Fintype α]

 theorem summable_words_iff (f : List α → ℝ) (hf : ∀ w, 0 ≤ f w) :
    Summable f ↔ Summable (fun n => ∑ v : List.Vector α n, f v.val) := by
  rw [← (wordSigma (α := α)).summable_iff]
  change Summable (fun v : Σ n : ℕ, List.Vector α n => f v.2.val) ↔ _
  have he := summable_sigma_of_nonneg
    (f := fun v : Σ n : ℕ, List.Vector α n => f v.2.val) (fun v => hf v.2.val)
  simpa only [tsum_fintype, and_iff_right (fun n => (hasSum_fintype (fun v : List.Vector α n => f v.val)).summable)] using he
 theorem tsum_words_degree (f : List α → ℝ) (hf : Summable f) :
    ∑' w, f w = ∑' n, ∑ v : List.Vector α n, f v.val := by
  have hs : Summable (fun v : Σ n : ℕ, List.Vector α n => f v.2.val) :=
    (wordSigma (α := α)).summable_iff.mpr hf
  calc
    ∑' w, f w = ∑' v : Σ n : ℕ, List.Vector α n, f v.2.val :=
      ((wordSigma (α := α)).tsum_eq f).symm
    _ = ∑' n, ∑' v : List.Vector α n, f v.val := hs.tsum_sigma
    _ = _ := by simp only [tsum_fintype]
 theorem summable_norm_sq_iff (f : Series α) :
    Summable (fun w => ‖f w‖ ^ 2) ↔ Summable (fun n => degreeNorm f n ^ 2) := by
  rw [summable_words_iff _ (fun w => sq_nonneg _)]
  simp only [degreeNorm_sq]
 theorem tsum_norm_sq_degree (f : Series α) (hf : Summable (fun w => ‖f w‖^2)) :
    ∑' w, ‖f w‖^2 = ∑' n, degreeNorm f n ^ 2 := by
  rw [tsum_words_degree _ hf]
  simp only [degreeNorm_sq]
end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
theorem degreeNorm_reverse [DecidableEq α] (f : Series α) (d : ℕ) : degreeNorm (fun w => f w.reverse) d = degreeNorm f d := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  rw [degreeNorm_sq, degreeNorm_sq]
  exact (vectorReverse (α := α) d).sum_comp (fun v => ‖f v.val‖^2)

omit [DecidableEq α] in
theorem degreeNorm_conj [DecidableEq α] (f : Series α) (d : ℕ) : degreeNorm (fun w => conj (f w)) d = degreeNorm f d := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  simp [degreeNorm_sq]

omit [DecidableEq α] [Fintype α] in
theorem wickCoefficients_cancel [DecidableEq α] [Fintype α] (f : Series α) (u : ℝ) (hu : 0 < u) (js : List α) :
    conj (wickCoefficients f u js) * (Real.sqrt u : ℂ)^js.length = f js.reverse := by
  have hr : (Real.sqrt u : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hu).ne'
  simp [wickCoefficients, hr]
 theorem wickCoefficients_degree_sq (f : Series α) (u : ℝ) (hu : 0 ≤ u) (d : ℕ) :
    degreeNorm (wickCoefficients f u) d ^ 2 = u⁻¹^d * degreeNorm f d ^ 2 := by
  have he : degreeNorm (wickCoefficients f u) d =
      degreeNorm ((Real.sqrt u : ℂ)⁻¹^d • (fun w => conj (f w.reverse) : Series α)) d := by
    apply degreeNorm_congr
    intro w hw
    simp [wickCoefficients, hw, div_eq_mul_inv, mul_comm]
  rw [he, degreeNorm_smul, degreeNorm_conj, degreeNorm_reverse, mul_pow]
  congr 1
  have hsq : (Real.sqrt u ^ d)^2 = u^d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul, Real.sq_sqrt hu]
  simp [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u), hsq]
 theorem residual_degree (R : Series α) (v : α → ℝ) (i : α) (d : ℕ) (hd : 2 ≤ d) :
    degreeNorm (residual R v i) d = degreeNorm (FreeSeries.deriv i R) d := by
  apply degreeNorm_congr
  intro w hw
  exact residual_long R v i w (by omega)
 theorem residual_degree_short {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (i : α) (d : ℕ) (hd : d < 2) : degreeNorm (residual R v i) d = 0 := by
  apply (degreeNorm_congr (g := 0) d ?_).trans (degreeNorm_zero d)
  intro w hw
  exact residual_short hc hv i w (by omega)
 theorem residual_degree_sum {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0) (d : ℕ) :
    ∑ i : α, degreeNorm (residual R v i) d ^ 2 =
      if 2 ≤ d then degreeNorm R (d+1)^2 else 0 := by
  by_cases hd : 2 ≤ d
  · simp only [ite_eq_left hd, residual_degree R v _ _ hd]
    exact (degreeNorm_succ_sq R d).symm
  · have hz (i : α) : degreeNorm (residual R v i) d = 0 :=
      residual_degree_short hc hv i d (by omega)
    simp [hd, hz]
 theorem wickCoefficients_degree_sum {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (u : ℝ) (hu : 0 ≤ u) (d : ℕ) :
    ∑ i : α, degreeNorm (wickCoefficients (residual R v i) u) d^2 =
      if 2 ≤ d then u⁻¹^d * degreeNorm R (d+1)^2 else 0 := by
  simp_rw [wickCoefficients_degree_sq _ u hu]
  rw [← mul_sum, residual_degree_sum hc hv]
  split_ifs <;> simp
end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GeometricTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset

 theorem geometricCumulantTail_factor (K u : ℝ) (k : ℕ) :
    u⁻¹^k * K^(2*(k+1)) = K^2 * (K^2/u)^k := by
  rw [Nat.mul_add, pow_add, pow_mul, div_pow, div_eq_mul_inv, inv_pow]
  ring
 theorem geometricCumulantTail_shift (K u : ℝ) (k : ℕ) :
    geometricCumulantTail K u (k+2) = (K^6/u^2) * (K^2/u)^k := by
  rw [geometricCumulantTail, ite_eq_left (by omega), geometricCumulantTail_factor, pow_add]
  rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]
  ring
 theorem geometricCumulantTail_summable {K u : ℝ} (hu : 0 < u) (hk : K^2 < u) :
    Summable (geometricCumulantTail K u) := by
  have hr : ‖K^2/u‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hu.le)]
    exact (div_lt_one hu).mpr hk
  apply (summable_nat_add_iff 2).mp
  simp_rw [geometricCumulantTail_shift]
  exact (summable_geometric_of_norm_lt_one hr).mul_left _
 theorem geometricCumulantTail_tsum {K u : ℝ} (hu : 0 < u) (hk : K^2 < u) :
    ∑' k, geometricCumulantTail K u k = (K^6/u^2) * (1-K^2/u)⁻¹ := by
  have hh := geometricCumulantTail_summable hu hk
  have hr : ‖K^2/u‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hu.le)]
    exact (div_lt_one hu).mpr hk
  rw [← hh.sum_add_tsum_nat_add 2]
  have hz : ∑ i ∈ range 2, geometricCumulantTail K u i = 0 := by
    norm_num [sum_range_succ, geometricCumulantTail]
  rw [hz, zero_add]
  simp_rw [geometricCumulantTail_shift]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
 theorem geometricCumulantTail_le {K u : ℝ} (hu : 0 < u) (hk : 2*K^2 ≤ u) :
    ∑' k, geometricCumulantTail K u k ≤ 2*K^6/u^2 := by
  have hk' : K^2 < u := by nlinarith [sq_nonneg K]
  rw [geometricCumulantTail_tsum hu hk']
  have hr : K^2/u ≤ 1/2 := (div_le_iff₀ hu).mpr (by linarith)
  have hd : 0 < 1 - K^2/u := by linarith
  have hi : (1-K^2/u)⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hd).mpr (by linarith)
  calc
    _ ≤ (K^6/u^2) * 2 := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

 theorem wick_degree_bound {R : Series α} {v : α → ℝ} {K u : ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (_hK : 0 ≤ K) (hR : ∀ m, degreeNorm R m ≤ K^m) (hu : 0 ≤ u) (d : ℕ) :
    ∑ i : α, degreeNorm (wickCoefficients (residual R v i) u) d ^ 2 ≤
      geometricCumulantTail K u d := by
  rw [wickCoefficients_degree_sum hc hv u hu d, geometricCumulantTail]
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      degreeNorm R (d+1)^2 ≤ (K^(d+1))^2 :=
        pow_le_pow_left₀ (degreeNorm_nonneg _ _) (hR _) _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  · rfl
 theorem wickCoefficient_summable {R : Series α} {v : α → ℝ} {K u : ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (hK : 0 ≤ K) (hR : ∀ m, degreeNorm R m ≤ K^m) (hu : 0 < u) (hKu : K^2 < u)
    (i : α) : Summable (fun js => ‖wickCoefficients (residual R v i) u js‖^2) := by
  apply (summable_norm_sq_iff _).mpr
  apply Summable.of_nonneg_of_le (fun d => sq_nonneg _) _ (geometricCumulantTail_summable hu hKu)
  intro d
  exact (single_le_sum (fun j _ => sq_nonneg (degreeNorm (wickCoefficients (residual R v j) u) d))
    (mem_univ i)).trans (wick_degree_bound hc hv hK hR hu.le d)
 theorem wickCoefficient_total_bound {R : Series α} {v : α → ℝ} {K u : ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (hK : 0 ≤ K) (hR : ∀ m, degreeNorm R m ≤ K^m) (hu : 0 < u) (hKu : 2*K^2 ≤ u) :
    ∑ i : α, ∑' js, ‖wickCoefficients (residual R v i) u js‖^2 ≤ 2*K^6/u^2 := by
  have hKu' : K^2 < u := by nlinarith [sq_nonneg K]
  have hs (i : α) := wickCoefficient_summable hc hv hK hR hu hKu' i
  have hd (i : α) := (summable_norm_sq_iff _).mp (hs i)
  have hsum := hasSum_sum (s := (univ : Finset α)) (fun i _ => (hd i).hasSum)
  simp_rw [tsum_norm_sq_degree _ (hs _)]
  rw [← hsum.tsum_eq]
  exact (hsum.summable.tsum_le_tsum (fun d => wick_degree_bound hc hv hK hR hu.le d)
    (geometricCumulantTail_summable hu hKu')).trans (geometricCumulantTail_le hu hKu)
end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

theorem fisher_cumulant_deficit {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (hsa : ∀ i, IsSelfAdjoint (X i))
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hc : ∀ i, cumulants (wordMoment (tracialVector B N G) X) [i] = 0)
    (hcov : ∀ i j, cumulants (wordMoment (tracialVector B N G) X) [i,j] =
      if j=i then (v i : ℂ) else 0)
    (K u : ℝ) (hK : 0 ≤ K) (hu : 0 < u) (hKu : 2*K^2 ≤ u)
    (hR : ∀ m, degreeNorm (cumulants (wordMoment (tracialVector B N G) X)) m ≤ K^m)
    (hvar : ∀ i, ‖heatTuple X (fun k => semicircularN (σ k)) u i
      (tracialVector B N G).vacuum‖^2 = v i + u) :
    0 ≤ (freeFisher (tracialVector B N G) (heatTuple X (fun k => semicircularN (σ k)) u)).toReal -
      ∑ i, (v i + u)⁻¹ ∧
    (freeFisher (tracialVector B N G) (heatTuple X (fun k => semicircularN (σ k)) u)).toReal -
      ∑ i, (v i + u)⁻¹ ≤ 2*K^6/u^4 := by
  let R := cumulants (wordMoment (tracialVector B N G) X)
  let a : Fin n → List (Fin n) → ℂ := fun i => wickCoefficients (residual R v i) u
  have hKu' : K^2 < u := by nlinarith [sq_nonneg K]
  have ha (i : Fin n) : Summable (fun js => ‖a i js‖^2) :=
    wickCoefficient_summable hc hcov hK hR hu hKu' i
  let av : Fin n → LabelHilbert.Space (List (Fin n)) := fun i => wickCoefficientVector (a i) (ha i)
  obtain ⟨ξ,hξ⟩ := heat_conjugates_exist J X hX σ hσ hs u hu
  have ht (i : Fin n) (w : List (Fin n)) :=
    heat_cumulant_residual_hasSum J X hX hsa σ hσ hs u hu.le v i w
  have he (i : Fin n) (w : List (Fin n)) :
      inner ℂ (heatTuple X (fun k => semicircularN (σ k)) u i (tracialVector B N G).vacuum)
        (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w (tracialVector B N G).vacuum) -
      ((v i + u : ℝ) : ℂ) * derivativeMoment (tracialVector B N G)
        (heatTuple X (fun k => semicircularN (σ k)) u) i w =
      ∑' js, conj (av i js) * (Real.sqrt u : ℂ)^js.length * reverseDerivativeMoment
        (tracialVector B N G) (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
    change _ = ∑' js, conj (wickCoefficients (residual R v i) u js) *
      (Real.sqrt u : ℂ)^js.length * _
    simp_rw [wickCoefficients_cancel _ u hu]
    exact (ht i w).tsum_eq.symm
  have hb := fisher_wick_series_bound J X hX σ hσ hs u hu ξ hξ
    (fun i => v i + u) hvar (fun i => by linarith [hv i]) av he
  have hf : (freeFisher (tracialVector B N G)
      (heatTuple X (fun k => semicircularN (σ k)) u)).toReal = ∑ i, ‖ξ i‖^2 := by
    rw [freeFisher_eq_of_conjugate _ hξ, ENNReal.toReal_ofReal (sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [hf]
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hb' : ∑ i, ∑' js, ‖av i js‖^2 ≤ 2*K^6/u^2 :=
    wickCoefficient_total_bound hc hcov hK hR hu hKu
  calc
    _ ≤ (u^2)⁻¹ * (2*K^6/u^2) := mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by rw [show u^4 = u^2*u^2 by ring]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem X_variance (u : ℝ) (hu : 0 ≤ u) (i : Fin (p+1)) :
    ‖X p u i (τ p).vacuum‖^2 = variance p i + u := by
  simpa [doublyNoised, heatTuple, variance] using doublyNoised_variance p u 0 hu (le_refl 0) i
 theorem fisherDeficit_bounds (hp : 2 ≤ p) (u : ℝ) (hu : 0 < u)
    (hKu : 2*(cumulantConstant p)^2 ≤ u) :
    0 ≤ fisherDeficit p u ∧ fisherDeficit p u ≤ 2*(cumulantConstant p)^6/u^4 :=
  fisher_cumulant_deficit ∅ (C p) (C_mem_background p ∅) (C_selfAdjoint p)
    (initialIndex p) (initialIndex_injective p) (by simp)
    (variance p) (variance_nonneg p) (signalCumulants_centered p hp) (signalCumulants_covariance p hp)
    (cumulantConstant p) u (by dsimp [cumulantConstant]; positivity) hu hKu
    (signalCumulants_norm_le p hp) (X_variance p u hu.le)
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set
namespace FiniteEntropySeparation

 theorem logarithmicPrimitive_deriv {a : ℝ} (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (logarithmicPrimitive a) (reciprocalDifference a s) s := by
  unfold logarithmicPrimitive reciprocalDifference
  have h1 : 1+s ≠ 0 := by linarith
  have h2 : a+s ≠ 0 := by linarith
  convert (((hasDerivAt_id s).const_add 1).log h1).sub (((hasDerivAt_id s).const_add a).log h2) using 1
  all_goals rfl

 theorem logarithmicPrimitive_atTop (a : ℝ) :
    Tendsto (logarithmicPrimitive a) atTop (𝓝 0) := by
  have h := (Real.tendsto_log_comp_add_sub_log 1).sub (Real.tendsto_log_comp_add_sub_log a)
  unfold logarithmicPrimitive
  convert h using 1 <;> simp [add_comm, sub_sub_sub_cancel_right]

 theorem reciprocalDifference_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (reciprocalDifference a) (Ioi 0) := by
  by_cases ha1 : 1 ≤ a
  · apply integrableOn_Ioi_deriv_of_nonneg' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (fun s hs => ?_) (logarithmicPrimitive_atTop a)
    have hs : 0 < s := hs
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by linarith : 0 < 1+s)
    linarith
  · apply integrableOn_Ioi_deriv_of_nonpos' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (fun s hs => ?_) (logarithmicPrimitive_atTop a)
    have hs : 0 < s := hs
    apply sub_nonpos.mpr
    apply one_div_le_one_div_of_le (by linarith : 0 < a+s)
    linarith

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem heatFisher_ne_top (u : ℝ) (hu : 0 < u) : freeFisher (τ p) (X p u) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (heat_freeFisher_le ∅ (C p) (C_mem_background p ∅) (initialIndex p)
      (initialIndex_injective p) (by simp) u hu)
 theorem heatFisherReal_upper (u : ℝ) (hu : 0 < u) : heatFisherReal p u ≤ (p+1 : ℕ)/u := by
  have he := heat_freeFisher_le ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) u hu
  exact (ENNReal.toReal_le_toReal (heatFisher_ne_top p u hu) ENNReal.ofReal_ne_top).mpr he |>.trans_eq
    (ENNReal.toReal_ofReal (by positivity))
 theorem heatFisherReal_lower (u : ℝ) (hu : 0 < u) : covarianceFisher p u ≤ heatFisherReal p u := by
  obtain ⟨ξ,hξ⟩ := heat_conjugates_exist ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) u hu
  change ConjugateSystem (τ p) (X p u) ξ at hξ
  unfold heatFisherReal
  rw [freeFisher_eq_of_conjugate _ hξ, ENNReal.toReal_ofReal (sum_nonneg (fun _ _ => sq_nonneg _))]
  apply sum_le_sum
  intro i _
  simpa only [X_variance p u hu.le, one_div] using conjugate_norm_sq_lower (τ p) hξ i
 theorem heatFisherReal_measurable : Measurable (fun u : Ioi (0 : ℝ) => heatFisherReal p u) :=
  ENNReal.measurable_toReal.comp (heat_freeFisher_measurable ∅ (C p) (C_mem_background p ∅)
    (initialIndex p) (initialIndex_injective p) (by simp))
 theorem heatFisherReal_shift_aesm (a : ℝ) (ha : 0 < a) :
    AEStronglyMeasurable (fun s => heatFisherReal p (a+s)) (volume.restrict (Ioi 0)) := by
  let g : ℝ → Ioi (0 : ℝ) := fun s => ⟨a+max s 0, by exact lt_of_lt_of_le ha (le_add_of_nonneg_right (le_max_right s 0))⟩
  have hg : Continuous g := by continuity
  have hm := ((heatFisherReal_measurable p).comp hg.measurable).aestronglyMeasurable (μ := volume.restrict (Ioi 0))
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change heatFisherReal p (a+max s 0) = _
  rw [max_eq_left (le_of_lt hs)]
 theorem heatFisherReal_broad_lower (hp : 2 ≤ p) (u : ℝ) (hu : 0 < u) :
    (p+1 : ℕ)/(u+4) ≤ heatFisherReal p u := by
  apply le_trans _ (heatFisherReal_lower p u hu)
  have he (i : Fin (p+1)) : 1/(u+4) ≤ (variance p i+u)⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith [variance_nonneg p i])
      (by linarith [variance_le_one p hp i])
  simpa [covarianceFisher, div_eq_mul_inv] using sum_le_sum (s := (univ : Finset (Fin (p+1)))) (fun i _ => he i)
 theorem entropyIntegrand_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun s : ℝ => (p+1 : ℕ)/(1+s)) (volume.restrict (Ioi 0)) := by
    exact (by fun_prop : Measurable (fun s : ℝ => (p+1 : ℕ)/(1+s))).aestronglyMeasurable
  apply integrable_of_le_of_le (hm.sub (heatFisherReal_shift_aesm p a ha))
    (g₁ := fun s => (p+1 : ℕ) * reciprocalDifference a s)
    (g₂ := fun s => (p+1 : ℕ) * reciprocalDifference (a+4) s)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have he := heatFisherReal_upper p (a+s) (by linarith [show 0<s from hs])
    dsimp [reciprocalDifference]
    simp only [mul_sub, mul_one_div]
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have he := heatFisherReal_broad_lower p hp (a+s) (by linarith [show 0<s from hs])
    dsimp [reciprocalDifference]
    simp only [mul_sub, mul_one_div]
    convert sub_le_sub_left he ((p+1 : ℕ)/(1+s)) using 1 ; congr 2 ; ring
  · exact (reciprocalDifference_integrable ha).const_mul _
  · exact (reciprocalDifference_integrable (by linarith : 0 < a+4)).const_mul _
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation

namespace Model
variable (p : ℕ) [NeZero p]

 theorem covarianceCorrection_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => ∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) (Ioi 0) :=
  integrable_finsetSum _ (fun i _ => reciprocalDifference_integrable (by linarith [variance_nonneg p i]))
 theorem covarianceCorrection_identity (a s : ℝ) :
    (∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) -
      ((p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) = fisherDeficit p (a+s) := by
  simp only [reciprocalDifference, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [fisherDeficit, covarianceFisher, heatFisherReal, one_div]
  have he : (∑ i : Fin (p+1), (a+variance p i+s)⁻¹) = ∑ i : Fin (p+1), (variance p i+(a+s))⁻¹ := by
    apply sum_congr rfl; intro i _; congr 1; ring
  rw [he]
  simp only [div_eq_mul_inv]
  ring
 theorem fisherDeficit_shift_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => fisherDeficit p (a+s)) (Ioi 0) := by
  have hh := (covarianceCorrection_integrable p a ha).sub (entropyIntegrand_integrable p hp a ha)
  change IntegrableOn (fun s => (∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) -
    ((p+1 : ℕ)/(1+s) - heatFisherReal p (a+s))) (Ioi 0) at hh
  simpa only [covarianceCorrection_identity] using hh
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.RealTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
namespace FiniteEntropySeparation
 theorem integrableOn_Ioi_translate {f : ℝ → ℝ} (a : ℝ) :
    IntegrableOn (fun s => f (a+s)) (Ioi 0) ↔ IntegrableOn f (Ioi a) := by
  have he : (fun s : ℝ => a+s) ⁻¹' Ioi a = Ioi 0 := by ext s; simp
  simpa only [he, Function.comp_def] using
    (measurePreserving_add_left volume a).integrableOn_comp_preimage (measurableEmbedding_addLeft a)
      (f := f) (s := Ioi a)
 theorem inverseFourth_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => 1/u^4) (Ioi a) := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) ha).congr_fun _ measurableSet_Ioi
  intro u hu
  norm_num
 theorem inverseFourth_integral {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi a, 1/u^4) = 1/(3*a^3) := by
  have he : (∫ u in Ioi a, 1/u^4) = ∫ u in Ioi a, u^(-4 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    norm_num
  rw [he, integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) ha]
  norm_num
  ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter Finset
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
theorem cumulantConstant_pos : 0 < cumulantConstant p := by
  unfold cumulantConstant
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos p))))
theorem fisherDeficit_tail_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fisherDeficit p) (Ioi a) :=
  (integrableOn_Ioi_translate a).mp (fisherDeficit_shift_integrable p hp a ha)
theorem fisherDeficit_tail_le (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (hKa : 2*(cumulantConstant p)^2 ≤ a) :
    (∫ u in Ioi a, fisherDeficit p u) ≤ 2*(cumulantConstant p)^6/(3*a^3) := by
  have hi := (inverseFourth_integrable ha).const_mul (2*(cumulantConstant p)^6)
  have hle : (∫ u in Ioi a, fisherDeficit p u) ≤
      ∫ u in Ioi a, 2*(cumulantConstant p)^6 * (1/u^4) := by
    apply integral_mono_ae (fisherDeficit_tail_integrable p hp a ha) hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [mul_one_div] using
      (fisherDeficit_bounds p hp u (lt_trans ha hu) (hKa.trans hu.le)).2
  rw [integral_const_mul, inverseFourth_integral ha] at hle
  simpa only [mul_one_div] using hle
theorem entropy_deficit_le_oai (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (hKa : 2*(cumulantConstant p)^2 ≤ a) :
    (1/2 : ℝ) * (∫ u in Ioi a, fisherDeficit p u) ≤ 1/24 := by
  have hK := cumulantConstant_pos p
  have hb := fisherDeficit_tail_le p hp a ha hKa
  have hc : (2*(cumulantConstant p)^2)^3 ≤ a^3 := pow_le_pow_left₀ (by positivity) hKa 3
  have hd : 0 < 3*a^3 := by positivity
  have he : 2*(cumulantConstant p)^6/(3*a^3) ≤ 1/12 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [hc]
  linarith
end FiniteEntropySeparation.Model

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.Model.entropy_deficit_le_oai := @OAI.FiniteEntropySeparation.Model.entropy_deficit_le_oai
