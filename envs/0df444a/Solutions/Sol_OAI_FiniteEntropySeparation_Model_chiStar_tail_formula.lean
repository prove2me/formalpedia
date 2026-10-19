-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.Model.chiStar_tail_formula
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:12:00.066143+00:00
-- url     : https://prove2.me/submissions/a5db18c8-dc7a-4fd4-bdb8-a4a4d15d666d

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

 theorem freeFisher_lower_covariance {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) :
    ENNReal.ofReal (∑ i, 1 / ‖X i τ.vacuum‖ ^ 2) ≤ freeFisher τ X := by
  refine le_iInf fun ξ => le_iInf fun hξ => ?_
  apply ENNReal.ofReal_le_ofReal
  exact Finset.sum_le_sum fun i _ => conjugate_norm_sq_lower τ hξ i

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

 theorem conjugate_polynomial_pairing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) (p : WordPolynomial n) :
    inner ℂ (ξ i) (polynomialVector τ X p) = polynomialDerivative τ X i p := by
  simp only [polynomialVector, polynomialDerivative, Finsupp.linearCombination_apply,
    Finsupp.sum, inner_sum, inner_smul_right, (hξ i).2, smul_eq_mul]

theorem norm_sq_eq_iSup_dense {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (v : ι → H) (ξ : H)
    (hξ : ξ ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    ENNReal.ofReal (‖ξ‖ ^ 2) =
      ⨆ p : ι →₀ ℂ, ENNReal.ofReal
        (2 * (inner ℂ ξ (Finsupp.linearCombination ℂ v p)).re -
          ‖Finsupp.linearCombination ℂ v p‖ ^ 2) := by
  let Q : H → ℝ := fun z => 2 * (inner ℂ ξ z).re - ‖z‖ ^ 2
  have hQ : Continuous Q := by fun_prop
  let b := ⨆ p : ι →₀ ℂ, ENNReal.ofReal (Q (Finsupp.linearCombination ℂ v p))
  change ENNReal.ofReal (‖ξ‖ ^ 2) = b
  apply le_antisymm
  · have hc : IsClosed {z : H | ENNReal.ofReal (Q z) ≤ b} :=
      isClosed_le (ENNReal.continuous_ofReal.comp hQ) continuous_const
    have hs : (Submodule.span ℂ (Set.range v) : Set H) ⊆ {z | ENNReal.ofReal (Q z) ≤ b} := by
      intro z hz
      rw [← Finsupp.range_linearCombination] at hz
      obtain ⟨p,rfl⟩ := hz
      exact le_iSup (fun p : ι →₀ ℂ => ENNReal.ofReal (Q (Finsupp.linearCombination ℂ v p))) p
    have hh := hc.closure_subset_iff.mpr hs hξ
    have he : Q ξ = ‖ξ‖ ^ 2 := by
      have hself : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
      dsimp [Q]
      rw [hself]
      ring
    change ENNReal.ofReal (Q ξ) ≤ b at hh
    rwa [he] at hh
  · refine iSup_le fun p => ENNReal.ofReal_le_ofReal ?_
    have h := norm_sub_sq (𝕜 := ℂ) ξ (Finsupp.linearCombination ℂ v p)
    change ‖ξ - Finsupp.linearCombination ℂ v p‖ ^ 2 =
      ‖ξ‖ ^ 2 - 2 * (inner ℂ ξ (Finsupp.linearCombination ℂ v p)).re +
        ‖Finsupp.linearCombination ℂ v p‖ ^ 2 at h
    dsimp [Q]
    nlinarith [sq_nonneg ‖ξ - Finsupp.linearCombination ℂ v p‖]

 theorem freeFisher_variational {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ∑ i, ⨆ p : WordPolynomial n, ENNReal.ofReal (fisherTest τ X i p) := by
  rw [freeFisher_eq_of_conjugate τ hξ, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  have h := norm_sq_eq_iSup_dense (fun w => wordEval X w τ.vacuum) (ξ i) (hξ i).1
  change ENNReal.ofReal (‖ξ i‖ ^ 2) =
    ⨆ p : WordPolynomial n, ENNReal.ofReal
      (2 * (inner ℂ (ξ i) (polynomialVector τ X p)).re - ‖polynomialVector τ X p‖ ^ 2) at h
  simpa only [conjugate_polynomial_pairing τ hξ, fisherTest] using h

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

 theorem semicircularB_norm_le {B N G : Type} [Group G]
    [DecidableEq B] [DecidableEq N] [DecidableEq G] (b : B) : ‖semicircularB (N := N) (G := G) b‖ ≤ 2 := by
  have h : ‖creationB (N := N) (G := G) b‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  calc
    _ ≤ ‖creationB (N := N) (G := G) b‖ + ‖star (creationB b)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add h (by simpa [ContinuousLinearMap.star_eq_adjoint] using h)
    _ = 2 := by norm_num

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

 theorem wordEval_append {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ} (X : Fin n → H →L[ℂ] H) (u v : List (Fin n)) :
    wordEval X (u ++ v) = wordEval X u * wordEval X v := by
  simp [wordEval]

 theorem star_wordEval {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (w : List (Fin n)) :
    star (wordEval X w) = wordEval X w.reverse := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    simp only [wordEval, List.map_cons, List.prod_cons, star_mul, (hX i).star_eq,
      List.reverse_cons, List.map_append, List.prod_append, ] at *
    rw [ih]
    simp

 theorem inner_wordVector {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (u v : List (Fin n)) :
    inner ℂ (wordEval X u τ.vacuum) (wordEval X v τ.vacuum) =
      wordMoment τ X (u.reverse ++ v) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    star_wordEval X hX u]
  simp only [wordMoment, trace, wordEval_append, mul_apply_eq_comp]

theorem polynomialVector_norm_sq_eq_of_moments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hY : ∀ i, IsSelfAdjoint (Y i))
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w) (p : WordPolynomial n) :
    ‖polynomialVector τ X p‖ ^ 2 = ‖polynomialVector ρ Y p‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  simp only [polynomialVector, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_wordVector τ X hX,
    inner_wordVector ρ Y hY, hm]

 theorem derivativeMoment_eq_of_moments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w) (i : Fin n) (w : List (Fin n)) :
    derivativeMoment τ X i w = derivativeMoment ρ Y i w := by
  simp only [derivativeMoment, hm]

theorem freeFisher_eq_of_wordMoments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hY : ∀ i, IsSelfAdjoint (Y i))
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w)
    (heX : ∃ ξ, ConjugateSystem τ X ξ) (heY : ∃ ξ, ConjugateSystem ρ Y ξ) :
    freeFisher τ X = freeFisher ρ Y := by
  obtain ⟨ξ,hξ⟩ := heX
  obtain ⟨η,hη⟩ := heY
  rw [freeFisher_variational τ X hξ, freeFisher_variational ρ Y hη]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg iSup
  funext p
  apply congrArg ENNReal.ofReal
  unfold fisherTest
  rw [polynomialVector_norm_sq_eq_of_moments τ ρ X Y hX hY hm]
  congr 2
  simp only [polynomialDerivative, Finsupp.linearCombination_apply, Finsupp.sum,
    derivativeMoment_eq_of_moments τ ρ X Y hm]

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
 theorem semicircularN_mem_background (J : Set N) {i : N} (hi : i ∈ J) :
    semicircularN (B := B) (G := G) i ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inr ⟨i,hi,rfl⟩)

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

 theorem heatTuple_mem_background {n : ℕ} (J : Set N)
    (X S : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (hS : ∀ i, S i ∈ backgroundAlgebra J)
    (u : ℝ) (i : Fin n) : heatTuple X S u i ∈ backgroundAlgebra J :=
  (backgroundAlgebra J).add_mem (hX i) ((backgroundAlgebra J).smul_mem (hS i) _)

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

 theorem C_norm_le (hp : 2 ≤ p) (i : Fin (p+1)) : ‖C p i‖ ≤ 2 := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact (equidiscreteSignal_norm_le p hp).trans (by norm_num)
  | cast i => rw [C_castSucc]; exact semicircularB_norm_le i

 theorem X_mem_background (h : ℝ) (i : Fin (p+1)) :
    X p h i ∈ backgroundAlgebra (oldNoise p) := by
  apply heatTuple_mem_background _ _ _ (C_mem_background p (oldNoise p))
  intro j
  exact semicircularN_mem_background _ ⟨j,rfl⟩

 theorem X_selfAdjoint (h : ℝ) (i : Fin (p+1)) : IsSelfAdjoint (X p h i) :=
  heatTuple_selfAdjoint (C p) (initialNoise p) (C_selfAdjoint p)
    (fun _index => semicircularN_selfAdjoint _) h i

omit [NeZero p] in
theorem auxiliaryNoise_selfAdjoint [NeZero p] (i : Fin (p+1)) : IsSelfAdjoint (auxiliaryNoise p i) :=
  semicircularN_selfAdjoint _

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

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem inner_selfAdjoint_word {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) = wordMoment τ X (i::w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (hX i).star_eq]
  rfl
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

 theorem fisher_le_scaled_test {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (Z : Fin n → H →L[ℂ] H) (η : Fin n → H) (v : ℝ) (hv : 0 < v)
    (ht : ∀ i w, inner ℂ (η i) (wordEval Z w τ.vacuum) =
      (v : ℂ) * derivativeMoment τ Z i w)
    (hn : ∀ i, ‖η i‖ ^ 2 ≤ v) : freeFisher τ Z ≤ ENNReal.ofReal ((n : ℝ)/v) := by
  have ht' (i : Fin n) (w : List (Fin n)) :
      inner ℂ ((v⁻¹ : ℂ) • η i) (wordEval Z w τ.vacuum) = derivativeMoment τ Z i w := by
    rw [inner_smul_left, ht i w]
    simp [hv.ne']
  apply (freeFisher_le_testVectors τ Z (fun i => ((v⁻¹ : ℂ) • η i)) ht').trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∑ i, v⁻¹ ^ 2 * ‖η i‖ ^ 2 := by
      simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
    _ ≤ ∑ _i : Fin n, v⁻¹ ^ 2 * v := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hn i) (sq_nonneg _))
    _ = _ := by simp [pow_two, hv.ne', div_eq_mul_inv]

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

 theorem initialIndex_fresh (i : Fin (p+1)) : initialIndex p i ∉ Set.range (auxiliaryIndex p) := by
  rintro ⟨j,h⟩
  exact auxiliaryIndex_fresh p j ⟨i,h.symm⟩

 theorem doublyNoised_comm (h s : ℝ) : doublyNoised p h s =
    heatTuple (heatTuple (C p) (auxiliaryNoise p) s) (initialNoise p) h := by
  funext i
  simp only [doublyNoised, X, heatTuple]
  abel

 theorem auxiliaryBackground_mem (s : ℝ) (i : Fin (p+1)) :
    heatTuple (C p) (auxiliaryNoise p) s i ∈ backgroundAlgebra (Set.range (auxiliaryIndex p)) := by
  apply heatTuple_mem_background _ _ _ (C_mem_background p _)
  intro j
  exact semicircularN_mem_background _ ⟨j,rfl⟩

 theorem noiseVector₀_test (h s : ℝ) (i : Fin (p+1)) (w : List (Fin (p+1))) :
    inner ℂ (noiseVector₀ p i) (wordEval (doublyNoised p h s) w (τ p).vacuum) =
      (Real.sqrt h : ℂ) * derivativeMoment (τ p) (doublyNoised p h s) i w := by
  rw [doublyNoised_comm]
  exact noise_basis_test _ _ (auxiliaryBackground_mem p s)
    (initialIndex p) (initialIndex_injective p) (initialIndex_fresh p) h i w

 theorem noiseVector₁_test (h s : ℝ) (i : Fin (p+1)) (w : List (Fin (p+1))) :
    inner ℂ (noiseVector₁ p i) (wordEval (doublyNoised p h s) w (τ p).vacuum) =
      (Real.sqrt s : ℂ) * derivativeMoment (τ p) (doublyNoised p h s) i w :=
  noise_basis_test _ _ (X_mem_background p h)
    (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) s i w

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

theorem doublyNoised_fisher_le (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    freeFisher (τ p) (doublyNoised p h s) ≤ ENNReal.ofReal ((p+1 : ℕ)/(h+s)) := by
  let η : Fin (p+1) → H p := fun i => (Real.sqrt h : ℂ) • noiseVector₀ p i +
    (Real.sqrt s : ℂ) • noiseVector₁ p i
  apply fisher_le_scaled_test (τ p) _ η (h+s) hu
  · intro i w
    simp only [η, inner_add_left, inner_smul_left, Complex.conj_ofReal,
      noiseVector₀_test, noiseVector₁_test, ← mul_assoc, ← pow_two]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt hh, Real.sq_sqrt hs]
    push_cast
    ring
  · intro i
    exact (norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs).le

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

 theorem C_vacuum_norm_sq_le (hp : 2 ≤ p) (i : Fin (p+1)) :
    ‖C p i (τ p).vacuum‖ ^ 2 ≤ 4 := by
  have h := (C p i).le_opNorm (τ p).vacuum
  rw [(τ p).norm_vacuum] at h
  have h' := C_norm_le p hp i
  nlinarith [norm_nonneg (C p i (τ p).vacuum)]

 theorem doublyNoised_fisher_lower (hp : 2 ≤ p) (h s : ℝ)
    (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    ENNReal.ofReal ((p+1 : ℕ)/(h+s+4)) ≤ freeFisher (τ p) (doublyNoised p h s) := by
  apply le_trans _ (freeFisher_lower_covariance (τ p) (doublyNoised p h s))
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∑ _i : Fin (p+1), 1 / (h+s+4) := by simp [div_eq_mul_inv]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      apply one_div_le_one_div_of_le
      · rw [doublyNoised_variance p h s hh hs]
        nlinarith [sq_nonneg ‖C p i (τ p).vacuum‖]
      · rw [doublyNoised_variance p h s hh hs]
        linarith [C_vacuum_norm_sq_le p hp i])

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
-- module Solutions.OAIQW_FiniteEntropySeparation.NoiseRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeSeries
variable {α : Type}
 theorem cumulants_injective_normalized {M N : Series α} (hM : M [] = 1) (hN : N [] = 1)
    (h : cumulants M = cumulants N) : M = N := by
  have hm := moments_unique (cumulants_nil M) (cumulants_equation hM)
  have hn := moments_unique (cumulants_nil N) (cumulants_equation hN)
  rw [hm, hn, h]
end FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem X_cumulants (h : ℝ) (hh : 0 ≤ h) :
    cumulants (wordMoment (τ p) (X p h)) =
      cumulants (wordMoment (τ p) (C p)) + (h : ℂ) • quadratic :=
  heat_cumulants ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) h hh
 theorem doublyNoised_cumulants (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    cumulants (wordMoment (τ p) (doublyNoised p h s)) =
      cumulants (wordMoment (τ p) (C p)) + ((h+s : ℝ) : ℂ) • quadratic := by
  calc
    _ = cumulants (wordMoment (τ p) (X p h)) + (s : ℂ) • quadratic :=
      heat_cumulants (oldNoise p) (X p h) (X_mem_background p h)
        (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) s hs
    _ = _ := by rw [X_cumulants p h hh]; simp [add_smul, add_assoc]
 theorem doublyNoised_law (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    wordMoment (τ p) (doublyNoised p h s) = wordMoment (τ p) (X p (h+s)) := by
  apply cumulants_injective_normalized (by simp) (by simp)
  rw [doublyNoised_cumulants p h s hh hs, X_cumulants p (h+s) (add_nonneg hh hs)]
 theorem doublyNoised_fisher_eq (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    freeFisher (τ p) (doublyNoised p h s) = freeFisher (τ p) (X p (h+s)) := by
  apply freeFisher_eq_of_wordMoments (τ p) (τ p)
  · intro i
    exact heatTuple_selfAdjoint (X p h) (auxiliaryNoise p) (X_selfAdjoint p h)
      (auxiliaryNoise_selfAdjoint p) s i
  · exact X_selfAdjoint p (h+s)
  · exact congrFun (doublyNoised_law p h s hh hs)
  · exact exists_conjugate_of_fisher_le _ _ ((p+1 : ℕ)/(h+s))
      (doublyNoised_fisher_le p h s hh hs hu)
  · exact heat_conjugates_exist ∅ (C p) (C_mem_background p ∅) (initialIndex p)
      (initialIndex_injective p) (by simp) (h+s) hu
end Model
end FiniteEntropySeparation

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
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem X_variance (u : ℝ) (hu : 0 ≤ u) (i : Fin (p+1)) :
    ‖X p u i (τ p).vacuum‖^2 = variance p i + u := by
  simpa [doublyNoised, heatTuple, variance] using doublyNoised_variance p u 0 hu (le_refl 0) i
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

 theorem reciprocalDifference_integral {a : ℝ} (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), reciprocalDifference a s = Real.log a := by
  simpa [logarithmicPrimitive] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (reciprocalDifference_integrable ha) (logarithmicPrimitive_atTop a)

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set
namespace FiniteEntropySeparation

 theorem lintegral_ofReal_finite {α : Type u1} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  (lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.hasFiniteIntegral

 theorem reciprocal_posPart_finite {n a : ℝ} (ha : 0 < a) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (n/(1+s)) - ENNReal.ofReal (n/(a+s))) < ∞ := by
  have hh := lintegral_ofReal_finite ((reciprocalDifference_integrable ha).const_mul n)
  apply lt_of_le_of_lt _ hh
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  have hs : 0 < s := hs
  by_cases hn : 0 ≤ n
  · rw [← ENNReal.ofReal_sub _ (div_nonneg hn (by linarith : 0 ≤ a+s))]
    apply le_of_eq
    congr 1
    simp [reciprocalDifference, mul_sub, div_eq_mul_inv]
  · have hz : n / (1+s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) (by linarith)
    rw [ENNReal.ofReal_of_nonpos hz, zero_tsub]
    exact bot_le

 theorem reciprocal_negPart_finite {n a : ℝ} (ha : 0 < a) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (n/(a+s)) - ENNReal.ofReal (n/(1+s))) < ∞ := by
  have hh := lintegral_ofReal_finite (((reciprocalDifference_integrable ha).const_mul n).neg)
  apply lt_of_le_of_lt _ hh
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  have hs : 0 < s := hs
  by_cases hn : 0 ≤ n
  · rw [← ENNReal.ofReal_sub _ (div_nonneg hn (by linarith : 0 ≤ 1+s))]
    apply le_of_eq
    congr 1
    simp [reciprocalDifference, mul_sub, div_eq_mul_inv]
  · have hz : n / (a+s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) (by linarith)
    rw [ENNReal.ofReal_of_nonpos hz, zero_tsub]
    exact bot_le

 theorem entropy_parts_finite {f : ℝ → ℝ≥0∞} {n a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ s, 0 < s → ENNReal.ofReal (n/(b+s)) ≤ f s)
    (hu : ∀ s, 0 < s → f s ≤ ENNReal.ofReal (n/(a+s))) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (n/(1+s)) - f s) < ∞ ∧
    (∫⁻ s in Ioi (0 : ℝ), f s - ENNReal.ofReal (n/(1+s))) < ∞ := by
  constructor
  · apply lt_of_le_of_lt _ (reciprocal_posPart_finite (n := n) hb)
    exact setLIntegral_mono' measurableSet_Ioi (fun s hs => tsub_le_tsub_left (hl s hs) _)
  · apply lt_of_le_of_lt _ (reciprocal_negPart_finite (n := n) ha)
    exact setLIntegral_mono' measurableSet_Ioi (fun s hs => tsub_le_tsub_right (hu s hs) _)

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

 theorem signed_lintegral_toEReal {α : Type u1} [MeasurableSpace α] {μ : Measure α}
    {b f : α → ℝ≥0∞} {r : α → ℝ}
    (hb : ∀ᵐ x ∂μ, b x ≠ ⊤) (hf : ∀ᵐ x ∂μ, f x ≠ ⊤)
    (hr : ∀ᵐ x ∂μ, r x = (b x).toReal - (f x).toReal) (hi : Integrable r μ) :
    (∫⁻ x, b x - f x ∂μ).toEReal - (∫⁻ x, f x - b x ∂μ).toEReal =
      ((∫ x, r x ∂μ : ℝ) : EReal) := by
  have hp : ∫⁻ x, b x - f x ∂μ = ∫⁻ x, ENNReal.ofReal (r x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hb,hf,hr] with x hb hf hr
    rw [hr, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb,
      ENNReal.ofReal_toReal hf]
  have hn : ∫⁻ x, f x - b x ∂μ = ∫⁻ x, ENNReal.ofReal (-r x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hb,hf,hr] with x hb hf hr
    rw [hr, neg_sub, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb,
      ENNReal.ofReal_toReal hf]
  have hnf : (∫⁻ x, ENNReal.ofReal (-r x) ∂μ) < ∞ := by
    simpa only [Pi.neg_apply] using lintegral_ofReal_finite hi.neg
  rw [hp,hn, ← EReal.coe_ennreal_toReal (lintegral_ofReal_finite hi).ne,
    ← EReal.coe_ennreal_toReal hnf.ne,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
  norm_cast

namespace Model
variable (p : ℕ) [NeZero p]
 theorem chiStar_integral (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    chiStar (τ p) (X p a) (auxiliaryNoise p) =
      (((p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
        (1/2 : ℝ) * ∫ s in Ioi (0 : ℝ), (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s) : ℝ) : EReal) := by
  let b : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((p+1 : ℕ)/(1+s))
  let f : ℝ → ℝ≥0∞ := fun s => freeFisher (τ p) (doublyNoised p a s)
  let r : ℝ → ℝ := fun s => (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)
  have hb : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), b s ≠ ⊤ := Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top)
  have hf : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), f s ≠ ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (doublyNoised_fisher_le p a s ha.le hs.le (by linarith [show 0<s from hs]))
  have hr : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), r s = (b s).toReal - (f s).toReal := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hu : 0 < a+s := by linarith [show 0<s from hs]
    have hs0 : 0 < s := hs
    dsimp [r,b,f,heatFisherReal]
    rw [doublyNoised_fisher_eq p a s ha.le hs.le hu, ENNReal.toReal_ofReal (by positivity)]
  have he := signed_lintegral_toEReal hb hf hr (entropyIntegrand_integrable p hp a ha)
  unfold chiStar
  change (_ : EReal) + (1/2 : EReal) * (∫⁻ s in Ioi (0:ℝ), b s - f s).toEReal -
    (1/2 : EReal) * (∫⁻ s in Ioi (0:ℝ), f s - b s).toEReal = _
  have ht := entropy_parts_finite (f := f) (n := (p+1 : ℕ)) ha (by linarith : 0 < a+4)
    (fun s hs => by simpa [f,add_assoc,add_comm,add_left_comm] using
      doublyNoised_fisher_lower p hp a s ha.le hs.le (by linarith))
    (fun s hs => doublyNoised_fisher_le p a s ha.le hs.le (by linarith))
  rw [← EReal.coe_ennreal_toReal ht.1.ne, ← EReal.coe_ennreal_toReal ht.2.ne] at he ⊢
  have he' : (∫⁻ s in Ioi (0:ℝ), b s - f s).toReal -
      (∫⁻ s in Ioi (0:ℝ), f s - b s).toReal = ∫ s in Ioi (0:ℝ), r s := by
    exact_mod_cast he
  change (((p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
    (1/2 : ℝ)*(∫⁻ s in Ioi (0:ℝ), b s-f s).toReal -
    (1/2 : ℝ)*(∫⁻ s in Ioi (0:ℝ), f s-b s).toReal : ℝ) : EReal) = _
  congr 1
  change _ = (p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
    (1/2 : ℝ)*∫ s in Ioi (0:ℝ), r s
  linarith [he']

 theorem covarianceCorrection_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => ∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) (Ioi 0) :=
  integrable_finsetSum _ (fun i _ => reciprocalDifference_integrable (by linarith [variance_nonneg p i]))
 theorem covarianceCorrection_integral (a : ℝ) (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), ∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) =
      ∑ i : Fin (p+1), Real.log (a+variance p i) := by
  rw [integral_finsetSum _ (fun i _ => reciprocalDifference_integrable (by linarith [variance_nonneg p i]))]
  apply sum_congr rfl
  intro i _
  exact reciprocalDifference_integral (by linarith [variance_nonneg p i])
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
 theorem chiStar_covariance_formula (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    chiStar (τ p) (X p a) (auxiliaryNoise p) =
      ((gaussianEntropy p a - (1/2 : ℝ) * ∫ s in Ioi (0:ℝ), fisherDeficit p (a+s) : ℝ) : EReal) := by
  rw [chiStar_integral p hp a ha]
  congr 1
  have he : (∫ s in Ioi (0:ℝ), fisherDeficit p (a+s)) =
      (∑ i : Fin (p+1), Real.log (a+variance p i)) -
      (∫ s in Ioi (0:ℝ), (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) := by
    simp_rw [← covarianceCorrection_identity p a]
    rw [integral_sub (covarianceCorrection_integrable p a ha) (entropyIntegrand_integrable p hp a ha),
      covarianceCorrection_integral p a ha]
  rw [he]
  unfold gaussianEntropy
  ring
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
 theorem integral_Ioi_translate (f : ℝ → ℝ) (a : ℝ) :
    (∫ s in Ioi (0 : ℝ), f (a+s)) = ∫ u in Ioi a, f u := by
  have he : (fun s : ℝ => a+s) ⁻¹' Ioi a = Ioi 0 := by ext s; simp
  simpa only [he] using (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a) f (Ioi a)
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
theorem chiStar_tail_formula_oai (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    chiStar (τ p) (X p a) (auxiliaryNoise p) =
      ((gaussianEntropy p a - (1/2 : ℝ) * ∫ u in Ioi a, fisherDeficit p u : ℝ) : EReal) := by
  rw [chiStar_covariance_formula p hp a ha, integral_Ioi_translate]
end FiniteEntropySeparation.Model

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.Model.chiStar_tail_formula_oai := @OAI.FiniteEntropySeparation.Model.chiStar_tail_formula_oai
