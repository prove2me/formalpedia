-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.lowerSemicontinuous_freeFisher
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:11:37.690373+00:00
-- url     : https://prove2.me/submissions/e704d224-30f6-4dca-a9a4-98f4f822d9b9

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE000

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

 theorem continuous_wordEval {T : Type u1} [TopologicalSpace T] {n : ℕ}
    (X : T → Fin n → H →L[ℂ] H) (hX : ∀ i, Continuous (fun t => X t i))
    (w : List (Fin n)) : Continuous (fun t => wordEval (X t) w) := by
  induction w with
  | nil => simpa [wordEval] using (continuous_const : Continuous (fun _ : T => (1 : H →L[ℂ] H)))
  | cons i w ih =>
    change Continuous (fun t => X t i * wordEval (X t) w)
    exact (hX i).mul ih

 theorem continuous_wordMoment {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {T : Type u2} [TopologicalSpace T] {n : ℕ}
    (X : T → Fin n → H →L[ℂ] H) (hX : ∀ i, Continuous (fun t => X t i))
    (w : List (Fin n)) : Continuous (fun t => wordMoment τ (X t) w) := by
  exact continuous_const.inner ((continuous_wordEval X hX w).clm_apply continuous_const)

 theorem continuous_derivativeMoment {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {T : Type u3} [TopologicalSpace T] {n : ℕ}
    (X : T → Fin n → H →L[ℂ] H) (hX : ∀ i, Continuous (fun t => X t i))
    (i : Fin n) (w : List (Fin n)) : Continuous (fun t => derivativeMoment τ (X t) i w) := by
  unfold derivativeMoment
  apply continuous_finsetSum
  intro r _
  split_ifs
  · exact (continuous_wordMoment τ X hX _).mul (continuous_wordMoment τ X hX _)
  · exact continuous_const

 theorem continuous_fisherTest {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {T : Type u4} [TopologicalSpace T] {n : ℕ}
    (X : T → Fin n → H →L[ℂ] H) (hX : ∀ i, Continuous (fun t => X t i))
    (i : Fin n) (p : WordPolynomial n) : Continuous (fun t => fisherTest τ (X t) i p) := by
  have hd : Continuous (fun t => polynomialDerivative τ (X t) i p) := by
    simp only [polynomialDerivative, Finsupp.linearCombination_apply, Finsupp.sum]
    apply continuous_finsetSum
    intro w _
    exact (continuous_const (y := p w)).smul (continuous_derivativeMoment τ X hX i w)
  have hv : Continuous (fun t => polynomialVector τ (X t) p) := by
    simp only [polynomialVector, Finsupp.linearCombination_apply, Finsupp.sum]
    exact continuous_finsetSum _ (fun w _ => continuous_const.smul
      ((continuous_wordEval X hX w).clm_apply continuous_const))
  exact (continuous_const.mul (Complex.continuous_re.comp hd)).sub (hv.norm.pow 2)

theorem lowerSemicontinuous_freeFisher_oai {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {T : Type u5} [TopologicalSpace T] {n : ℕ}
    (X : T → Fin n → H →L[ℂ] H) (hX : ∀ i, Continuous (fun t => X t i))
    (he : ∀ t, ∃ ξ, ConjugateSystem τ (X t) ξ) :
    LowerSemicontinuous (fun t => freeFisher τ (X t)) := by
  have heq : (fun t => freeFisher τ (X t)) =
      (fun t => ∑ i, ⨆ p : WordPolynomial n, ENNReal.ofReal (fisherTest τ (X t) i p)) := by
    funext t
    obtain ⟨ξ,hξ⟩ := he t
    exact freeFisher_variational τ _ hξ
  rw [heq]
  apply lowerSemicontinuous_sum
  intro i _
  apply lowerSemicontinuous_iSup
  intro p
  exact (ENNReal.continuous_ofReal.comp (continuous_fisherTest τ X hX i p)).lowerSemicontinuous

end FiniteEntropySeparation

end

end OAI
end

theorem solution.{u5} : type_of% @OAI.FiniteEntropySeparation.lowerSemicontinuous_freeFisher_oai.{u5} := @OAI.FiniteEntropySeparation.lowerSemicontinuous_freeFisher_oai.{u5}
