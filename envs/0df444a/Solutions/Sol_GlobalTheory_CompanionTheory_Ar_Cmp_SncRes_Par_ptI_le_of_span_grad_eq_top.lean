-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.ptI_le_of_span_grad_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:05.745311+00:00
-- url     : https://prove2.me/submissions/e82480ae-b268-4836-9eda-040ee8ae7a14

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SpanEqTopOfForallDotEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_lin_mem_of_eval_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_ptIdeal_eq_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) (A : Set (MvPolynomial (Fin m) ℂ)) (hAJ : A ⊆ J)
    (hA0 : ∀ a ∈ A, eval t a = 0) (hA : Submodule.span ℂ (gradP t '' A) = ⊤) :
    ptI t ≤ J := by
  let φ : (Fin m → ℂ) →ₗ[ℂ] MvPolynomial (Fin m) ℂ :=
    { toFun := fun v => ∑ i, C (v i) * (X i - C (t i))
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          MvPolynomial.smul_eq_C_mul, mul_assoc] }
  have hφ : ∀ v, φ v = ∑ i, C (v i) * (X i - C (t i)) := fun v => rfl
  have hspan : Submodule.span ℂ (gradP t '' A) ≤ Submodule.comap φ (J.restrictScalars ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, haA, rfl⟩
    show φ (gradP t a) ∈ J
    rw [hφ]
    exact lin_mem_of_eval_eq_zero t J hJ (hAJ haA) (hA0 a haA)
  have key : ∀ i, X i - C (t i) ∈ J := by
    intro i
    have hmem : (Pi.single i 1 : Fin m → ℂ) ∈ Submodule.comap φ (J.restrictScalars ℂ) :=
      hspan (by rw [hA]; exact Submodule.mem_top)
    have h2 : φ (Pi.single i 1) ∈ J := hmem
    rw [hφ, Finset.sum_eq_single i] at h2
    · simpa using h2
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact key i
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
