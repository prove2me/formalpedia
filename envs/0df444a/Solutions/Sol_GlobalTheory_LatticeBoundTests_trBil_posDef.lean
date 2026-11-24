-- Prove2me | solution 1 for GlobalTheory.LatticeBoundTests.trBil_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:50.468999+00:00
-- url     : https://prove2.me/submissions/9c677a32-e22e-42fe-8b4c-92c1582a5110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
import Theorems.Thm_GlobalTheory_LatticeBoundTests_trBil_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.LatticeBoundTests
theorem _root_.solution :
    (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i) (RingOfIntegers.basis E j)).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun t ht => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, trBil_apply]
    exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]
  · set u : (E →+* ℂ) → ℂ := fun σ => ∑ i, (t i : ℂ) * σ (RingOfIntegers.basis E i : E) with hu
    have key : star t ⬝ᵥ (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i)
        (RingOfIntegers.basis E j)).mulVec t = ∑ σ, Complex.normSq (u σ) := by
      have : ∀ σ, Complex.normSq (u σ) = ∑ i, ∑ j, t i * ((σ (RingOfIntegers.basis E i : E) *
          starRingEnd ℂ (σ (RingOfIntegers.basis E j : E))).re * t j) := by
        intro σ
        rw [← Complex.ofReal_re (Complex.normSq (u σ)), ← Complex.mul_conj, hu]
        simp only [map_sum, Finset.sum_mul_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp; ring
      simp only [this, dotProduct, Matrix.mulVec, Matrix.of_apply, trBil_apply, star_trivial,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (γ := E →+* ℂ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm (γ := E →+* ℂ)]
    rw [key]
    refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => ht ?_
    have hz : ∀ σ, u σ = 0 := fun σ => Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm σ
        (Finset.mem_univ _))
    have li := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun i => (t i : ℂ)) (by
        funext σ
        have := hz σ
        simpa [hu, canonicalEmbedding.latticeBasis_apply, integralBasis_apply] using this)
    funext i
    exact_mod_cast li i
end GlobalTheory.LatticeBoundTests
