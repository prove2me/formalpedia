-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:58.587565+00:00
-- url     : https://prove2.me/submissions/78dbf83f-6076-4dba-8aa9-44e7138623ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
variable {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution (ε : D.G → ℝ) (hε : ∀ g h, ε (g * h) = ε g * ε h) (I J : Ideal (𝓞 K)) :
    chi D ε (I * J) = chi D ε I * chi D ε J := by
  by_cases hI : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
  · by_cases hJ : J ≠ ⊥ ∧ IsCoprime J (Ideal.span {(M : 𝓞 K)})
    · have hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)}) :=
        ⟨mul_ne_zero hI.1 hJ.1, hI.2.mul_left hJ.2⟩
      simp only [chi]
      rw [if_pos hIJ, if_pos hI, if_pos hJ, D.cls_mul I J hI.2 hJ.2 hI.1 hJ.1, hε]
    · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
        rintro ⟨h1, h2⟩
        exact hJ ⟨fun h => h1 (by rw [h, Ideal.mul_bot]), h2.of_mul_left_right⟩
      simp only [chi]
      rw [if_pos hI, if_neg hJ, if_neg hIJ, mul_zero]
  · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
      rintro ⟨h1, h2⟩
      exact hI ⟨fun h => h1 (by rw [h, Ideal.bot_mul]), h2.of_mul_left_left⟩
    simp only [chi]
    rw [if_neg hI, if_neg hIJ, zero_mul]
end GlobalTheory.Hk.RaySq
