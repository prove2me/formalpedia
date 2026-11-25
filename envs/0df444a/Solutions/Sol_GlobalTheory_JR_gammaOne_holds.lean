-- Prove2me | solution 1 for GlobalTheory.JR.gammaOne_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:37.296803+00:00
-- url     : https://prove2.me/submissions/8e0c0d41-600d-418b-8683-98c486bf9ff7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianLatticeIsOpenIsCompactTestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KerLEqTraceDotProductOfIsIsomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PsiKMulNLEqOneOnIntegralLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierIndicatorHermitianIntegralLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConstantStandardHermitianEqOne
import Theorems.Thm_GlobalTheory_GammaOneProof_wS_pow_four
import Theorems.Thm_GlobalTheory_GammaOneProof_wn_pow_three
import Theorems.Thm_GlobalTheory_GammaOneProof_rep_smul
import Theorems.Thm_GlobalTheory_T_fourier_indicator_hermitianIntegralLattice
import Theorems.Thm_GlobalTheory_T_hermitianLattice_isOpen_isCompact_test
import Theorems.Thm_GlobalTheory_T_kerL_eq_trace_dotProduct_of_isIsom
import Theorems.Thm_GlobalTheory_T_psiK_mul_NL_eq_one_on_integral_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.GammaOneProof
namespace GlobalTheory.JR
theorem _root_.solution : GammaOne := by
  intro F E _ _ _ _ _ A ψ hψ x μ hsd ω γ W hW r j hj
  obtain ⟨hΛo, hΛc, hT⟩ := GlobalTheory.T.hermitianLattice_isOpen_isCompact_test F E A r j
  have hN := GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice F E A ψ hψ (x : A.K) r j hj
  have hFour := GlobalTheory.T.fourier_indicator_hermitianIntegralLattice F E A ψ hψ r j (A.kerL ψ x) (GlobalTheory.T.kerL_eq_trace_dotProduct_of_isIsom F E A ψ (x : A.K) r j hj) hΛo hΛc μ hsd.1
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  set φ0 : A.L → ℂ := Set.indicator Λ 1 with hφ0
  have h0 : (0 : A.L) ∈ Λ := by simp [hΛ]
  have hφ00 : φ0 0 = 1 := by simp [hφ0, Set.indicator_of_mem h0]
  have hc : (((μ Λ).toReal : ℝ) : ℂ) = 1 := by
    have h2 := hsd.2 φ0 hT 0
    have hfe : fourB μ (A.kerL ψ x) φ0 = fun y => (((μ Λ).toReal : ℝ) : ℂ) * φ0 y := funext hFour
    rw [hfe] at h2
    have hl : fourB μ (A.kerL ψ x) (fun y => (((μ Λ).toReal : ℝ) : ℂ) * φ0 y) 0
        = (((μ Λ).toReal : ℝ) : ℂ) * fourB μ (A.kerL ψ x) φ0 0 := by
      simp only [fourB, mul_assoc]; exact integral_const_mul _ _
    rw [hl, hFour, neg_zero, hφ00, mul_one] at h2
    have hr : (μ Λ).toReal * (μ Λ).toReal = 1 := by exact_mod_cast h2
    have hnn : 0 ≤ (μ Λ).toReal := ENNReal.toReal_nonneg
    have : (μ Λ).toReal = 1 := by nlinarith
    rw [this]; simp
  obtain ⟨hrep, hrel⟩ := hW
  obtain ⟨hn, -, hw⟩ := hrel φ0 hT
  have hWw : W (wS A.K) φ0 = γ • φ0 := by
    funext y; rw [hw y, hFour y, hc]; simp
  have hWn : W (nS 1) φ0 = φ0 := by
    funext y; rw [hn 1 y]
    by_cases hy : y ∈ Λ
    · rw [one_mul, hN y hy, one_mul]
    · simp [hφ0, Set.indicator_of_notMem hy]
  have hWwn : W (wS A.K * nS 1) φ0 = γ • φ0 := by rw [hrep.2.2.1 _ _ _ hT, hWn, hWw]
  have hpow : ∀ (g : SpecialLinearGroup (Fin 2) A.K) (c : ℂ), W g φ0 = c • φ0 → ∀ k : ℕ, W (g ^ k) φ0 = c ^ k • φ0 := by
    intro g c hg k
    induction k with
    | zero => simp [hrep.2.1 φ0 hT]
    | succ k ih => rw [pow_succ', hrep.2.2.1 _ _ _ hT, ih, rep_smul hrep _ _ hT, hg, smul_smul, pow_succ]
  have e4 := congrFun (hpow _ _ hWw 4) 0
  rw [wS_pow_four, hrep.2.1 φ0 hT] at e4
  have e3 := congrFun (hpow _ _ hWwn 3) 0
  rw [wn_pow_three, hrep.2.1 φ0 hT] at e3
  simp only [Pi.smul_apply, smul_eq_mul, hφ00, mul_one] at e4 e3
  have : γ ^ 4 = γ ^ 3 * γ := pow_succ _ _
  rw [← e4, ← e3, one_mul] at this
  exact this.symm
end GlobalTheory.JR
