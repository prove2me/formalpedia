-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:22.869952+00:00
-- url     : https://prove2.me/submissions/51f6cbb8-6ac0-4ad1-a7a0-6e05d79c27a4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecCloseOfKerBasicColSq
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_ker_sub_of_kerBasic
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_enorm_sq_Lp_two
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_enorm_sq_piLp_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns
namespace GlobalTheory.CompanionTheory.KernelColumns
theorem _root_.solution : KerBasic → ColSq → VecClose := by
  intro hK hC X ι _ Φ Φ' Ω ε y j k k' hΩ hΦ hk hk'
  set R : ℝ≥0∞ := ENNReal.ofReal ε ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y with hR
  have key : ∀ l, ‖(k - k') l‖ₑ ^ 2 ≤ R := by
    intro l
    obtain ⟨t, t', s, s', hd⟩ := hΦ l
    have hT : Tst (fun z => Φ l j z - Φ' l j z) :=
      ⟨t.1.sub t'.1, t.2.sub t'.2⟩
    have hS : Function.support (fun z => Φ l j z - Φ' l j z) ⊆ Ω := by
      intro z hz
      by_contra hn
      have h1 : Φ l j z = 0 := by
        by_contra h0
        exact hn (s h0)
      have h2 : Φ' l j z = 0 := by
        by_contra h0
        exact hn (s' h0)
      exact hz (by simp [h1, h2])
    have hcol := hC X (fun z => Φ l j z - Φ' l j z) ε Ω hT hd hΩ hS y
    have hae : ((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν]
        fun z => ker X.Γ (fun w => Φ l j w - Φ' l j w) z y := by
      filter_upwards [Lp.coeFn_sub (k l) (k' l), hk l, hk' l] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ker_sub_of_kerBasic hK X t t']
    have hsub : (k - k') l = k l - k' l := rfl
    rw [hsub, enorm_sq_Lp_two]
    calc ∫⁻ z, ‖((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) z‖ₑ ^ 2 ∂X.ν
        = ∫⁻ z, ‖ker X.Γ (fun w => Φ l j w - Φ' l j w) z y‖ₑ ^ 2 ∂X.ν :=
          lintegral_congr_ae (hae.mono fun z hz => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) hz)
      _ ≤ R := hcol
  rw [enorm_sq_piLp_two]
  calc ∑ l, ‖(k - k') l‖ₑ ^ 2 ≤ ∑ _l : ι, R := Finset.sum_le_sum fun l _ => key l
    _ = Fintype.card ι * R := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end GlobalTheory.CompanionTheory.KernelColumns
