-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:48.954182+00:00
-- url     : https://prove2.me/submissions/5b1379ff-4e1e-4aeb-8d29-07f49d15e94e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TemperedOfLpDimLeOneOfUnitEigenvalues
import Theorems.Thm_GlobalTheory_WeilDeligne_absSpace_eq_bot_of_norm_charpoly_roots
import Theorems.Thm_GlobalTheory_WeilDeligne_absSpace_one_eq_top_of_norm_charpoly_roots
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  intro E Ω _ _ _ _ _ A w h a _ heig
  induction a using WD.ind with
  | hP n a =>
  rw [WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := by
    intro α hα; exact heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hne : ∀ s : ℝ, s ≠ 0 → ((normV w : ℕ) : ℝ) ^ s ≠ 1 := by
    intro s hs h1
    rw [← Real.rpow_zero ((normV w : ℕ) : ℝ), Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne'] at h1
    exact hs h1
  refine ⟨eq_top_iff.mpr ?_, fun i => ?_⟩
  · rw [← absSpace_one_eq_top_of_norm_charpoly_roots (a.semisimple φ) hroots]
    refine le_iSup_of_le (0 : ℤ) ?_
    simp
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, Nat.cast_zero, neg_zero]
      exact Set.bijOn_id _
    · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
      rw [absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith)),
        absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith))]
      simp only [Submodule.bot_coe]
      exact ⟨fun v hv => by rw [Set.mem_singleton_iff.mp hv, map_zero]; rfl,
        fun v hv v' hv' _ => by rw [Set.mem_singleton_iff.mp hv, Set.mem_singleton_iff.mp hv'],
        fun v hv => ⟨0, rfl, by rw [Set.mem_singleton_iff.mp hv, map_zero]⟩⟩
end GlobalTheory.WeilDeligne.WD
