-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.norm_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:25.25281+00:00
-- url     : https://prove2.me/submissions/9ce1f217-3523-4bd6-b845-3d942db67599

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_orthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil



set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KWeightMajor
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
namespace GlobalTheory.CompanionTheory.KWeightMajor
theorem _root_.solution (hF : KRel ε E) (hU : KUnit ε E) {a b : Fin n} (he : ε a = ε b) {μ : Fin n → ℝ} {w : V}
    (hw : IsWeight E μ w) : ‖E a b w‖ ^ 2 = ‖E b a w‖ ^ 2 + (μ b - μ a) * ‖w‖ ^ 2 := by
  have hc := hF a b b a he he.symm
  simp only [if_pos rfl, ↓reduceIte] at hc
  have hcw : E a b (E b a w) - E b a (E a b w) = (μ a : ℂ) • w - (μ b : ℂ) • w := by
    have := congrArg (fun T : Module.End ℂ V => T w) hc
    simpa [Module.End.mul_apply, hw a, hw b] using this
  have h1 : inner ℂ (E a b w) (E a b w) = inner ℂ w (E b a (E a b w)) := hU a b he w (E a b w)
  have h2 : inner ℂ (E b a w) (E b a w) = inner ℂ w (E a b (E b a w)) := hU b a he.symm w (E b a w)
  have h3 : E b a (E a b w) = E a b (E b a w) - ((μ a : ℂ) • w - (μ b : ℂ) • w) := by
    rw [← hcw]; abel
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (E a b w), norm_sq_eq_re_inner (𝕜 := ℂ) (E b a w),
    norm_sq_eq_re_inner (𝕜 := ℂ) w, h1, h2, h3, inner_sub_right, inner_sub_right, inner_smul_right,
    inner_smul_right]
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.re_ofReal_mul]
  ring
end GlobalTheory.CompanionTheory.KWeightMajor
