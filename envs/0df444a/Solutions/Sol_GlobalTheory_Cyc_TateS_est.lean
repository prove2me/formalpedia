-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.est
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:48.844121+00:00
-- url     : https://prove2.me/submissions/7045277b-0173-4986-aee9-b766bf5b0546

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_Gj_le
import Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_le
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_le_one
import Theorems.Thm_GlobalTheory_Cyc_TateS_est_pow
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_continuous
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_le_one
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers
import Theorems.Thm_GlobalTheory_UnramValue_norm_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {ζ : PadicComplex l} (hζ : IsPrimitiveRoot ζ l)
    {x : PadicComplex l} (hx : x ∈ Xj K j) : ‖ζ - 1‖ * ‖x‖ ≤ l * ‖act g x - x‖ := by
  have hp : l.Prime := Fact.out
  have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine closure_minimal (s := (Xalg K j : Set (PadicComplex l)))
    (t := {x : PadicComplex l | ‖ζ - 1‖ * ‖x‖ ≤ l * ‖act g x - x‖}) (fun d hd => ?_)
    (isClosed_le (continuous_const.mul continuous_norm)
      (continuous_const.mul ((act_continuous hact g).sub continuous_id).norm)) hx
  change ‖ζ - 1‖ * ‖d‖ ≤ l * ‖act g d - d‖
  rw [← norm_mul]
  have hdX := Xalg_le K j hd
  rcases (norm_nonneg (act g d - d)).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1) fun n =>
      est_pow hact hχ K hj hg hζ hd n (by rw [← h]; positivity)
  · have h1 : ‖act g d - d‖ ≤ 1 := norm_le_one hact hχ K hj.1
      (sub_mem ((GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.2.2.2.1 g (Gj_le K j hg.1) d hdX) hdX)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one h h1 hl0 hl1
    refine (est_pow hact hχ K hj hg hζ hd n hn').trans ?_
    have : (l : ℝ)⁻¹ ^ n = l * (l : ℝ)⁻¹ ^ (n + 1) := by
      rw [pow_succ]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hn.le (by positivity)
end GlobalTheory.Cyc.TateS
