-- Prove2me | solution 1 for GlobalTheory.Mem.ray_prod_LSeries_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:04.557857+00:00
-- url     : https://prove2.me/submissions/2e7d6671-0a9b-4adc-96ac-58b02fe8d086

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_tsum
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_exists_LSeries_exp
import Theorems.Thm_GlobalTheory_Mem_norm_character
import Theorems.Thm_GlobalTheory_Mem_posDirichlet_local
import Theorems.Thm_GlobalTheory_T_ray_L_series_euler_product


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
namespace GlobalTheory.Mem
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) [Fintype (D.G →* ℂˣ)], ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧ ∀ s : ℂ, 1 < s.re → LSeries b s = ∏ χ : D.G →* ℂˣ, LSeries (D.coef χ) s := by
  intro K _ _ M hM D _
  have hsum : ∀ (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → Summable (fun v : D.Pr =>
      -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro χ s hs
    refine (Summable.clog_one_sub (Summable.of_norm ?_)).neg
    simpa only [norm_mul, norm_character, one_mul] using (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.1
  have hq : ∀ v : D.Pr, 2 ≤ Ideal.absNorm v.1.asIdeal := fun v =>
    NumberField.HeightOneSpectrum.one_lt_absNorm v.1
  obtain ⟨b, h0, h1, h2, h3⟩ := (PosDirichlet.tsum
    (fun v : D.Pr => posDirichlet_local (D.cls v.1.asIdeal) (hq v))
    (fun s hs => summable_sum fun χ _ => hsum χ s hs)).exists_LSeries_exp
  refine ⟨b, h0, h1, h2, fun s hs => ?_⟩
  rw [h3 s hs, Summable.tsum_finsetSum (fun χ _ => hsum χ s hs), Complex.exp_sum]
  exact Finset.prod_congr rfl fun χ _ => (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.2.symm
end GlobalTheory.Mem
