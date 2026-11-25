-- Prove2me | solution 1 for GlobalTheory.WachTie.Laur.tw_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:10.180379+00:00
-- url     : https://prove2.me/submissions/daa4c327-b00e-44ea-8800-25bbeb123068

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfSumSmul
import Theorems.Thm_GlobalTheory_WachTie_Laur_co_smul
import Theorems.Thm_GlobalTheory_WachTie_Laur_co_tw
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GradedSeries_serMul_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WachTie.Laur.co_tw

set_option autoImplicit false
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open GlobalTheory GlobalTheory.WachTie
open GlobalTheory.WachTie.Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
namespace GlobalTheory.WachTie.Laur
theorem _root_.solution {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (f : L⟦X⟧) (x : Laur L M) :
    tw c g (f • x) = rescale c f • tw c g x := by
  apply co_injective
  funext k
  rw [co_tw, co_smul, co_smul]
  show (c ^ k • g) (∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j)) =
    ∑ᶠ j : ℕ, PowerSeries.coeff j (rescale c f) • co (tw c g x) (k - j)
  rw [map_finsum (c ^ k • g) (serMul_finite f (isLaurent_co x) k)]
  refine finsum_congr fun j => ?_
  rw [LinearMap.smul_apply, map_smul, co_tw, PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show c ^ k = c ^ (j : ℤ) * c ^ (k - j) by rw [← zpow_add₀ hc, add_sub_cancel], zpow_natCast]
  ring
end GlobalTheory.WachTie.Laur
