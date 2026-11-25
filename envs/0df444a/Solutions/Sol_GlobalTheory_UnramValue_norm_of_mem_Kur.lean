-- Prove2me | solution 1 for GlobalTheory.UnramValue.norm_of_mem_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:17.466263+00:00
-- url     : https://prove2.me/submissions/c6ef8ab3-fae7-44fb-9ec7-f1eec0889b75

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_norm_algebraMap_int
import Theorems.Thm_GlobalTheory_UnramValue_norm_rootRing
import Theorems.Thm_GlobalTheory_UnramValue_exists_mul_mem

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
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by
  have hp : l.Prime := Fact.out
  obtain ⟨m, hm, hlm, c, hc, hmem⟩ := exists_mul_mem hx
  have hcx : algebraMap ℤ_[l] (Om l) c * x ≠ 0 := by
    refine mul_ne_zero ?_ h0
    rw [← norm_ne_zero_iff, norm_algebraMap_int]
    exact norm_ne_zero_iff.2 hc
  obtain ⟨n, hn⟩ := norm_rootRing hm hlm hmem hcx
  rw [norm_mul, norm_algebraMap_int] at hn
  have hc' : (c : ℚ_[l]) ≠ 0 := fun h => hc (PadicInt.ext (h.trans PadicInt.coe_zero.symm))
  have hcv : ‖c‖ = (l : ℝ) ^ (-(c : ℚ_[l]).valuation) := by
    rw [PadicInt.norm_def]
    exact Padic.norm_eq_zpow_neg_valuation hc'
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hcv] at hn
  refine ⟨n + (c : ℚ_[l]).valuation, ?_⟩
  calc ‖x‖ = (l : ℝ) ^ ((c : ℚ_[l]).valuation) * ((l : ℝ) ^ (-(c : ℚ_[l]).valuation) * ‖x‖) := by
        rw [← mul_assoc, ← zpow_add₀ hl0, add_neg_cancel, zpow_zero, one_mul]
    _ = (l : ℝ) ^ (n + (c : ℚ_[l]).valuation) := by rw [hn, zpow_add₀ hl0, mul_comm]
end GlobalTheory.UnramValue
