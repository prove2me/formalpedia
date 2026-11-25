-- Prove2me | solution 1 for GlobalTheory.Cyc.IntBasis.coeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:32.926817+00:00
-- url     : https://prove2.me/submissions/1d1f5631-f2e3-4d8a-80be-93d095a1ffbc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
import Theorems.Thm_GlobalTheory_Cyc_IntBasis_norm_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.IntBasis
theorem _root_.solution (K : FinExt l) (i : ℕ) (hi : 2 ≤ i) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ i))
    (z : Om l) (hz : z ∈ Ks K (i - 1)) (a : ℕ) (ha : a < l) (h : ‖z * (ζ - 1) ^ a‖ ≤ 1) :
    ‖z‖ ≤ 1 := by
  by_cases hz0 : z = 0
  · rw [hz0, norm_zero]
    exact zero_le_one
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn, hna⟩ := norm_term K i hi ζ hζ z hz hz0
  have hD : (0 : ℝ) < (l : ℝ) ^ (i - 1) * ((l : ℝ) - 1) := by
    apply mul_pos (pow_pos (by linarith) _)
    linarith
  rw [hna a] at h
  have h1 : ((n * l - a : ℤ) : ℝ) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1)) ≤ 0 := by
    by_contra h1
    exact absurd h (not_le.2 (Real.one_lt_rpow hl (lt_of_not_ge h1)))
  have h2 : n * (l : ℤ) - a ≤ 0 := by
    have := (div_le_iff₀ hD).1 h1
    rw [zero_mul] at this
    exact_mod_cast this
  have h3 : n ≤ 0 := by
    by_contra hn'
    have : (l : ℤ) ≤ n * l := by nlinarith
    omega
  rw [hn]
  apply Real.rpow_le_one_of_one_le_of_nonpos hl.le
  apply div_nonpos_of_nonpos_of_nonneg _ hD.le
  have : n * (l : ℤ) ≤ 0 := by nlinarith
  exact_mod_cast this
end GlobalTheory.Cyc.IntBasis
