-- Prove2me | solution 1 for GlobalTheory.Cyc.IntBasis.term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:35.450581+00:00
-- url     : https://prove2.me/submissions/c45f71c0-0fc8-4f03-bb15-5d9ec1f452b6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
import Theorems.Thm_GlobalTheory_Cyc_IntBasis_norm_le_norm_sum
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
    (z : ℕ → Om l) (hz : ∀ a, z a ∈ Ks K (i - 1)) (a : ℕ) (ha : a < l) :
    ‖z a * (ζ - 1) ^ a‖ ≤ ‖∑ b ∈ Finset.range l, z b * (ζ - 1) ^ b‖ := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  apply norm_le_norm_sum _ _ _ a (Finset.mem_range.2 ha)
  intro b hb c hc hbc hb0 hc0 heq
  have hzb : z b ≠ 0 := left_ne_zero_of_mul hb0
  have hzc : z c ≠ 0 := left_ne_zero_of_mul hc0
  obtain ⟨nb, -, hnb⟩ := norm_term K i hi ζ hζ (z b) (hz b) hzb
  obtain ⟨nc, -, hnc⟩ := norm_term K i hi ζ hζ (z c) (hz c) hzc
  rw [hnb b, hnc c] at heq
  have hD : (0 : ℝ) < (l : ℝ) ^ (i - 1) * ((l : ℝ) - 1) := by
    apply mul_pos (pow_pos (by linarith) _)
    linarith
  have h1 : (((nb * l - b : ℤ) : ℝ)) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1)) =
      (((nc * l - c : ℤ) : ℝ)) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1)) :=
    le_antisymm ((Real.rpow_le_rpow_left_iff hl).1 heq.le) ((Real.rpow_le_rpow_left_iff hl).1 heq.ge)
  have h2 : nb * (l : ℤ) - b = nc * l - c := by
    exact_mod_cast (div_left_inj' hD.ne').1 h1
  have hb' : b < l := Finset.mem_range.1 hb
  have hc' : c < l := Finset.mem_range.1 hc
  have key : (nb - nc) * (l : ℤ) = b - c := by rw [sub_mul]; linarith
  rcases lt_trichotomy nb nc with h | h | h
  · have : (nb - nc) * (l : ℤ) ≤ -l := by nlinarith
    omega
  · subst h
    omega
  · have : (l : ℤ) ≤ (nb - nc) * l := by nlinarith
    omega
end GlobalTheory.Cyc.IntBasis
