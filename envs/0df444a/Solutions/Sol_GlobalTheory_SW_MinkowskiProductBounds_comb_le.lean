-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.comb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:10.186965+00:00
-- url     : https://prove2.me/submissions/1bc57678-eb7d-4d47-98b2-aee49bf547af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_fac
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution {m n : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef)
    (x : Fin n → Fin m → ℂ) (t : Fin n → ℂ) {C M : ℝ}
    (hx : ∀ j, (x j ⬝ᵥ H *ᵥ star (x j)).re ≤ C) (ht : ∀ j, ‖t j‖ ≤ M) :
    ((∑ j, t j • x j) ⬝ᵥ H *ᵥ star (∑ j, t j • x j)).re ≤ (n * (M * √C)) ^ 2 := by
  obtain ⟨B, -, -, h3⟩ := fac hH
  rw [h3]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have : WithLp.toLp 2 ((∑ j, t j • x j) ᵥ* B) = ∑ j, t j • WithLp.toLp 2 (x j ᵥ* B) := by
    simp [sum_vecMul, smul_vecMul]
  rw [this]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (M * √C) fun j _ => ?_).trans
    (by simp))
  rw [norm_smul]
  have h4 := hx j
  rw [h3] at h4
  exact mul_le_mul (ht j) (Real.le_sqrt_of_sq_le h4) (norm_nonneg _) ((norm_nonneg _).trans (ht j))
end GlobalTheory.SW.MinkowskiProductBounds
