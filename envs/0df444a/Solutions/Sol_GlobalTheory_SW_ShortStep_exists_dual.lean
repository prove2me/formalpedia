-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:56.102458+00:00
-- url     : https://prove2.me/submissions/fd9d6543-95a2-4171-82c7-25cc2b9fd365

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_mul
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_one
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_dvd
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_sub
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_conj
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_inv_smul
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {n D c : ℕ} (hc : 0 < c) {G : Matrix (Fin n) (Fin n) E}
    {V : Matrix (Fin 1) (Fin n) E} {X : Matrix (Fin n) (Fin 1) E} (hG : Gᴴ = G) (h0 : G.det ≠ 0)
    (hD1 : Den D G) (hD2 : Den D G⁻¹) (hVi : IntM V) (hX : IntM X) (hVX : V * X = (c : E) • 1)
    (hV : V * G * Vᴴ = 0) : ∃ w : Matrix (Fin 1) (Fin n) E, Den (D * c * D * (D * c) * 2) w ∧
      V * G * wᴴ = 1 ∧ w * G * Vᴴ = 1 ∧ w * G * wᴴ = 0 := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  obtain ⟨u, hu⟩ : ∃ u, u = ((c : E)⁻¹ • (G⁻¹ * X))ᴴ := ⟨_, rfl⟩
  have hud : Den (D * c) u := by
    have := den_conj (den_inv_smul hc (den_mul hD2 (den_one hX)))
    rwa [mul_one, ← hu] at this
  have h1 : V * G * uᴴ = 1 := by
    rw [hu, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ h0.isUnit, hVX, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : u * G * Vᴴ = 1 := by
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose h1
  obtain ⟨s, hs⟩ : ∃ s, s = ((2 : ℕ) : E)⁻¹ • (u * G * uᴴ) := ⟨_, rfl⟩
  have hsc : sᴴ = s := by
    simp [hs, conjTranspose_mul, hG, Matrix.mul_assoc]
  have hsd : Den (D * c * D * (D * c) * 2) s :=
    hs ▸ den_inv_smul two_pos (den_mul (den_mul hud hD1) (den_conj hud))
  have h3 : (u - s * V) * G * Vᴴ = 1 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, h2, Matrix.mul_assoc s, Matrix.mul_assoc s, hV]; simp
  refine ⟨u - s * V, den_sub (den_dvd hud ⟨D * (D * c) * 2, by ring⟩)
    (by simpa using den_mul hsd (den_one hVi)), ?_, h3, ?_⟩
  · simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose h3
  · rw [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, ← Matrix.mul_assoc, h3, hsc,
      Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc s, Matrix.mul_assoc s, h1,
      Matrix.mul_one, Matrix.one_mul, hs, sub_sub, ← add_smul]
    norm_num
end GlobalTheory.SW.ShortStep
