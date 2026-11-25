-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.exists_int_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:55.321967+00:00
-- url     : https://prove2.me/submissions/8744a2f1-2882-4ccb-adf3-df6267085ede

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_mul
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_smul
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_one
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_li_of_mul
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul
import Theorems.Thm_GlobalTheory_SW_Base_ccT_one
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
theorem _root_.solution {N m n D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E} (h0 : G.det ≠ 0)
    {W : Matrix (Fin N) (Fin m) E} (hW : IsoRows G W) {V : Matrix (Fin n) (Fin m) E}
    {S : Matrix (Fin m) (Fin n) E} (hS : S * V = 1) :
    ∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' (V * ((D : E) • G) * ccT V) T := by
  classical
  obtain ⟨k, hk, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin N × Fin n => (W * S) p.1 p.2)
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
  have h1 : ((k : E) • (W * S)) * V = (k : E) • W := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hS, Matrix.mul_one]
  have h2 : ccT V * ccT S = 1 := by rw [← ccT_mul, hS, ccT_one]
  refine ⟨(k : E) • (W * S), fun i j => ?_, ?_, ?_⟩
  · simpa using hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  · refine li_of_mul (R := ((k : E)⁻¹ * (D : E)⁻¹) • (ccT S * G⁻¹)) ?_
    have : (k : E) • (W * S) * (V * ((D : E) • G) * ccT V) *
        ((k : E)⁻¹ * (D : E)⁻¹) • (ccT S * G⁻¹) = W := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (ccT V), h2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.one_mul,
        mul_nonsing_inv_cancel_right _ _ h0.isUnit]
      rw [show (k : E)⁻¹ * (D : E)⁻¹ * (D * k) = 1 by field_simp, one_smul]
    rw [this]
    exact hW.1
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (ccT V), ← ccT_mul, h1, ccT_smul]
    simp [hW.2]
end GlobalTheory.SW.MinkowskiProductBounds
