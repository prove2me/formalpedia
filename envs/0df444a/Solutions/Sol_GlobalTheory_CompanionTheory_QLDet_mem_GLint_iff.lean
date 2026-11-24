-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:07:49.371425+00:00
-- url     : https://prove2.me/submissions/24dd98b9-e93e-4a56-bb74-f89a6c6f9127

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Theorems.Thm_GlobalTheory_CompanionTheory_QLDet_det_mem_of_isInt
import Theorems.Thm_GlobalTheory_CompanionTheory_QLDet_adjugate_isInt
import Theorems.Thm_GlobalTheory_T_localField_uniformizer_norm_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLDet
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QLDet
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
      nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  obtain ⟨-, -, hO, -, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hdet : (g : Matrix (Fin n) (Fin n) F).det * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ : IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
        IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := hg
    refine ⟨h1, ?_⟩
    have a1 := (hO _).2 (det_mem_of_isInt O h1)
    have a2 := (hO _).2 (det_mem_of_isInt O h2)
    have hm : nrm (g : Matrix (Fin n) (Fin n) F).det *
        nrm ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← map_mul, hdet, map_one]
    have p1 := nrm.nonneg (g : Matrix (Fin n) (Fin n) F).det
    have p2 := nrm.nonneg ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det
    nlinarith
  · rintro ⟨h1, h2⟩
    show IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨h1, ?_⟩
    intro a b
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    apply O.mul_mem
    · apply (hO _).1
      rw [map_inv₀, h2, inv_one]
    · exact adjugate_isInt O h1 a b
end GlobalTheory.CompanionTheory.QLDet
