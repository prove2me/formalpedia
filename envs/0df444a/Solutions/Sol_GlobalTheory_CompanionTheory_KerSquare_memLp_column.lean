-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerSquare.memLp_column
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:42.338152+00:00
-- url     : https://prove2.me/submissions/63dfe4b1-0b1e-4907-b488-8d1e2bfca219

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelRowsColumnsSquareIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerSquare
namespace GlobalTheory.CompanionTheory.KerSquare
theorem _root_.solution (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by
  have hcont : Continuous fun x => ker X.Γ φ x y :=
    (hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have hΩ : IsCompact (tsupport φ) := hφ.2
  have hbound := hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y
  have hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤ := hΩ.inv.measure_lt_top.ne
  have hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤ :=
    (hC X).1 _ (hΩ.inv.mul hΩ) y
  have hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ *
      cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact hbound.trans_lt hfin
end GlobalTheory.CompanionTheory.KerSquare
