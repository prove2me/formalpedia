-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.DualLattice.eq_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:41.291438+00:00
-- url     : https://prove2.me/submissions/e90291c4-9892-4efb-a9d8-8206379a5e32

import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DualLattice_ratBasis_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.DualLattice
namespace GlobalTheory.CompanionTheory.SW.ThW.DualLattice
theorem _root_.solution {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) {x y : F}
    (h : ∀ v, Algebra.trace ℚ F ((b v : F) * x) = Algebra.trace ℚ F ((b v : F) * y)) :
    x = y := by
  have hnd := traceForm_nondegenerate ℚ F
  rw [← sub_eq_zero]
  apply hnd.2 _
  intro z
  have hL : (Algebra.trace ℚ F) ∘ₗ (LinearMap.mulRight ℚ (x - y)) = 0 := by
    refine (ratBasis b).ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ratBasis_apply, mul_sub, map_sub, h v,
      sub_self, LinearMap.zero_apply]
  exact LinearMap.congr_fun hL z
end GlobalTheory.CompanionTheory.SW.ThW.DualLattice
