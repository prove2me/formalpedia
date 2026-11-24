-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_trace_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:42.819927+00:00
-- url     : https://prove2.me/submissions/ecc8cefa-8d8e-4442-9b1b-1b2cd3ae4d53

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
    [DecidableEq κ] (b : Module.Basis κ ℤ (𝓞 F)) :
    ∃ d : κ → F, ∀ v u, Algebra.trace ℚ F ((b v : F) * d u) = if v = u then 1 else 0 := by
  classical
  have hnd := traceForm_nondegenerate ℚ F
  refine ⟨fun u => (Algebra.traceForm ℚ F).dualBasis hnd (ratBasis b) u, fun v u => ?_⟩
  have h := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ F) hnd
    (ratBasis b) u v
  rw [Algebra.traceForm_apply, ratBasis_apply, mul_comm] at h
  exact h
end GlobalTheory.CompanionTheory.SW.ThW.DualLattice
