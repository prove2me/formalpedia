-- Prove2me | solution 1 for GlobalTheory.T.dual_lattice_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:42.388459+00:00
-- url     : https://prove2.me/submissions/f510358f-9dac-4f61-aec0-c57783229cc5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrizationStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DualLattice_exists_dual_param


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), B.det ≠ 0 → 0 < N → ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧ ∀ y : ι → F, (∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param | exact GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param <;> assumption)
end _root_.GlobalTheory.T
