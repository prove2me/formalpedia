-- Prove2me | solution 1 for GlobalTheory.T.totally_real_integral_basis_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:45.403993+00:00
-- url     : https://prove2.me/submissions/a04e07f5-0eed-47b1-be86-5d409b11f973

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealIntegralBasisExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealIntegralBasisExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_exists_integralBasis_infinitePlace


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | exact GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace <;> assumption)
end _root_.GlobalTheory.T
