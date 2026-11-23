-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.mem_unitGL_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:56.312249+00:00
-- url     : https://prove2.me/submissions/08f3b37d-5408-4889-a6a2-42e284999911

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution {g : GL (Fin n) F} (hg : g ∈ unitGL (n := Fin n) F) (i l : Fin n) :
    valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ 1 := by
  obtain ⟨g₀, rfl⟩ := hg
  exact ((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))) i l).2
end GlobalTheory.CompanionTheory.TwContraction
