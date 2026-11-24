-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubEig.smooth_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:17.35178+00:00
-- url     : https://prove2.me/submissions/30e11cb0-64dd-4a24-994f-8095a6e46f84

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothQuot
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisLast
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SubquotientOfEigencharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubEig
variable {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.SubEig
theorem _root_.solution {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : U) = v} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact hρ _
end GlobalTheory.CompanionTheory.SubEig
