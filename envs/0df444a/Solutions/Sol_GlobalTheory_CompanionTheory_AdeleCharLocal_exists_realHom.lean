-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.exists_realHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:40.894842+00:00
-- url     : https://prove2.me/submissions/b0e8d0ae-94b0-4d9b-b469-687c2926d75e

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution : ∃ ρ : ℝ →+* Ainf F, Continuous ρ := by
  have h : ∀ w : InfinitePlace F, ∃ ρ : ℝ →+* w.Completion, Continuous ρ := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom,
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous⟩
    · exact ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.comp Complex.ofRealHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.comp
          Complex.continuous_ofReal⟩
  choose ρ hρ using h
  exact ⟨Pi.ringHom ρ, continuous_pi hρ⟩
end GlobalTheory.CompanionTheory.AdeleCharLocal
