-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.star_eq_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:49.87502+00:00
-- url     : https://prove2.me/submissions/03b169d7-e759-40b7-824b-faa99cc66a2c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDensityEuler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E) (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (hu : _root_.Formalism.HermitianLatticesTheory.IsCMUnram E) (x : E) :
    star x = σ x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ x, hu.2.1 τ x]
  rfl
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual
end GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual
