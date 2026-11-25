-- Prove2me | solution 1 for GroundTheory.Global.ofUnits_unitsRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:01:15.668861+00:00
-- url     : https://prove2.me/submissions/c29c8e1c-5339-4d09-9345-76fb23622f5d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L)))
namespace GroundTheory.Global
theorem _root_.solution (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (u : Additive (𝓞 L)ˣ) :
    (SUnit.ofUnits S).toAdditive (unitsRep K L g u) =
      sUnitRep S hS g ((SUnit.ofUnits S).toAdditive u) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rfl
end GroundTheory.Global
