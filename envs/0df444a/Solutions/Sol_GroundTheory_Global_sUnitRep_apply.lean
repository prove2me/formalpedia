-- Prove2me | solution 1 for GroundTheory.Global.sUnitRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:43.668772+00:00
-- url     : https://prove2.me/submissions/64da6f8c-3dec-4e7c-9713-95bba4b3ef1a

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
    (x : Additive (S.unit L)) :
    sUnitRep S hS g x = Additive.ofMul (sUnitMap S hS g x.toMul) :=
  rfl
end GroundTheory.Global
