-- Prove2me | solution 1 for GlobalTheory.OnePoint.epi_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:15:47.031481+00:00
-- url     : https://prove2.me/submissions/991e819e-5a1d-4e8a-a8de-f4575ae33729

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution {T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K)) : Epi g :=
  have : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective g
end GlobalTheory.OnePoint
