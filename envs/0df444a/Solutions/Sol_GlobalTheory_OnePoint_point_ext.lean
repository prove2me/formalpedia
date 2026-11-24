-- Prove2me | solution 1 for GlobalTheory.OnePoint.point_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:24.432325+00:00
-- url     : https://prove2.me/submissions/256d3b07-7702-49c9-8827-5f805eb67f55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_epi_of_nonempty

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
theorem _root_.solution {X T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K))
    {s s' : Spec (.of K) ⟶ X} (h : g ≫ s = g ≫ s') : s = s' :=
  have := epi_of_nonempty g
  (cancel_epi g).mp h
end GlobalTheory.OnePoint
