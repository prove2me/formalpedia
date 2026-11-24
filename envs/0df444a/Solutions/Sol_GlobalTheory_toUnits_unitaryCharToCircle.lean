-- Prove2me | solution 1 for GlobalTheory.toUnits_unitaryCharToCircle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:59.758624+00:00
-- url     : https://prove2.me/submissions/73c3853b-1e48-4043-9134-06141a9bfa91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) (y : A) :
    Circle.toUnits (unitaryCharToCircle a ha y) = a y := by
  ext
  rfl
end GlobalTheory
