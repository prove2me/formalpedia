-- Prove2me | solution 1 for GlobalTheory.ThetaGL.DualPair.ev_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:12.008748+00:00
-- url     : https://prove2.me/submissions/bf75657b-36ca-4860-97db-6b2c29b28f8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGL.DualPair.ev_tmul

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaGL GlobalTheory.ThetaGL.DualPair
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.ThetaGL.DualPair
theorem _root_.solution {H : Type} [Group H] (σ : Representation ℂ H V) (π : Representation ℂ G W) (g : H) (h : G)
    (t : V ⊗[ℂ] smoothPart π.dual) (w : W) :
    ev V π (TensorProduct.map (σ g) (contra π h) t) w = σ g (ev V π t (π h⁻¹ w)) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul v l => simp
end GlobalTheory.ThetaGL.DualPair
