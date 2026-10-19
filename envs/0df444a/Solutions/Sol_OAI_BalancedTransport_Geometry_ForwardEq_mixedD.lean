-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.ForwardEq.mixedD
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:23:49.913885+00:00
-- url     : https://prove2.me/submissions/6e24b258-e004-41c9-ba86-9e23f2d424b6

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem solution {v w : BalancedTransport.Field F} (h : ForwardEq v w) (a : MultiIndex) :
    ForwardEq (BalancedTransport.mixedD a v) (BalancedTransport.mixedD a w) := by
  induction a with
  | nil => exact h
  | cons o a ih =>
    intro t ht
    funext x
    cases o with
    | none =>
      show derivWithin (fun s => BalancedTransport.mixedD a v s x) (Set.Ici 0) t =
        derivWithin (fun s => BalancedTransport.mixedD a w s x) (Set.Ici 0) t
      apply derivWithin_congr
      · intro s hs; exact congrFun (ih s hs) x
      · exact congrFun (ih t ht) x
    | some i =>
      show fderiv ℝ (BalancedTransport.mixedD a v t) x (Pi.single i 1) =
        fderiv ℝ (BalancedTransport.mixedD a w t) x (Pi.single i 1)
      rw [ih t ht]

