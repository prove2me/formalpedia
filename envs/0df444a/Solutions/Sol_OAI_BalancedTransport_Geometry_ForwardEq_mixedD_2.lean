-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.ForwardEq.mixedD
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:25:32.856501+00:00
-- url     : https://prove2.me/submissions/f79ffd50-31e5-45dc-88af-9a3f05ef6bc4

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ResidualRegularity.lean:L15-L30
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.ForwardEq.mixedD. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ResidualRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma ForwardEq.mixedD {v w : Field F} (h : ForwardEq v w) (a : MultiIndex) :
    ForwardEq (BalancedTransport.mixedD a v) (BalancedTransport.mixedD a w) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
    intro t ht
    funext x
    cases i with
    | none =>
      change derivWithin (fun s => BalancedTransport.mixedD a v s x) (Ici 0) t =
        derivWithin (fun s => BalancedTransport.mixedD a w s x) (Ici 0) t
      exact derivWithin_congr (s := Ici (0 : ℝ))
        (fun s hs => congrFun (ha s hs) x) (congrFun (ha t ht) x)
    | some i =>
      change fderiv ℝ (BalancedTransport.mixedD a v t) x _ = fderiv ℝ (BalancedTransport.mixedD a w t) x _
      rw [ha t ht]

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.ForwardEq.mixedD := @_root_.OAI.BalancedTransport.Geometry.ForwardEq.mixedD
