-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.RepeatsAfter.fullTimeD
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:22:47.366779+00:00
-- url     : https://prove2.me/submissions/95c4a7d1-0dde-46ce-8d5d-7987db8a9b81

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FieldBounds.lean:L86-L99
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.RepeatsAfter.fullTimeD. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FieldBounds ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma JointSmooth.timeSlice {v : Field F} (hv : JointSmooth v) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => v t x) := hv.comp (contDiff_id.prodMk contDiff_const)

lemma RepeatsAfter.fullTimeD {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    (hv : JointSmooth v) : RepeatsAfter T (fullTimeD v) := by
  intro t ht
  funext x
  have hh := (hv.timeSlice x).differentiable (by simp)
  have hs : DifferentiableAt ℝ (fun s => v (s + 1) x) t :=
    (hh (t + 1)).comp t (differentiableAt_id.add_const 1)
  have he : EqOn (fun s => v (s + 1) x) (fun s => v s x) (Ici T) :=
    fun s hs => congrFun (h s hs) x
  change deriv (fun s => v s x) (t + 1) = deriv (fun s => v s x) t
  rw [← deriv_comp_add_const (fun s => v s x) 1 t,
    ← hs.derivWithin (uniqueDiffOn_Ici T t ht),
    derivWithin_congr he (he ht),
    (hh t).derivWithin (uniqueDiffOn_Ici T t ht)]

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.RepeatsAfter.fullTimeD := @_root_.OAI.BalancedTransport.Geometry.RepeatsAfter.fullTimeD
