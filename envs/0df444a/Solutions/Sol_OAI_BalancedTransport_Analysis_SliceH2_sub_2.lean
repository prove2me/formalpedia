-- Prove2me | solution 2 for OAI.BalancedTransport.Analysis.SliceH2.sub
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:56:18.91026+00:00
-- url     : https://prove2.me/submissions/269d1e3a-2021-4acb-836f-26ae026f79a8

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EnergySlice.lean:L25-L41
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Analysis.SliceH2.sub. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Work ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pd_sub (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp only [pd, fderiv_fun_sub hf hg, sub_apply]

theorem pd_contDiff (i : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EnergySlice ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry

lemma SliceH2.sub {u v : Space → Space} (hu : SliceH2 u) (hv : SliceH2 v) :
    SliceH2 (fun x => u x - v x) := by
  have he (j : Fin 3) : pd j (fun x => u x - v x) = fun x => pd j u x - pd j v x := by
    ext x i
    rw [pd_sub _ (hu.smooth.differentiable (by simp) x) (hv.smooth.differentiable (by simp) x)]
  refine ⟨hu.smooth.sub hv.smooth, fun i => (hu.l2 i).sub (hv.l2 i), ?_, ?_⟩
  · intro i j
    rw [he]
    exact (hu.d_l2 i j).sub (hv.d_l2 i j)
  · intro i j
    rw [he]
    have hh : pd j (fun x => pd j u x - pd j v x) =
        fun x => pd j (pd j u) x - pd j (pd j v) x :=
      funext (fun x => pd_sub j ((pd_contDiff j hu.smooth).differentiable (by simp) x)
        ((pd_contDiff j hv.smooth).differentiable (by simp) x))
    rw [hh]
    exact (hu.dd_l2 i j).sub (hv.dd_l2 i j)

end BalancedTransport.Analysis
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry


theorem solution : type_of% @_root_.OAI.BalancedTransport.Analysis.SliceH2.sub := @_root_.OAI.BalancedTransport.Analysis.SliceH2.sub
