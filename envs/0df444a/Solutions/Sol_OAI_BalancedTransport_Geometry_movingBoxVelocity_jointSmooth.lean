-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.movingBoxVelocity_jointSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:19:35.910567+00:00
-- url     : https://prove2.me/submissions/202af601-82a2-4646-a195-b60a7cdb88eb

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/TimeRegularity.lean:L89-L107
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.movingBoxVelocity_jointSmooth. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem JointSmooth.spaceD {f : Field F} (hf : JointSmooth f) (i : Fin 3) :
    JointSmooth (spaceD i f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × Space => f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem JointSmooth.curl {A : Velocity} (hA : JointSmooth A) :
    JointSmooth (fun t => curl (A t)) := by
  have he (i : Fin 3) : JointSmooth (fun t x => A t x i) := contDiff_pi.mp hA i
  have hd (i j : Fin 3) := (he j).spaceD i
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (hd 1 2).sub (hd 2 1)
  · exact (hd 2 0).sub (hd 0 2)
  · exact (hd 0 1).sub (hd 1 0)

lemma logarithmicRate_contDiff {d : ℝ → Space} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (logarithmicRate d) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_infty_iff_deriv.mp (contDiff_pi.mp hd i)).2.div
    (contDiff_pi.mp hd i) (fun t => hn t i)

theorem movingBoxVelocity_jointSmooth {c d : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (a b : Space) (η : ℝ) :
    JointSmooth (movingBoxVelocity a b c d η) := by
  apply JointSmooth.curl
  have hcd := (contDiff_infty_iff_deriv.mp hc).2
  have hl := logarithmicRate_contDiff hd hn
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space =>
    boxCutoff (lowerEndpoint a c d z.1) (lowerEndpoint b c d z.1) η z.2 •
      affinePotential (c z.1) (deriv c z.1) (logarithmicRate d z.1) z.2)
  refine ContDiff.smul (f := fun z : ℝ × Space =>
    boxCutoff (lowerEndpoint a c d z.1) (lowerEndpoint b c d z.1) η z.2)
    (g := fun z : ℝ × Space =>
      affinePotential (c z.1) (deriv c z.1) (logarithmicRate d z.1) z.2) ?_ ?_
  · unfold boxCutoff lowerEndpoint
    fun_prop
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [affinePotential] <;> fun_prop

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.movingBoxVelocity_jointSmooth := @_root_.OAI.BalancedTransport.Geometry.movingBoxVelocity_jointSmooth
