-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.nonlinear_stabilized_regularity_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:09:23.708681+00:00
-- url     : https://prove2.me/submissions/5d9ec842-8288-4476-a365-af89048f8eda

import Mathlib

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
variable {X E F D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma nonlinear_stabilized_regularity_bp240_oai {f : E → F} (hf : ContDiff ℝ ∞ f)
    {P : E →L[ℝ] F} {v : X → E} {x : X} (hP : HasFDerivAt f P (v x))
    (Q : E →L[ℝ] D) (L : F × D →L[ℝ] E) (hL : LeftInverse L (P.prod Q))
    (hv : ContinuousAt v x) (hQ : ContDiffAt ℝ ∞ (fun t => Q (v t)) x)
    (he : ∀ᶠ t in 𝓝 x, f (v t)=0) : ContDiffAt ℝ ∞ v x := by
  let G : E → E := fun y => L (f y,Q y)
  have hG : ContDiff ℝ ∞ G := L.contDiff.comp (hf.prodMk Q.contDiff)
  have hd : HasFDerivAt G (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap (v x) := by
    have hh := L.hasFDerivAt.comp (v x) (hP.prodMk (Q.hasFDerivAt (x := v x)))
    have h : L.comp (P.prod Q) = (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap := by
      ext y
      exact hL y
    exact h ▸ hh
  let e := hG.contDiffAt.toOpenPartialHomeomorph G hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hm : v x ∈ e.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hG.contDiffAt hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hs : ContDiffAt ℝ ∞ e.symm (G (v x)) :=
    ContDiffAt.to_localInverse hG.contDiffAt hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hval : G (v x)=L (0,Q (v x)) := by
    change L (f (v x),Q (v x)) = _
    rw [he.self_of_nhds]
  have hout : ContDiffAt ℝ ∞ (fun t => e.symm (L (0,Q (v t)))) x := by
    rw [hval] at hs
    exact hs.comp x (L.contDiff.contDiffAt.comp x (contDiffAt_const.prodMk hQ))
  apply hout.congr_of_eventuallyEq
  have hn : ∀ᶠ t in 𝓝 x, v t∈e.source := hv.eventually (e.open_source.mem_nhds hm)
  filter_upwards [hn,he] with t ht ht0
  have hh := e.left_inv ht
  change e.symm (G (v t))=v t at hh
  change v t=e.symm (L (0,Q (v t)))
  calc
    v t = e.symm (G (v t)) := hh.symm
    _ = e.symm (L (0,Q (v t))) := by
      apply congrArg e.symm
      change L (f (v t),Q (v t))=L (0,Q (v t))
      rw [ht0]

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.nonlinear_stabilized_regularity_bp240_oai.{u_1, u_2, u_3, u_4} := @OAI.HigherDimensionalBallPacking.Rigidity.nonlinear_stabilized_regularity_bp240_oai.{u_1, u_2, u_3, u_4}
