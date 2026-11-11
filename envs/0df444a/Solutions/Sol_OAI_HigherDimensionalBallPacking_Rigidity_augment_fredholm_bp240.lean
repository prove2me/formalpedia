-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:47:23.68971+00:00
-- url     : https://prove2.me/submissions/5bd3e58b-d5e5-4718-84b5-248ed485b42a

import Mathlib
import Definitions.Def_OAIQ240Bp007

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (hD : D.IsFredholm)
  (E : Submodule ℝ Y) [FiniteDimensional ℝ E]

include hD in
omit [CompleteSpace Y] in
lemma finite_ker_augment [CompleteSpace Y] : FiniteDimensional ℝ (D.coprod E.subtypeL).ker := by
  obtain ⟨pkg⟩ := hD.nonempty_fredholmPackage
  let : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  let G := D.coprod E.subtypeL
  let A : X × E →L[ℝ] pkg.decDom.X₀ × E :=
    ((ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp
      ((domCoords pkg).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ X E))).prod
        (ContinuousLinearMap.snd ℝ X E)
  let AK := A.comp G.ker.subtypeL
  have hAK : Injective AK := by
    intro v w he
    change (((domCoords pkg) v.val.1).2,v.val.2)=(((domCoords pkg) w.val.1).2,w.val.2) at he
    have hk : ((domCoords pkg) v.val.1).2=((domCoords pkg) w.val.1).2 := congrArg (Prod.fst : pkg.decDom.X₀ × E → pkg.decDom.X₀) he
    have hee : v.val.2=w.val.2 := congrArg (Prod.snd : pkg.decDom.X₀ × E → E) he
    have hv : D v.val.1+(v.val.2:Y)=0 := v.property
    have hw : D w.val.1+(w.val.2:Y)=0 := w.property
    have hxx : D v.val.1=D w.val.1 := add_right_cancel (hv.trans hw.symm |>.trans (by rw [hee]))
    have hc := congrArg (fun y => ((codCoords pkg) y).1) hxx
    simp only [fredholm_original_coords] at hc
    have hx1 := pkg.equiv.injective hc
    apply Subtype.ext
    exact Prod.ext ((domCoords pkg).injective (Prod.ext hx1 hk)) hee
  exact FiniteDimensional.of_injective AK.toLinearMap hAK

include hD in
lemma augment_fredholm_bp240_oai (hG : Surjective (D.coprod E.subtypeL)) :
    (D.coprod E.subtypeL).IsFredholm := by
  let G := D.coprod E.subtypeL
  let : FiniteDimensional ℝ G.ker := finite_ker_augment hD E
  have htop : G.range=⊤ := LinearMap.range_eq_top.mpr hG
  refine ⟨(G.isOpenMap hG).isStrictMap G.continuous,?_,inferInstance,?_,?_⟩
  · rw [htop]
    exact isClosed_univ
  · rw [htop]
    infer_instance
  · exact Submodule.ClosedComplemented.of_finiteDimensional _

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm_bp240_oai.{u_1, u_2} := @OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm_bp240_oai.{u_1, u_2}
