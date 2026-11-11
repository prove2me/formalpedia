-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.indexZero_finite_stabilizer_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:24.874227+00:00
-- url     : https://prove2.me/submissions/705f87d9-77f3-43b7-9bba-aa5c89b88e28

import Mathlib
import Definitions.Def_OAIQ240Bp017

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousLinearMap.FredholmPackage
open scoped _root_.ContinuousLinearMap _root_.ContinuousLinearMap.FredholmPackage
open Set Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {P : E →L[ℝ] F}

 theorem finitePerturbation_injective (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) :
    Injective (P+finitePerturbation pkg L) ↔ Injective L := by
  constructor
  · intro hi x y hxy
    have hh : (P+finitePerturbation pkg L) ((domCoords pkg).symm (0,x)) =
        (P+finitePerturbation pkg L) ((domCoords pkg).symm (0,y)) := by
      apply (codCoords pkg).injective
      rw [finitePerturbation_coords pkg,finitePerturbation_coords pkg,
        ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply,hxy]
    have h := congrArg (domCoords pkg) (hi hh)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,Prod.mk.injEq,true_and] using h
  · intro hi x y hxy
    apply (domCoords pkg).injective
    have hh := congrArg (codCoords pkg) hxy
    rw [finitePerturbation_coords pkg,finitePerturbation_coords pkg] at hh
    exact Prod.ext (pkg.equiv.injective (congrArg Prod.fst hh)) (hi (congrArg Prod.snd hh))

 theorem finitePerturbation_surjective (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) :
    Surjective (P+finitePerturbation pkg L) ↔ Surjective L := by
  constructor
  · intro hs y
    obtain ⟨x,hx⟩ := hs ((codCoords pkg).symm (0,y))
    refine ⟨((domCoords pkg) x).2,?_⟩
    have hh := congrArg (codCoords pkg) hx
    rw [finitePerturbation_coords pkg,ContinuousLinearEquiv.apply_symm_apply] at hh
    exact congrArg Prod.snd hh
  · intro hs y
    obtain ⟨x,hx⟩ := hs ((codCoords pkg) y).2
    refine ⟨(domCoords pkg).symm (pkg.equiv.symm ((codCoords pkg) y).1,x),?_⟩
    apply (codCoords pkg).injective
    rw [finitePerturbation_coords pkg,ContinuousLinearEquiv.apply_symm_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply,hx,Prod.mk.eta]

end ContinuousLinearMap.FredholmPackage

end

end OAI
end

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

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
section Generic
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {D : X →L[ℝ] Y}
lemma fredholmPackage_balanced (pkg : D.FredholmPackage) (hi : IsIndexZeroFredholm D) :
    Module.finrank ℝ pkg.decDom.X₀ = Module.finrank ℝ pkg.decCodom.X₀ := by
  have h := hi.2
  rw [pkg.ker_eq,pkg.range_eq] at h
  exact h.trans (Submodule.quotientEquivOfIsCompl pkg.decCodom.X₁ pkg.decCodom.X₀
    pkg.decCodom.isTopCompl.isCompl).finrank_eq

end Generic

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma indexZero_finite_stabilizer_bp240_oai {D : X →L[ℝ] Y} (hD : IsIndexZeroFredholm D) :
    ∃ E : Submodule ℝ Y,FiniteDimensional ℝ E ∧
      ∃ P : X →L[ℝ] E,(D+E.subtypeL.comp P).IsInvertible := by
  obtain ⟨pkg⟩ := hD.1.nonempty_fredholmPackage
  let : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  let : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
  let L : pkg.decDom.X₀ ≃L[ℝ] pkg.decCodom.X₀ :=
    ContinuousLinearEquiv.ofFinrankEq (fredholmPackage_balanced pkg hD)
  let P : X →L[ℝ] pkg.decCodom.X₀ := L.toContinuousLinearMap.comp
    (pkg.decDom.X₀.projectionOntoL _ pkg.decDom.isTopCompl.symm)
  have hinj : Injective (D+finitePerturbation pkg L.toContinuousLinearMap) :=
    (finitePerturbation_injective pkg L.toContinuousLinearMap).mpr L.injective
  have hsurj : Surjective (D+finitePerturbation pkg L.toContinuousLinearMap) :=
    (finitePerturbation_surjective pkg L.toContinuousLinearMap).mpr L.surjective
  refine ⟨pkg.decCodom.X₀,inferInstance,P,?_⟩
  let e := ContinuousLinearEquiv.ofBijective (D+finitePerturbation pkg L.toContinuousLinearMap)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨e,ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.indexZero_finite_stabilizer_bp240_oai.{u_1, u_2} := @OAI.HigherDimensionalBallPacking.Rigidity.indexZero_finite_stabilizer_bp240_oai.{u_1, u_2}
