-- Prove2me | solution 1 for GlobalTheory.CoordShear.measurePreserving_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:11.121029+00:00
-- url     : https://prove2.me/submissions/d9291bd7-8cd1-4da8-9802-6aed9182b326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalField
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.CoordShear
namespace GlobalTheory.CoordShear
theorem _root_.solution {k : Type} [AddCommGroup k] [MeasurableSpace k] [MeasurableAdd₂ k]
    (ν : Measure k) [SigmaFinite ν] [ν.IsAddLeftInvariant]
    {J : Type} [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k))
    (hg : Measurable g) (h1 : ∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y')
    (h2 : ∀ (y : J → k) j, j ∉ S → g y j = 0) :
    MeasurePreserving (fun y => y + g y) (Measure.pi fun _ : J => ν) (Measure.pi fun _ : J => ν) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => k) (fun j => j ∉ S) with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : J => ν)
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : J => ν) (fun j => j ∉ S)
  let G : ({j // j ∉ S} → k) → ({j // ¬ j ∉ S} → k) := fun b i => g (e.symm (b, 0)) i
  have hG : Measurable G := by
    refine measurable_pi_lambda _ fun i => ?_
    exact (measurable_pi_apply (i : J)).comp
      (hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hΦ : MeasurePreserving
      (fun p : ({j // j ∉ S} → k) × ({j // ¬ j ∉ S} → k) => (id p.1, G p.1 + p.2))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) := by
    refine (MeasurePreserving.id _).skew_product (g := fun b a => G b + a) ?_ ?_
    · exact (hG.comp measurable_fst).add measurable_snd
    · exact Filter.Eventually.of_forall fun b => (measurePreserving_add_left _ (G b)).map_eq

  have hGy : ∀ y : J → k, g (e.symm ((e y).1, 0)) = g y := by
    intro y
    refine h1 _ _ fun j hj => ?_
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have key : (fun y => y + g y) = e.symm ∘ (fun p => (id p.1, G p.1 + p.2)) ∘ e := by
    funext y
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h2 y i i.2]
    · have := congrFun (hGy y) i
      simp only [G, Pi.add_apply]
      rw [this]
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, add_comm]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΦ.comp he_mp)
end GlobalTheory.CoordShear
