-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.integral_shear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:18.173449+00:00
-- url     : https://prove2.me/submissions/1a21181c-ed71-4ee4-8f69-ec3a0c988b6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [T2Space k]
  [SecondCountableTopology k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]
omit [T2Space k]
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution {I : Type} [Fintype I] (J : I → Prop) (S : (I → k) → (I → k))
    (hS : Continuous S) (h0 : ∀ e i, ¬ J i → S e i = 0)
    (h1 : ∀ e e' : I → k, (∀ i, ¬ J i → e i = e' i) → S e = S e')
    (f : (I → k) → ℂ) (hf : Continuous f) :
    ∫ e, f (e + S e) ∂(Measure.pi fun _ => ν) = ∫ e, f e ∂(Measure.pi fun _ => ν) := by
  classical
  have hE := measurePreserving_piEquivPiSubtypeProd (fun _ : I => ν) (fun i => ¬ J i)
  set E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => k) (fun i => ¬ J i) with hEdef
  let g : ({i // ¬ J i} → k) → ({i // ¬ ¬ J i} → k) → ({i // ¬ ¬ J i} → k) :=
    fun a b => b + fun i => S (E.symm (a, 0)) i.1
  have hgm : Measurable (Function.uncurry g) := by
    refine measurable_snd.add (measurable_pi_lambda _ fun i => ?_)
    exact (measurable_pi_apply i.1).comp (hS.measurable.comp
      (E.symm.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hT := (MeasurePreserving.id (Measure.pi fun _ : {i // ¬ J i} => ν)).skew_product
    (μc := Measure.pi fun _ : {i // ¬ ¬ J i} => ν) (μd := Measure.pi fun _ : {i // ¬ ¬ J i} => ν) hgm
    (Filter.Eventually.of_forall fun a => map_add_right_eq_self _ _)
  have hall := (hE.symm E).comp (hT.comp hE)
  have heq : (fun e : I → k => e + S e) = E.symm ∘ (fun p => (id p.1, g p.1 p.2)) ∘ E := by
    funext e
    have : S (E.symm ((E e).1, 0)) = S e := by
      apply h1
      intro i hi
      simp [hEdef, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
    funext i
    simp only [Function.comp, g, this, id]
    by_cases hi : J i
    · simp [hEdef, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
    · simp [hEdef, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi, h0 e i hi]
  rw [← heq] at hall
  conv_rhs => rw [← hall.map_eq]
  rw [integral_map hall.measurable.aemeasurable hf.aestronglyMeasurable]
end GlobalTheory.RootEx.Exchange
