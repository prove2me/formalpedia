-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteIdeleNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:59:32.525961+00:00
-- url     : https://prove2.me/submissions/91bc9757-2ea2-40ee-a43d-4965b2efc1a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
theorem _root_.solution : Continuous (finiteIdeleNorm (E := E)) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
      fun _ => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun x : Idele E => x.val.2 := continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun x : Idele E => (x⁻¹).val.2 := h1.comp continuous_inv
  have key : ∀ y : Idele E, (∀ v, y.val.2 v ∈ v.adicCompletionIntegers E) →
      (∀ v, (y⁻¹).val.2 v ∈ v.adicCompletionIntegers E) → finiteIdeleNorm y = 1 := by
    intro y hy hy'
    refine finprod_eq_one_of_forall_eq_one fun v => norm_eq_one_of_valued ?_
    have e : y.val.2 v * (y⁻¹).val.2 v = 1 :=
      congrArg (fun a : AdeleRing (𝓞 E) E => a.2 v) y.mul_inv
    have e' := congrArg Valued.v e
    rw [map_mul, map_one] at e'
    exact eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hc : Continuous fun y : Idele E => x⁻¹ * y := continuous_const.mul continuous_id
  have hU := (hO.preimage (h1.comp hc)).inter (hO.preimage (h2.comp hc))
  refine (continuousAt_const (y := finiteIdeleNorm x)).congr ?_
  filter_upwards [hU.mem_nhds (x := x) ⟨fun v => by
    simp only [Function.comp_apply, inv_mul_cancel]; exact one_mem _, fun v => by
    simp only [Function.comp_apply, inv_mul_cancel, inv_one]; exact one_mem _⟩] with y hy
  have := key _ hy.1 hy.2
  rw [← mul_one (finiteIdeleNorm x), ← this, ← map_mul, mul_inv_cancel_left]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
