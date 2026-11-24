-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:40.667075+00:00
-- url     : https://prove2.me/submissions/d6161884-621a-4fbe-97ec-45848befc45a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulInvariantMeasureShearedProductPairGroup
import Theorems.Thm_GlobalTheory_UnfoldNormal_measurableEmbedding_shear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
open GlobalTheory GlobalTheory.UnfoldNormal
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (hκ : κ.IsHaarMeasure)
    (hconj : ∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) :
    SMulInvariantMeasure (pairGroup Γ N hN) (H × H) ((κ.prod ν).map (shear N)) := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  refine ⟨fun g s hs => ?_⟩
  obtain ⟨⟨u, v⟩, hu, hv, huv⟩ := g
  have hmeasg : Measurable (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) := by
    change Measurable (fun x : H × H => (u * x.1, v * x.2))
    exact (measurable_fst.const_mul u).prodMk (measurable_snd.const_mul v)
  let δ : N := ⟨u * v⁻¹, huv⟩
  let c : N → N := fun n => ⟨v * n * v⁻¹, hN v hv n n.2⟩
  have hc : MeasurePreserving c κ κ :=
    ⟨(show Continuous c from ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _).measurable,
      hconj v hv⟩
  have hf : MeasurePreserving (fun n : N => δ * c n) κ κ := (measurePreserving_mul_left κ δ).comp hc
  have hT : MeasurePreserving (Prod.map (fun n : N => δ * c n) (fun h : H => v * h)) (κ.prod ν) (κ.prod ν) :=
    hf.prod (measurePreserving_mul_left ν v)
  have hsh := (measurableEmbedding_shear (N := N) hNc)
  have key : (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) ∘ shear N
      = shear N ∘ Prod.map (fun n : N => δ * c n) (fun h : H => v * h) := by
    funext p
    change (u * (p.1 * p.2), v * p.2) = (((u * v⁻¹) * (v * p.1 * v⁻¹)) * (v * p.2), v * p.2)
    congr 1
    group
  rw [← Measure.map_apply hmeasg hs, Measure.map_map hmeasg hsh.measurable, key,
    ← Measure.map_map hsh.measurable hT.measurable, hT.map_eq]
end GlobalTheory.UnfoldNormal
