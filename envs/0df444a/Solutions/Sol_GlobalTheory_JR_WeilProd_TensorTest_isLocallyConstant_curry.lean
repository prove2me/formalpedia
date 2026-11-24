-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.isLocallyConstant_curry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:11.338349+00:00
-- url     : https://prove2.me/submissions/9a44365d-29bc-4f68-983f-b8b4ebc061bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd GlobalTheory.JR.WeilProd.TensorTest
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace GlobalTheory.JR.WeilProd.TensorTest
theorem _root_.solution {f : X × Y → ℂ} (hf : IsTest f) :
    IsLocallyConstant (fun u => fun v => f (u, v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have hK : IsCompact (Prod.snd '' tsupport f) := hf.2.isCompact.image continuous_snd
  have hev : ∀ᶠ u in 𝓝 u₀, ∀ v ∈ Prod.snd '' tsupport f, f (u, v) = f (u₀, v) := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro y _
    have h1 : ∀ᶠ z in 𝓝 (u₀, y), f z = f (u₀, y) := ((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y)
    have hc : Continuous (fun z : X × Y => (u₀, z.2)) := (continuous_const.prodMk continuous_id).comp continuous_snd
    have ht : Tendsto (fun z : X × Y => (u₀, z.2)) (𝓝 (u₀, y)) (𝓝 (u₀, y)) := hc.continuousAt
    have h2 : ∀ᶠ z in 𝓝 (u₀, y), f (u₀, z.2) = f (u₀, y) :=
      ht.eventually (((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y))
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  filter_upwards [hev] with u hu
  funext v
  by_cases hv : v ∈ Prod.snd '' tsupport f
  · exact hu v hv
  · have hA : (u, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    have hB : (u₀, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]
end GlobalTheory.JR.WeilProd.TensorTest
