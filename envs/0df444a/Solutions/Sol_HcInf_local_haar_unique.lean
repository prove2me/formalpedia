-- Prove2me | solution 1 for HcInf.local_haar_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:35.681359+00:00
-- url     : https://prove2.me/submissions/db34cbc4-3d6c-4584-8851-82d0489b546a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExLHU
import Theorems.Thm_HcInf_lhu_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace HcInf
theorem _root_.solution : LocalHaarUnique := by
  intro G _ _ _ _ _ _ _ _ m hm β W hWo h1W hinv hfin hβW
  have hU : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (hWo.mem_nhds h1W) (hWo.inv.mem_nhds (by simpa using h1W))
  obtain ⟨V, hV1, hVsub, hVc⟩ := local_compact_nhds hU
  have hVW : V ⊆ W := fun x hx => (hVsub hx).1
  have hVW' : ∀ v ∈ V, v⁻¹ ∈ W := fun v hv => (hVsub hv).2
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hβV : β V ≠ ⊤ := hfin V hVc hVW
  have hβVi : β V⁻¹ ≠ ⊤ := hfin V⁻¹ hVc.inv (fun x hx => by simpa using hVW' x⁻¹ hx)
  have h1V : (1 : G) ∈ interior V := mem_interior_iff_mem_nhds.2 hV1
  have hmV0 : m V ≠ 0 :=
    ((isOpen_interior.measure_pos m ⟨1, h1V⟩).trans_le (measure_mono interior_subset)).ne'
  have hmVt : m V ≠ ⊤ := hVc.measure_lt_top.ne

  have hβV0 : β V ≠ 0 := by
    intro h0
    apply hβW
    let U : G → Set G := fun w => W ∩ (fun x => w⁻¹ * x) ⁻¹' interior V
    have hUo : ∀ w, IsOpen (U w) := fun w =>
      hWo.inter (isOpen_interior.preimage (continuous_const.mul continuous_id))
    have hU0 : ∀ w, β (U w) = 0 := by
      intro w
      have hSm : MeasurableSet ((fun x => w * x) ⁻¹' U w) :=
        measurable_const_mul w (hUo w).measurableSet
      have hSV : (fun x => w * x) ⁻¹' U w ⊆ V := by
        intro x hx
        have hx2 := hx.2
        simp only [Set.mem_preimage, inv_mul_cancel_left] at hx2
        exact interior_subset hx2
      have himg : (fun g => w * g) '' ((fun x => w * x) ⁻¹' U w) = U w :=
        Set.image_preimage_eq _ (mul_left_surjective w)
      have h := hinv w _ hSm (hSV.trans hVW) (by rw [himg]; exact fun y hy => hy.1)
      rw [himg] at h
      rw [h]
      exact measure_mono_null hSV h0
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
    have hWU : W ⊆ ⋃ w ∈ T, U w := by
      rw [hTU]
      intro x hx
      exact Set.mem_iUnion.2 ⟨x, hx, by simpa using h1V⟩
    exact measure_mono_null hWU ((measure_biUnion_null_iff hTc).2 (fun w _ => hU0 w))
  obtain ⟨K, hK⟩ := lhu_key m β W V hinv hVc hVW hVW' hβV hβVi
  refine ⟨β V / m V, (ENNReal.div_pos hβV0 hmVt).ne', ENNReal.div_ne_top hβV hmV0, V, hV1, hVW, ?_⟩
  ext s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  have h1 := hK (s ∩ V) (hs.inter hVm) (fun x hx => hx.2)
  have h2 := hK V hVm subset_rfl
  have e1 : β (s ∩ V) = (m V)⁻¹ * (K * m (s ∩ V)) := by
    rw [← h1, ← mul_assoc, ENNReal.inv_mul_cancel hmV0 hmVt, one_mul]
  have e2 : β V = (m V)⁻¹ * (K * m V) := by
    rw [← h2, ← mul_assoc, ENNReal.inv_mul_cancel hmV0 hmVt, one_mul]
  rw [e1, div_eq_mul_inv, e2]
  calc (m V)⁻¹ * (K * m (s ∩ V)) = (m V)⁻¹ * K * (m V * (m V)⁻¹) * m (s ∩ V) := by
        rw [ENNReal.mul_inv_cancel hmV0 hmVt, mul_one, mul_assoc]
    _ = (m V)⁻¹ * (K * m V) * (m V)⁻¹ * m (s ∩ V) := by ring
end HcInf
