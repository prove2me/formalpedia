-- Prove2me | solution 1 for OAI.EuclideanFiveColor.five_local_palette
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:59:25.11205+00:00
-- url     : https://prove2.me/submissions/084cb0dd-2c18-4d32-8b88-a763da031b32

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_fiveState_diag

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteDensity
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
namespace EuclideanFiveColor
lemma angleMk_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving ((↑) : ℝ → Angles) volume angularMeasure := by
  have hm : Measurable ((↑) : ℝ → Angles) := (AddCircle.measurePreserving_mk (2*Real.pi) 0).measurable
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply hm hA]
  have hzv : (volume : Measure Angles) A=0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,Measure.smul_apply]
    change ENNReal.ofReal (2*Real.pi) * angularMeasure A=0
    rw [hz,mul_zero]
  have hh (n : ℤ) : volume (((↑) : ℝ → Angles) ⁻¹' A ∩
      Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)))=0 := by
    have h := (AddCircle.measurePreserving_mk (2*Real.pi) (n • (2*Real.pi))).quasiMeasurePreserving.preimage_null hzv
    rw [Measure.restrict_apply' measurableSet_Ioc] at h
    simpa only [add_zsmul,one_zsmul] using h
  have hcov := iUnion_Ioc_zsmul (by positivity : 0 < 2*Real.pi)
  have he : ((↑) : ℝ → Angles) ⁻¹' A = ⋃ n : ℤ,
      ((↑) : ℝ → Angles) ⁻¹' A ∩ Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)) := by
    rw [← inter_iUnion,hcov,inter_univ]
  rw [he]
  exact measure_iUnion_null hh
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Accumulation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma palette_eq_measurable (x : ℂ) (p : Finset (Fin 5)) :
    MeasurableSet {t | palette c hc x t=p} := by
  simp only [Finset.ext_iff,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i∈p
  · simpa only [hi,iff_true,mem_palette,Set.ofPred_mem_eq] using paletteSet_measurable c hc x i
  · simpa only [hi,iff_false,mem_palette,← Set.mem_compl_iff,Set.ofPred_mem_eq] using (paletteSet_measurable c hc x i).compl
lemma fiveState_measurable (x : ℂ) : Measurable (fiveState c hc x) := by
  exact Measurable.ite (palette_eq_measurable c hc x _) measurable_const
    (Measurable.ite (palette_eq_measurable c hc x _) measurable_const
      (Measurable.ite (palette_eq_measurable c hc x _) measurable_const
        (Measurable.ite (palette_eq_measurable c hc x _) measurable_const measurable_const)))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FiveSupport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
lemma ae_mem_stateSupport {f : ℝ → ι} (hf : Measurable f) (i : ι) :
    ∀ᵐt : ℝ∂volume,f t=i → t∈stateSupport f i :=
  (ae_restrict_iff' (measurableSet_eq_fun hf measurable_const)).mp
    (volume.restrict {t | f t=i}).support_mem_ae
lemma ae_state_support {f : ℝ → ι} (hf : Measurable f) :
    ∀ᵐt : ℝ∂volume,t∈stateSupport f (f t) := by
  have h : ∀ᵐt : ℝ∂volume,∀i : ι,f t=i → t∈stateSupport f i :=
    ae_all_iff.mpr (fun i => ae_mem_stateSupport hf i)
  exact h.mono fun t ht => ht (f t) rfl
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
variable {ι X : Type*} [Finite ι] [TopologicalSpace X]
lemma finite_closed_family_locally_subset {S : ι → Set X} (hS : ∀i,IsClosed (S i)) (a : X) :
    ∃V,IsOpen V ∧ a∈V ∧ ∀v∈V,∀i,v∈S i → a∈S i := by
  let V := ⋂i∈({i | a∉S i} : Set ι),(S i)ᶜ
  have hop : IsOpen V := (Set.toFinite _).isOpen_biInter (fun i _ => (hS i).isOpen_compl)
  refine ⟨V,hop,?_,?_⟩
  · exact mem_iInter₂.mpr (fun _ hi => hi)
  · intro v hv i hi
    by_contra hn
    exact mem_iInter₂.mp hv i hn hi
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma stateSupport_local_pred {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {f : ℝ → ι} (hf : Measurable f) {P : ι → Prop} {a : ℝ}
    (ha : ∀i,a∈stateSupport f i → P i) :
    ∃V,IsOpen V ∧ a∈V ∧ ∀ᵐt : ℝ∂volume,t∈V → P (f t) := by
  obtain ⟨V,hV,haV,hsub⟩ := finite_closed_family_locally_subset
    (S := stateSupport f) (fun _ => Measure.isClosed_support) a
  refine ⟨V,hV,haV,?_⟩
  exact (ae_state_support hf).mono fun t ht hv => ha _ (hsub t hv _ ht)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CyclicCore
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_real_diag (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) :
    ∀ᵐt : ℝ∂volume,palette c hc x (t : Angles)=fiveDiag (fiveState c hc x (t : Angles)) :=
  angleMk_quasiMeasurePreserving.ae (fiveState_diag c hc hw hx)
lemma five_local_palette_oai (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {k : Fin 5}
    (hk : ∀i,a∈fiveSupport c hc x i → k∈fiveDiag i) :
    ∃V, IsOpen V ∧ a∈V ∧ ∀ᵐt : ℝ∂volume,t∈V → (t : Angles)∈paletteSet c hc x k := by
  obtain ⟨V,hV,ha,hkV⟩ := stateSupport_local_pred
    ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) hk
  refine ⟨V,hV,ha,?_⟩
  filter_upwards [hkV,five_real_diag c hc hw hx] with t ht hd htv
  apply (mem_palette c hc x (t : Angles) k).mp
  rw [hd]
  exact ht htv
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.five_local_palette_oai := @OAI.EuclideanFiveColor.five_local_palette_oai
