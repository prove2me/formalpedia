-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3e186877-c83d-539a-ba89-d7354bf14e1f

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure NumberField IsDedekindDomain Set Filter Topology
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure.LanglandsTunnell.TateLocal"

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.mulMeasure TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "modulus modulus_coe_units modulus_ne_zero modulus_mul mulMeasure modulus_adicCompletion_eq_nnnorm"
namespace MulHaarLocal
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

theorem range_val : Set.range (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩

theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  rw [range_val]
  exact isClosed_singleton.isOpen_compl

theorem image_val_subset_compl_zero (A : Set (v.adicCompletion K)ˣ) :
    (Units.val '' A) ⊆ ({0}ᶜ : Set (v.adicCompletion K)) := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

theorem image_val_smul (g : (v.adicCompletion K)ˣ) (A : Set (v.adicCompletion K)ˣ) :
    Units.val '' (g • A) = (g : v.adicCompletion K) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(a : v.adicCompletion K), ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g * a, ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩

theorem smul_set_eq_preimage {c : v.adicCompletion K} (hc : c ≠ 0) (T : Set (v.adicCompletion K)) :
    c • T = (fun y => c⁻¹ * y) ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

theorem modulus_eq_nnnorm (x : v.adicCompletion K) : modulus x = ‖x‖₊ :=
  LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x

theorem modulus_units_ne_zero (u : (v.adicCompletion K)ˣ) : modulus (u : v.adicCompletion K) ≠ 0 :=
  modulus_ne_zero u.ne_zero

section MulMeasure

variable [MeasurableSpace (v.adicCompletion K)]

theorem mulMeasure_apply_of_subset (μ : Measure (v.adicCompletion K)) {T : Set (v.adicCompletion K)}
    (hT : MeasurableSet T) (hT0 : T ⊆ ({0}ᶜ : Set (v.adicCompletion K))) :
    mulMeasure μ T = ∫⁻ x in T, ((modulus x : ℝ≥0∞))⁻¹ ∂μ := by
  rw [mulMeasure, withDensity_apply _ hT, Measure.restrict_restrict hT, Set.inter_eq_left.mpr hT0]

variable [BorelSpace (v.adicCompletion K)]

theorem measurableSet_smul_set {c : v.adicCompletion K} (hc : c ≠ 0) {T : Set (v.adicCompletion K)}
    (hT : MeasurableSet T) : MeasurableSet (c • T) := by
  rw [smul_set_eq_preimage hc]
  exact hT.preimage (measurable_const_mul _)

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem map_mul_left_eq_smul (u : (v.adicCompletion K)ˣ) :
    μ.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x)
      = (distribHaarChar (v.adicCompletion K) u⁻¹ : ℝ≥0∞) • μ := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) ⁻¹' s
      = ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • s := by
    rw [smul_set_eq_preimage (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul μ (u⁻¹) s
  rw [show ((u⁻¹ : (v.adicCompletion K)ˣ) • s : Set (v.adicCompletion K))
      = ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • s from rfl] at h
  exact h.symm

theorem mulMeasure_units_smul (u : (v.adicCompletion K)ˣ) {T : Set (v.adicCompletion K)}
    (hT : MeasurableSet T) (hT0 : T ⊆ ({0}ᶜ : Set (v.adicCompletion K))) :
    mulMeasure μ ((u : v.adicCompletion K) • T) = mulMeasure μ T := by
  set c : v.adicCompletion K := (u : v.adicCompletion K) with hc
  have hc0 : c ≠ 0 := u.ne_zero
  have hcT : MeasurableSet (c • T) := measurableSet_smul_set hc0 hT
  have hcT0 : c • T ⊆ ({0}ᶜ : Set (v.adicCompletion K)) := by
    rintro x ⟨y, hy, rfl⟩
    exact mul_ne_zero hc0 (hT0 hy)
  set D : ℝ≥0 := distribHaarChar (v.adicCompletion K) u with hD
  have hD0 : (D : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr distribHaarChar_pos.ne'
  have hDtop : (D : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hDinv : distribHaarChar (v.adicCompletion K) u⁻¹ = D⁻¹ := by rw [map_inv]

  set g : v.adicCompletion K → ℝ≥0∞ := fun x => ((modulus x : ℝ≥0∞))⁻¹ with hg
  have hg_mul : ∀ x, g (c * x) = (D : ℝ≥0∞)⁻¹ * g x := by
    intro x
    simp only [hg]
    rw [modulus_mul, hc, modulus_coe_units, ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hD0) (Or.inl hDtop)]

  let e : v.adicCompletion K ≃ᵐ v.adicCompletion K := MeasurableEquiv.mulLeft₀ c hc0
  have he : (e : v.adicCompletion K → v.adicCompletion K) = fun x => c * x := rfl
  have hind : ∀ x, (c • T).indicator g (c * x) = T.indicator (fun y => (D : ℝ≥0∞)⁻¹ * g y) x := by
    intro x
    by_cases hx : x ∈ T
    · have hcx : c * x ∈ c • T := Set.mem_smul_set.mpr ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hcx, hg_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      intro hcx
      obtain ⟨y, hy, hxy⟩ := Set.mem_smul_set.mp hcx
      exact hx ((mul_left_cancel₀ hc0 hxy) ▸ hy)
  have h1 : ∫⁻ x, (c • T).indicator g x ∂(μ.map e) = ∫⁻ x, (c • T).indicator g (c * x) ∂μ :=
    lintegral_map_equiv _ e
  rw [he, map_mul_left_eq_smul μ u, hDinv, lintegral_smul_measure] at h1
  simp_rw [hind] at h1
  rw [lintegral_indicator hcT, lintegral_indicator hT, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hD0),
    ← mulMeasure_apply_of_subset μ hcT hcT0, ← mulMeasure_apply_of_subset μ hT hT0] at h1
  have hDi0 : ((D⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (inv_ne_zero distribHaarChar_pos.ne')
  rw [ENNReal.coe_inv distribHaarChar_pos.ne', smul_eq_mul] at h1
  rw [ENNReal.coe_inv distribHaarChar_pos.ne'] at hDi0
  exact (ENNReal.mul_right_inj hDi0 (ENNReal.inv_ne_top.mpr hD0)).mp h1

end MulMeasure

section Pullback

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]

theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) :=
  isOpenEmbedding_val.measurableEmbedding

theorem comap_val_apply (ρ : Measure (v.adicCompletion K)) (A : Set (v.adicCompletion K)ˣ) :
    Measure.comap Units.val ρ A = ρ (Units.val '' A) :=
  measurableEmbedding_val.comap_apply ρ A

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem isMulLeftInvariant_comap : (Measure.comap Units.val (mulMeasure μ)).IsMulLeftInvariant := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  have hpre : (fun h => g * h) ⁻¹' A = g⁻¹ • A := by
    ext a
    simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  rw [hpre, comap_val_apply, comap_val_apply, image_val_smul]
  exact mulMeasure_units_smul μ g⁻¹ (measurableEmbedding_val.measurableSet_image' hA)
    (image_val_subset_compl_zero A)

theorem isFiniteMeasureOnCompacts_comap : IsFiniteMeasureOnCompacts (Measure.comap Units.val (mulMeasure μ)) := by
  haveI : T2Space (v.adicCompletion K)ˣ := Units.isEmbedding_val₀.t2Space
  refine ⟨fun C hC => ?_⟩
  rw [comap_val_apply]
  set C' : Set (v.adicCompletion K) := Units.val '' C with hC'
  have hC'c : IsCompact C' := hC.image Units.continuous_val
  have hC'0 : C' ⊆ ({0}ᶜ : Set (v.adicCompletion K)) := image_val_subset_compl_zero C
  have hC'm : MeasurableSet C' := hC'c.isClosed.measurableSet
  rcases C'.eq_empty_or_nonempty with hCe | hCne
  · rw [hCe, measure_empty]
    exact ENNReal.zero_lt_top
  obtain ⟨x₀, hx₀, hmin⟩ := hC'c.exists_isMinOn hCne continuous_norm.continuousOn
  have hx₀0 : x₀ ≠ 0 := hC'0 hx₀
  set δ : ℝ≥0 := ‖x₀‖₊ with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ] using hx₀0
  have hbound : ∀ x ∈ C', ((modulus x : ℝ≥0∞))⁻¹ ≤ (δ : ℝ≥0∞)⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr ?_)
    rw [modulus_eq_nnnorm]
    have h := hmin hx
    simp only [Set.mem_setOf_eq] at h
    exact h
  rw [mulMeasure_apply_of_subset μ hC'm hC'0]
  calc ∫⁻ x in C', ((modulus x : ℝ≥0∞))⁻¹ ∂μ
      ≤ ∫⁻ _x in C', (δ : ℝ≥0∞)⁻¹ ∂μ := setLIntegral_mono' hC'm hbound
    _ = (δ : ℝ≥0∞)⁻¹ * μ C' := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hδ0)))
        hC'c.measure_lt_top

theorem isOpenPosMeasure_comap : (Measure.comap Units.val (mulMeasure μ)).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [comap_val_apply]
  obtain ⟨u₀, hu₀⟩ := hne
  set U' : Set (v.adicCompletion K) := Units.val '' U with hU'
  have hU'o : IsOpen U' := isOpenEmbedding_val.isOpenMap _ hU
  have hU'0 : U' ⊆ ({0}ᶜ : Set (v.adicCompletion K)) := image_val_subset_compl_zero U
  set W : Set (v.adicCompletion K) := U' ∩ Metric.ball (u₀ : v.adicCompletion K) 1 with hW
  have hWo : IsOpen W := hU'o.inter Metric.isOpen_ball
  have hW0 : W ⊆ ({0}ᶜ : Set (v.adicCompletion K)) := inter_subset_left.trans hU'0
  have hWne : W.Nonempty := ⟨(u₀ : v.adicCompletion K), ⟨u₀, hu₀, rfl⟩, Metric.mem_ball_self one_pos⟩
  set R : ℝ≥0 := ‖(u₀ : v.adicCompletion K)‖₊ + 1 with hR
  have hbound : ∀ x ∈ W, (R : ℝ≥0∞)⁻¹ ≤ ((modulus x : ℝ≥0∞))⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr ?_)
    rw [modulus_eq_nnnorm]
    have hd : dist x (u₀ : v.adicCompletion K) < 1 := Metric.mem_ball.mp hx.2
    have h1 : ‖x‖ ≤ ‖(u₀ : v.adicCompletion K)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x (u₀ : v.adicCompletion K)
      rw [← dist_eq_norm] at this
      linarith
    rw [← NNReal.coe_le_coe]
    push_cast
    exact h1
  have hWpos : 0 < μ W := hWo.measure_pos μ hWne
  have hlow : (R : ℝ≥0∞)⁻¹ * μ W ≤ mulMeasure μ U' := by
    calc (R : ℝ≥0∞)⁻¹ * μ W = ∫⁻ _x in W, (R : ℝ≥0∞)⁻¹ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in W, ((modulus x : ℝ≥0∞))⁻¹ ∂μ := setLIntegral_mono' hWo.measurableSet hbound
      _ = mulMeasure μ W := (mulMeasure_apply_of_subset μ hWo.measurableSet hW0).symm
      _ ≤ mulMeasure μ U' := measure_mono inter_subset_left
  have hR0 : (R : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  exact (lt_of_lt_of_le (ENNReal.mul_pos hR0 hWpos.ne') hlow).ne'

end Pullback

end LanglandsTunnell.TateLocal.MulHaarLocal

end

open MeasureTheory NumberField IsDedekindDomain _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure.LanglandsTunnell.TateLocal in

theorem solution (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] :
    (Measure.comap Units.val (mulMeasure μ) : Measure (v.adicCompletion K)ˣ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := MulHaarLocal.isFiniteMeasureOnCompacts_comap μ
    toIsMulLeftInvariant := MulHaarLocal.isMulLeftInvariant_comap μ
    toIsOpenPosMeasure := MulHaarLocal.isOpenPosMeasure_comap μ }

end S_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure (solution)
