-- Prove2me | solution 1 for NumberField.mixedEmbedding.fundamentalCone.setLIntegral_inv_norm_eq_volume_normLeOne_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e26b70a5-320e-5ad0-8a67-1f6b06273d54

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log.NumberField NumberField.mixedEmbedding P2MW.S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log.NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log.NumberField.mixedEmbedding.fundamentalCone"
open scoped ENNReal Pointwise Classical

noncomputable section

namespace NumberField
p2m_export "NumberField" "mixedEmbedding.fundamentalCone mixedEmbedding.fundamentalCone.normLeOne mixedEmbedding mixedEmbedding.continuous_norm mixedEmbedding.norm mixedEmbedding.norm_smul mixedEmbedding.finrank mixedEmbedding.norm_nonneg"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "fundamentalCone fundamentalCone.normLeOne mixedSpace measurableSet_fundamentalCone norm_smul"
namespace fundamentalCone
p2m_export "NumberField.mixedEmbedding.fundamentalCone" "mem_normLeOne normLeOne isBounded_normLeOne smul_mem_iff_mem norm_pos_of_mem"
namespace ConeSlab
p2m_open "NumberField.mixedEmbedding.fundamentalCone NumberField.mixedEmbedding NumberField"

variable (K : Type) [Field K] [NumberField K]

theorem volume_normLeOne_ne_top : volume (normLeOne K) ≠ ⊤ :=
  (isBounded_normLeOne K).measure_lt_top.ne

theorem finrank_pos' : 0 < Module.finrank ℚ K := Module.finrank_pos

theorem inter_norm_le_eq_smul {T : ℝ} (hT : 0 < T) :
    fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ T} =
      (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • normLeOne K := by
  set r : ℝ := T ^ ((Module.finrank ℚ K : ℝ)⁻¹) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hT _
  have hrn : r ^ Module.finrank ℚ K = T := Real.rpow_inv_natCast_pow hT.le (finrank_pos' K).ne'
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hrpos.ne', mem_normLeOne, smul_mem_iff_mem (inv_ne_zero hrpos.ne'),
    mixedEmbedding.norm_smul, abs_of_pos (inv_pos.2 hrpos), inv_pow, hrn, Set.mem_inter_iff, Set.mem_setOf_eq,
    inv_mul_le_iff₀ hT, mul_one]

theorem volume_inter_norm_le {T : ℝ} (hT : 0 < T) :
    volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ T}) = ENNReal.ofReal T * volume (normLeOne K) := by
  rw [inter_norm_le_eq_smul K hT, Measure.addHaar_smul, mixedEmbedding.finrank,
    abs_of_nonneg (pow_nonneg (Real.rpow_nonneg hT.le _) _),
    Real.rpow_inv_natCast_pow hT.le (finrank_pos' K).ne']

theorem volume_inter_norm_lt {T : ℝ} (hT : 0 < T) :
    volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x < T}) = ENNReal.ofReal T * volume (normLeOne K) := by

  set s : ℕ → Set (mixedSpace K) := fun k =>
    fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ T * (1 - 1 / ((k : ℝ) + 2))} with hs
  have hc : ∀ k : ℕ, 0 < 1 - 1 / ((k : ℝ) + 2) := fun k => by
    have : (1 : ℝ) / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  have hmono : Monotone s := by
    intro k l hkl x hx
    have h1 : (1 : ℝ) / ((l : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 2)
    refine ⟨hx.1, ?_⟩
    have hx2 : mixedEmbedding.norm x ≤ T * (1 - 1 / ((k : ℝ) + 2)) := hx.2
    show mixedEmbedding.norm x ≤ T * (1 - 1 / ((l : ℝ) + 2))
    nlinarith
  have hunion : (⋃ k, s k) = fundamentalCone K ∩ {x | mixedEmbedding.norm x < T} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, hs]
    constructor
    · rintro ⟨k, hx, hle⟩
      refine ⟨hx, lt_of_le_of_lt hle ?_⟩
      have : T * (1 - 1 / ((k : ℝ) + 2)) < T * 1 :=
        mul_lt_mul_of_pos_left (by linarith [one_div_pos.2 (by positivity : (0 : ℝ) < (k : ℝ) + 2)]) hT
      simpa using this
    · rintro ⟨hx, hlt⟩

      have hq : 0 < 1 - mixedEmbedding.norm x / T := by
        rw [sub_pos, div_lt_one hT]; exact hlt
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - mixedEmbedding.norm x / T))
      refine ⟨k, hx, ?_⟩
      have hk2 : 1 / (1 - mixedEmbedding.norm x / T) < (k : ℝ) + 2 := by linarith
      have h3 : 1 / ((k : ℝ) + 2) < 1 - mixedEmbedding.norm x / T := by
        rw [one_div_lt (by positivity) hq]; exact hk2
      have h4 : mixedEmbedding.norm x / T < 1 - 1 / ((k : ℝ) + 2) := by linarith
      rw [div_lt_iff₀ hT] at h4
      linarith
  have h1 : Filter.Tendsto (volume ∘ s) Filter.atTop (nhds (volume (⋃ k, s k))) :=
    tendsto_measure_iUnion_atTop hmono
  have h2 : Filter.Tendsto (volume ∘ s) Filter.atTop (nhds (ENNReal.ofReal T * volume (normLeOne K))) := by
    have heq : (volume ∘ s) = fun k : ℕ =>
        ENNReal.ofReal (T * (1 - 1 / ((k : ℝ) + 2))) * volume (normLeOne K) := by
      funext k
      exact volume_inter_norm_le K (mul_pos hT (hc k))
    rw [heq]
    refine ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal ?_) (Or.inr (volume_normLeOne_ne_top K))
    have : Filter.Tendsto (fun k : ℕ => T * (1 - 1 / ((k : ℝ) + 2))) Filter.atTop (nhds (T * (1 - 0))) := by
      refine tendsto_const_nhds.mul (tendsto_const_nhds.sub ?_)
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h' : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) :=
        h.comp (Filter.tendsto_add_atTop_nat 1)
      refine h'.congr fun k => ?_
      push_cast; ring_nf
    simpa using this
  rw [← hunion]
  exact tendsto_nhds_unique h1 h2

theorem volume_slab_inter_norm_lt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {t : ℝ} (ht : 0 < t) :
    volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b} ∩
        {x | mixedEmbedding.norm x < t⁻¹}) =
      ENNReal.ofReal (min b t⁻¹ - a) * volume (normLeOne K) := by
  have hV := volume_normLeOne_ne_top K
  rcases le_or_gt t⁻¹ a with h1 | h1
  ·
    have hset : fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b} ∩
        {x | mixedEmbedding.norm x < t⁻¹} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨-, hax, -⟩, hlt⟩
      linarith
    have hle : min b t⁻¹ - a ≤ 0 := by
      have := min_le_right b t⁻¹; linarith
    rw [hset, measure_empty, ENNReal.ofReal_of_nonpos hle, zero_mul]
  ·
    have hsub : fundamentalCone K ∩ {x | mixedEmbedding.norm x < a} ⊆
        fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ b} ∩ {x | mixedEmbedding.norm x < t⁻¹} := by
      rintro x ⟨hx, hlt⟩
      exact ⟨⟨hx, le_trans (le_of_lt hlt) hab⟩, lt_trans hlt h1⟩
    have hset : fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b} ∩
        {x | mixedEmbedding.norm x < t⁻¹} =
        (fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ b} ∩ {x | mixedEmbedding.norm x < t⁻¹}) \
          (fundamentalCone K ∩ {x | mixedEmbedding.norm x < a}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_diff, not_and, not_lt]
      constructor
      · rintro ⟨⟨hx, hax, hxb⟩, hlt⟩
        exact ⟨⟨⟨hx, hxb⟩, hlt⟩, fun _ => hax⟩
      · rintro ⟨⟨⟨hx, hxb⟩, hlt⟩, h⟩
        exact ⟨⟨hx, h hx, hxb⟩, hlt⟩
    have hmeasN : Measurable (mixedEmbedding.norm : mixedSpace K → ℝ) := (mixedEmbedding.continuous_norm K).measurable
    have hmeas_a : MeasurableSet (fundamentalCone K ∩ {x | mixedEmbedding.norm x < a}) :=
      (measurableSet_fundamentalCone K).inter (measurableSet_lt hmeasN measurable_const)
    have hfin_a : volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x < a}) ≠ ⊤ := by
      rw [volume_inter_norm_lt K ha]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV
    rw [hset, measure_diff hsub hmeas_a.nullMeasurableSet hfin_a, volume_inter_norm_lt K ha]

    have hbig : volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ b} ∩ {x | mixedEmbedding.norm x < t⁻¹}) =
        ENNReal.ofReal (min b t⁻¹) * volume (normLeOne K) := by
      rcases le_or_gt t⁻¹ b with h2 | h2
      · have : fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ b} ∩ {x | mixedEmbedding.norm x < t⁻¹} =
            fundamentalCone K ∩ {x | mixedEmbedding.norm x < t⁻¹} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
          exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, le_trans h.2.le h2⟩, h.2⟩⟩
        rw [this, volume_inter_norm_lt K (inv_pos.2 ht), min_eq_right h2]
      · have : fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ b} ∩ {x | mixedEmbedding.norm x < t⁻¹} =
            fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ b} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
          exact ⟨fun h => h.1, fun h => ⟨h, lt_of_le_of_lt h.2 h2⟩⟩
        rw [this, volume_inter_norm_le K (lt_of_lt_of_le ha hab), min_eq_left h2.le]
    rw [hbig]
    have hmin : a ≤ min b t⁻¹ := le_min hab h1.le
    rw [ENNReal.ofReal_sub _ ha.le]
    rcases eq_or_lt_of_le hmin with heq | hlt
    · rw [← heq, tsub_self, tsub_self, zero_mul]
    · rw [ENNReal.sub_mul fun _ _ => hV]

theorem lintegral_ofReal_min_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min b t⁻¹ - a) = ENNReal.ofReal (Real.log (b / a)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hba : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha hab

  have hsplit : Set.Ioi (0 : ℝ) = (Set.Ioc 0 b⁻¹ ∪ Set.Ioc b⁻¹ a⁻¹) ∪ Set.Ioi a⁻¹ := by
    rw [Set.Ioc_union_Ioc_eq_Ioc (inv_pos.2 hb).le hba, Set.Ioc_union_Ioi_eq_Ioi (inv_pos.2 ha).le]
  rw [hsplit, lintegral_union measurableSet_Ioi, lintegral_union measurableSet_Ioc]
  rotate_left
  · exact Set.Ioc_disjoint_Ioc_of_le le_rfl
  · rw [Set.disjoint_left]
    rintro t (⟨-, ht⟩ | ⟨-, ht⟩) ht'
    · exact absurd (lt_of_le_of_lt (le_trans ht hba) ht') (lt_irrefl _)
    · exact absurd (lt_of_le_of_lt ht ht') (lt_irrefl _)

  have h1 : ∫⁻ t in Set.Ioc (0 : ℝ) b⁻¹, ENNReal.ofReal (min b t⁻¹ - a) =
      ENNReal.ofReal ((b - a) * b⁻¹) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (fun t ht => by rw [min_eq_left ((le_inv_comm₀ ht.1 hb).1 ht.2)] :
        ∀ t ∈ Set.Ioc (0 : ℝ) b⁻¹, ENNReal.ofReal (min b t⁻¹ - a) = ENNReal.ofReal (b - a)),
      setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by linarith), mul_comm]

  have h2 : ∫⁻ t in Set.Ioc b⁻¹ a⁻¹, ENNReal.ofReal (min b t⁻¹ - a) =
      ENNReal.ofReal (Real.log (a⁻¹ / b⁻¹) - a * (a⁻¹ - b⁻¹)) := by
    have hcongr : ∀ t ∈ Set.Ioc b⁻¹ a⁻¹, ENNReal.ofReal (min b t⁻¹ - a) = ENNReal.ofReal (t⁻¹ - a) := by
      intro t ht
      have htpos : 0 < t := lt_trans (inv_pos.2 hb) ht.1
      rw [min_eq_right ((inv_lt_comm₀ hb htpos).1 ht.1).le]
    rw [setLIntegral_congr_fun measurableSet_Ioc hcongr]
    have hint : IntegrableOn (fun t : ℝ => t⁻¹ - a) (Set.Ioc b⁻¹ a⁻¹) volume := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact (continuousOn_inv₀.mono fun t ht => (lt_of_lt_of_le (inv_pos.2 hb) ht.1).ne').sub
        continuousOn_const
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc b⁻¹ a⁻¹)] fun t : ℝ => t⁻¹ - a := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have htpos : 0 < t := lt_trans (inv_pos.2 hb) ht.1
      have : a ≤ t⁻¹ := (le_inv_comm₀ htpos ha).1 ht.2
      simpa using this
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume b⁻¹ a⁻¹ := by
      refine intervalIntegral.intervalIntegrable_inv (f := fun x : ℝ => x) (fun t ht => ?_) continuousOn_id
      rw [Set.uIcc_of_le hba] at ht
      exact (lt_of_lt_of_le (inv_pos.2 hb) ht.1).ne'
    have hI : ∫ x : ℝ in b⁻¹..a⁻¹, (x⁻¹ - a) = Real.log (a⁻¹ / b⁻¹) - a * (a⁻¹ - b⁻¹) := by
      rw [intervalIntegral.integral_sub hii intervalIntegrable_const, integral_inv_of_pos (inv_pos.2 hb) (inv_pos.2 ha),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← intervalIntegral.integral_of_le hba, hI]

  have h3 : ∫⁻ t in Set.Ioi a⁻¹, ENNReal.ofReal (min b t⁻¹ - a) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by
        have htpos : 0 < t := lt_trans (inv_pos.2 ha) ht
        have : t⁻¹ < a := (inv_lt_comm₀ htpos ha).2 ht
        exact ENNReal.ofReal_of_nonpos (by have := min_le_right b t⁻¹; linarith) :
        ∀ t ∈ Set.Ioi a⁻¹, ENNReal.ofReal (min b t⁻¹ - a) = 0),
      lintegral_zero]
  rw [h1, h2, h3, add_zero, ← ENNReal.ofReal_add (by
      exact mul_nonneg (by linarith) (inv_pos.2 hb).le) (by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
      rw [inv_div] at this
      have e1 : Real.log (a⁻¹ / b⁻¹) = Real.log (b / a) := by rw [inv_div_inv]
      have e2 : a * (a⁻¹ - b⁻¹) = 1 - a / b := by field_simp
      rw [e1, e2]; linarith)]
  congr 1
  have e1 : Real.log (a⁻¹ / b⁻¹) = Real.log (b / a) := by rw [inv_div_inv]
  rw [e1]
  field_simp
  ring

theorem main {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ x in fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b},
        ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      volume (normLeOne K) * ENNReal.ofReal (Real.log (b / a)) := by
  set S : Set (mixedSpace K) := fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b} with hS
  have hmeasN : Measurable (mixedEmbedding.norm : mixedSpace K → ℝ) := (mixedEmbedding.continuous_norm K).measurable
  have hf : AEMeasurable (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹) (volume.restrict S) :=
    hmeasN.inv.aemeasurable
  have hnn : 0 ≤ᵐ[volume.restrict S] fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ :=
    Filter.Eventually.of_forall fun x => inv_nonneg.2 (mixedEmbedding.norm_nonneg x)
  rw [lintegral_eq_lintegral_meas_lt _ hnn hf]
  have hpiece : ∀ t ∈ Set.Ioi (0 : ℝ),
      (volume.restrict S) {x : mixedSpace K | t < (mixedEmbedding.norm x)⁻¹} =
        ENNReal.ofReal (min b t⁻¹ - a) * volume (normLeOne K) := by
    intro t ht
    rw [Measure.restrict_apply (show MeasurableSet {x : mixedSpace K | t < (mixedEmbedding.norm x)⁻¹} from
      measurableSet_lt measurable_const hmeasN.inv)]
    have hset : {x : mixedSpace K | t < (mixedEmbedding.norm x)⁻¹} ∩ S =
        fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b} ∩ {x | mixedEmbedding.norm x < t⁻¹} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hS]
      constructor
      · rintro ⟨hlt, hx, hab'⟩
        refine ⟨⟨hx, hab'⟩, ?_⟩
        rwa [lt_inv_comm₀ ht (norm_pos_of_mem hx)] at hlt
      · rintro ⟨⟨hx, hab'⟩, hlt⟩
        refine ⟨?_, hx, hab'⟩
        rwa [lt_inv_comm₀ ht (norm_pos_of_mem hx)]
    rw [hset, volume_slab_inter_norm_lt K ha hab ht]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpiece, lintegral_mul_const _ (by
      exact (Measurable.ennreal_ofReal ((measurable_const.min measurable_inv).sub measurable_const))),
    lintegral_ofReal_min_sub ha hab, mul_comm]

end NumberField.mixedEmbedding.fundamentalCone.ConeSlab

end

theorem solution
    (K : Type) [Field K] [NumberField K] (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ x in NumberField.mixedEmbedding.fundamentalCone K ∩
        {x | NumberField.mixedEmbedding.norm x ∈ Set.Icc a b},
        ENNReal.ofReal (NumberField.mixedEmbedding.norm x)⁻¹ =
      MeasureTheory.volume (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) *
        ENNReal.ofReal (Real.log (b / a)) :=
  NumberField.mixedEmbedding.fundamentalCone.ConeSlab.main K ha hab

end S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log
end P2MW
export P2MW.S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log (solution)
