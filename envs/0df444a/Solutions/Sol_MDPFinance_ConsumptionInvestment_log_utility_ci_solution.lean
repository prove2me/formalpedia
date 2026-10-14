-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.log_utility_ci_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:03:46.689567+00:00
-- url     : https://prove2.me/submissions/8ba87567-975f-400d-9fed-e13323e04fb3

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market
import Definitions.Def_MDPFinance_ConsumptionInvestment_LogAuxiliary

open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.ConsumptionInvestment

section NA

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {R : Ω → Fin d → ℝ}

def luK (P : Measure Ω) (R : Ω → Fin d → ℝ) : Submodule ℝ (Fin d → ℝ) where
  carrier := {β | ∀ᵐ ω ∂P, ∑ k, β k * R ω k = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    filter_upwards [ha, hb] with ω h1 h2
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  zero_mem' := by
    show ∀ᵐ ω ∂P, ∑ k, (0 : Fin d → ℝ) k * R ω k = 0
    exact Filter.Eventually.of_forall fun ω => by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    filter_upwards [ha] with ω h
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h, mul_zero]

lemma lu_bounded_rep [IsProbabilityMeasure P] (hNA : NoArbitrageOnePeriodCI P R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ α : Fin d → ℝ, (∀ᵐ ω ∂P, 0 ≤ 1 + ∑ k, α k * R ω k) →
      ∃ α' : Fin d → ℝ, ‖α'‖ ≤ B ∧ ∀ᵐ ω ∂P, ∑ k, α' k * R ω k = ∑ k, α k * R ω k := by
  obtain ⟨L, hKL⟩ := Submodule.exists_isCompl (luK P R)
  have hbd : ∃ B : ℝ, 0 ≤ B ∧ ∀ l ∈ L, (∀ᵐ ω ∂P, 0 ≤ 1 + ∑ k, l k * R ω k) → ‖l‖ ≤ B := by
    by_contra hcon
    push_neg at hcon
    have hex : ∀ m : ℕ, ∃ l ∈ L, (∀ᵐ ω ∂P, 0 ≤ 1 + ∑ k, l k * R ω k) ∧ (m : ℝ) + 1 < ‖l‖ :=
      fun m => hcon ((m : ℝ) + 1) (by positivity)
    choose l hlL hlA hlnorm using hex
    have hlpos : ∀ m, 0 < ‖l m‖ := fun m => lt_trans (by positivity) (hlnorm m)
    let β : ℕ → (Fin d → ℝ) := fun m => ‖l m‖⁻¹ • l m
    have hS : IsCompact ((L : Set (Fin d → ℝ)) ∩ Metric.sphere 0 1) :=
      (isCompact_sphere 0 1).inter_left L.closed_of_finiteDimensional
    have hβS : ∀ m, β m ∈ (L : Set (Fin d → ℝ)) ∩ Metric.sphere 0 1 := by
      intro m
      refine ⟨L.smul_mem _ (hlL m), ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hlpos m).ne']
    obtain ⟨β0, hβ0, φ, hφ, hlim⟩ := hS.tendsto_subseq hβS
    have hae : ∀ᵐ ω ∂P, ∀ m, 0 ≤ 1 + ∑ k, l m k * R ω k := ae_all_iff.2 hlA
    have hpos : ∀ᵐ ω ∂P, 0 ≤ ∑ k, β0 k * R ω k := by
      filter_upwards [hae] with ω hω
      have ht : Tendsto (fun m => ∑ k, β (φ m) k * R ω k) atTop (𝓝 (∑ k, β0 k * R ω k)) :=
        tendsto_finset_sum _ fun k _ =>
          (((continuous_apply k).tendsto β0).comp hlim).mul_const _
      have hlow : ∀ m : ℕ, -(1 / ((m : ℝ) + 1)) ≤ ∑ k, β (φ m) k * R ω k := by
        intro m
        have e : ∑ k, β (φ m) k * R ω k = ‖l (φ m)‖⁻¹ * ∑ k, l (φ m) k * R ω k := by
          simp only [β, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
        rw [e]
        have h1 := hω (φ m)
        have h2 : (m : ℝ) + 1 < ‖l (φ m)‖ := by
          have : (m : ℝ) ≤ φ m := by exact_mod_cast hφ.id_le m
          linarith [hlnorm (φ m)]
        have hp := hlpos (φ m)
        have h3 : ‖l (φ m)‖⁻¹ ≤ 1 / ((m : ℝ) + 1) := by
          rw [one_div]; exact inv_anti₀ (by positivity) h2.le
        have h4 : ‖l (φ m)‖⁻¹ * (-1) ≤ ‖l (φ m)‖⁻¹ * ∑ k, l (φ m) k * R ω k :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      have ht2 : Tendsto (fun m : ℕ => -(1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
      exact le_of_tendsto_of_tendsto' ht2 ht hlow
    have hzero : P {ω | 0 < ∑ k, β0 k * R ω k} = 0 := by
      by_contra hne
      exact hNA ⟨β0, hpos, pos_iff_ne_zero.2 hne⟩
    have hK : β0 ∈ luK P R := by
      show ∀ᵐ ω ∂P, ∑ k, β0 k * R ω k = 0
      have := measure_eq_zero_iff_ae_notMem.1 hzero
      filter_upwards [this, hpos] with ω h1 h2
      simp only [Set.mem_setOf_eq, not_lt] at h1
      linarith
    have h0 : β0 = 0 := by
      have := Submodule.mem_inf.2 ⟨hK, hβ0.1⟩
      rw [hKL.inf_eq_bot, Submodule.mem_bot] at this
      exact this
    have := hβ0.2
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨B, hB0, hB⟩ := hbd
  refine ⟨B, hB0, fun α hα => ?_⟩
  have hmem : α ∈ luK P R ⊔ L := by rw [hKL.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  have hy' : ∀ᵐ ω ∂P, ∑ k, y k * R ω k = 0 := hy
  have heq : ∀ᵐ ω ∂P, ∑ k, z k * R ω k = ∑ k, α k * R ω k := by
    filter_upwards [hy'] with ω h
    rw [← hyz]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, h, zero_add]
  refine ⟨z, hB z hz ?_, heq⟩
  filter_upwards [hα, heq] with ω h1 h2
  rw [h2]; exact h1

end NA

section OneP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  {R : Ω → Fin d → ℝ}

def luA (P : Measure Ω) (R : Ω → Fin d → ℝ) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂P, 0 < 1 + ∑ k, α k * R ω k}

noncomputable def luL (R : Ω → Fin d → ℝ) (α : Fin d → ℝ) (ω : Ω) : ℝ :=
  Real.log (1 + ∑ k, α k * R ω k)

noncomputable def luv (P : Measure Ω) (R : Ω → Fin d → ℝ) : ℝ :=
  ⨆ α ∈ luA P R, ∫ ω, luL R α ω ∂P

lemma lu_mem {α : Fin d → ℝ} : α ∈ luA P R ↔ ∀ᵐ ω ∂P, 0 < 1 + ∑ k, α k * R ω k := Iff.rfl

lemma lu_zero_mem : (0 : Fin d → ℝ) ∈ luA P R :=
  lu_mem.2 (Filter.Eventually.of_forall fun ω => by simp)

lemma lu_dot_abs (α r : Fin d → ℝ) : |∑ k, α k * r k| ≤ ‖α‖ * ∑ k, |r k| := by
  calc |∑ k, α k * r k| ≤ ∑ k, |α k * r k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖α‖ * |r k| := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm α k) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

lemma lu_log_le_abs {t : ℝ} (h : 0 < 1 + t) : Real.log (1 + t) ≤ |t| := by
  have := Real.log_le_sub_one_of_pos h
  linarith [le_abs_self t]

variable (hRm : Measurable R) (hRi : Integrable (fun ω => ∑ k, |R ω k|) P)
include hRm hRi

lemma lu_comp_int (k : Fin d) : Integrable (fun ω => R ω k) P := by
  refine hRi.mono' ((measurable_pi_apply k).comp hRm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |R ω j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)

lemma lu_dot_meas (α : Fin d → ℝ) : Measurable (fun ω => ∑ k, α k * R ω k) :=
  Finset.measurable_sum _ fun k _ => measurable_const.mul ((measurable_pi_apply k).comp hRm)

lemma lu_dot_int (α : Fin d → ℝ) : Integrable (fun ω => ∑ k, α k * R ω k) P :=
  integrable_finset_sum _ fun k _ => (lu_comp_int hRm hRi k).const_mul _

lemma lu_L_meas (α : Fin d → ℝ) : Measurable (luL R α) :=
  Real.measurable_log.comp (measurable_const.add (lu_dot_meas hRm hRi α))

variable {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ α : Fin d → ℝ, (∀ᵐ ω ∂P, 0 ≤ 1 + ∑ k, α k * R ω k) →
      ∃ α' : Fin d → ℝ, ‖α'‖ ≤ B ∧ ∀ᵐ ω ∂P, ∑ k, α' k * R ω k = ∑ k, α k * R ω k)
include hB0 hB

lemma lu_int_abs_le (α : Fin d → ℝ) (hα : ∀ᵐ ω ∂P, 0 ≤ 1 + ∑ k, α k * R ω k) :
    ∫ ω, |∑ k, α k * R ω k| ∂P ≤ B * ∫ ω, ∑ k, |R ω k| ∂P := by
  obtain ⟨α', hn, heq⟩ := hB α hα
  rw [← integral_const_mul]
  calc ∫ ω, |∑ k, α k * R ω k| ∂P = ∫ ω, |∑ k, α' k * R ω k| ∂P :=
        integral_congr_ae (heq.mono fun ω h => by simp only [h])
    _ ≤ _ := by
        refine integral_mono (lu_dot_int hRm hRi α').abs (hRi.const_mul B) fun ω => ?_
        exact (lu_dot_abs α' (R ω)).trans (mul_le_mul_of_nonneg_right hn
          (Finset.sum_nonneg fun _ _ => abs_nonneg _))

lemma lu_L_le (α : Fin d → ℝ) (hα : α ∈ luA P R) :
    ∫ ω, luL R α ω ∂P ≤ B * ∫ ω, ∑ k, |R ω k| ∂P := by
  have hC : 0 ≤ B * ∫ ω, ∑ k, |R ω k| ∂P :=
    mul_nonneg hB0 (integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => abs_nonneg _)
  by_cases hI : Integrable (luL R α) P
  · refine le_trans ?_ (lu_int_abs_le hRm hRi hB0 hB α ((lu_mem.1 hα).mono fun ω h => h.le))
    refine integral_mono_ae hI (lu_dot_int hRm hRi α).abs ?_
    filter_upwards [lu_mem.1 hα] with ω h
    exact lu_log_le_abs h
  · rw [integral_undef hI]; exact hC

lemma lu_bdd : BddAbove (Set.range fun α => ⨆ (_ : α ∈ luA P R), ∫ ω, luL R α ω ∂P) := by
  refine ⟨B * ∫ ω, ∑ k, |R ω k| ∂P, ?_⟩
  rintro _ ⟨α, rfl⟩
  by_cases hA : α ∈ luA P R
  · simp only [ciSup_pos hA]; exact lu_L_le hRm hRi hB0 hB α hA
  · simp only [ciSup_neg hA, Real.sSup_empty]
    exact mul_nonneg hB0 (integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma lu_le_v (α : Fin d → ℝ) (hα : α ∈ luA P R) : ∫ ω, luL R α ω ∂P ≤ luv P R := by
  have := le_ciSup (lu_bdd hRm hRi hB0 hB) α
  simp only [ciSup_pos hα] at this
  exact this

lemma lu_v_le : luv P R ≤ B * ∫ ω, ∑ k, |R ω k| ∂P := by
  refine ciSup_le fun α => ?_
  by_cases hA : α ∈ luA P R
  · simp only [ciSup_pos hA]; exact lu_L_le hRm hRi hB0 hB α hA
  · simp only [ciSup_neg hA, Real.sSup_empty]
    exact mul_nonneg hB0 (integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma lu_v_nonneg : 0 ≤ luv P R := by
  have := lu_le_v hRm hRi hB0 hB 0 lu_zero_mem
  simpa [luL] using this

lemma lu_exists : ∃ α ∈ luA P R, Integrable (luL R α) P ∧ ∫ ω, luL R α ω ∂P = luv P R := by
  set v := luv P R with hv
  set s : Ω → ℝ := fun ω => ∑ k, |R ω k| with hs
  have hsm : Measurable s := Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp hRm).abs
  have hseq : ∀ m : ℕ, ∃ α : Fin d → ℝ, ‖α‖ ≤ B ∧ α ∈ luA P R ∧ Integrable (luL R α) P ∧
      v - 1 / ((m : ℝ) + 1) < ∫ ω, luL R α ω ∂P := by
    intro m
    have hlt : v - 1 / ((m : ℝ) + 1) < v := by
      linarith [show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity]
    obtain ⟨α, hα⟩ := exists_lt_of_lt_ciSup hlt
    have hz : v - 1 / ((m : ℝ) + 1) < ∫ ω, luL R 0 ω ∂P → ∃ α0 ∈ luA P R,
        Integrable (luL R α0) P ∧ v - 1 / ((m : ℝ) + 1) < ∫ ω, luL R α0 ω ∂P := fun h =>
      ⟨0, lu_zero_mem, (integrable_const (0:ℝ)).congr (Filter.Eventually.of_forall fun ω => by simp [luL]), h⟩
    have h0 : ∫ ω, luL R 0 ω ∂P = 0 := by simp [luL]
    have : ∃ α0 ∈ luA P R, Integrable (luL R α0) P ∧
        v - 1 / ((m : ℝ) + 1) < ∫ ω, luL R α0 ω ∂P := by
      by_cases hA : α ∈ luA P R
      · rw [ciSup_pos hA] at hα
        by_cases hI : Integrable (luL R α) P
        · exact ⟨α, hA, hI, hα⟩
        · rw [integral_undef hI] at hα
          exact hz (by rw [h0]; exact hα)
      · rw [ciSup_neg hA, Real.sSup_empty] at hα
        exact hz (by rw [h0]; exact hα)
    obtain ⟨α0, hA0, hI0, hlt0⟩ := this
    obtain ⟨α', hn, heq⟩ := hB α0 ((lu_mem.1 hA0).mono fun ω h => h.le)
    have hℓ : luL R α' =ᵐ[P] luL R α0 := heq.mono fun ω h => by simp only [luL, h]
    refine ⟨α', hn, ?_, hI0.congr hℓ.symm, by rwa [integral_congr_ae hℓ]⟩
    show ∀ᵐ ω ∂P, 0 < 1 + ∑ k, α' k * R ω k
    filter_upwards [lu_mem.1 hA0, heq] with ω h1 h2
    rw [h2]; exact h1
  choose α hαn hαA hαI hαlt using hseq
  obtain ⟨αs, hαsB, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin d → ℝ) B).tendsto_subseq
    (x := α) (fun m => mem_closedBall_zero_iff.2 (hαn m))
  have hαsn : ‖αs‖ ≤ B := mem_closedBall_zero_iff.1 hαsB
  have hae : ∀ᵐ ω ∂P, ∀ m, 0 < 1 + ∑ k, α m k * R ω k := ae_all_iff.2 fun m => lu_mem.1 (hαA m)
  have hconv : ∀ ω, Tendsto (fun m => 1 + ∑ k, α (φ m) k * R ω k) atTop
      (𝓝 (1 + ∑ k, αs k * R ω k)) := fun ω =>
    tendsto_const_nhds.add (tendsto_finset_sum _ fun k _ =>
      (((continuous_apply k).tendsto αs).comp hlim).mul_const _)
  -- bound log ≤ B s
  have hLB : ∀ (β : Fin d → ℝ), ‖β‖ ≤ B → ∀ ω, 0 < 1 + ∑ k, β k * R ω k →
      luL R β ω ≤ B * s ω := by
    intro β hβ ω h
    exact (lu_log_le_abs h).trans ((lu_dot_abs β (R ω)).trans
      (mul_le_mul_of_nonneg_right hβ (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
  set c : ℝ := B * ∫ ω, s ω ∂P - v with hc
  have hc0 : 0 ≤ c := by
    have := lu_v_le hRm hRi hB0 hB; rw [hc]; linarith
  let h : ℕ → Ω → ENNReal := fun m ω => ENNReal.ofReal (B * s ω - luL R (α (φ m)) ω)
  let H : Ω → ENNReal := fun ω => if 0 < 1 + ∑ k, αs k * R ω k then
    ENNReal.ofReal (B * s ω - luL R αs ω) else ⊤
  have hhm : ∀ m, Measurable (h m) := fun m =>
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hsm).sub (lu_L_meas hRm hRi _))
  have hHm : Measurable H :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_const.add (lu_dot_meas hRm hRi αs)))
      (ENNReal.measurable_ofReal.comp ((measurable_const.mul hsm).sub (lu_L_meas hRm hRi _)))
      measurable_const
  have hpt : ∀ᵐ ω ∂P, Tendsto (fun m => h m ω) atTop (𝓝 (H ω)) := by
    filter_upwards [hae] with ω hω
    by_cases hp : 0 < 1 + ∑ k, αs k * R ω k
    · simp only [H, if_pos hp, h, luL]
      refine (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub ?_)
      exact ((Real.continuousAt_log hp.ne').tendsto).comp (hconv ω)
    · simp only [H, if_neg hp, h, luL]
      have h0 : 1 + ∑ k, αs k * R ω k = 0 := by
        have := ge_of_tendsto' (hconv ω) (fun m => (hω (φ m)).le)
        linarith
      have h1 : Tendsto (fun m => 1 + ∑ k, α (φ m) k * R ω k) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨h0 ▸ hconv ω, Filter.Eventually.of_forall fun m => hω (φ m)⟩
      have h2 := Real.tendsto_log_nhdsGT_zero.comp h1
      have h3 : Tendsto (fun m => B * s ω - Real.log (1 + ∑ k, α (φ m) k * R ω k)) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp h2)
      exact ENNReal.tendsto_ofReal_atTop.comp h3
  have hint_m : ∀ m, ∫⁻ ω, h m ω ∂P ≤ ENNReal.ofReal (c + 1 / ((m : ℝ) + 1)) := by
    intro m
    have hnn : 0 ≤ᵐ[P] fun ω => B * s ω - luL R (α (φ m)) ω := by
      filter_upwards [lu_mem.1 (hαA (φ m))] with ω hω
      have := hLB _ (hαn (φ m)) ω hω
      simp only [Pi.zero_apply]; linarith
    have hI : Integrable (fun ω => B * s ω - luL R (α (φ m)) ω) P :=
      (hRi.const_mul B).sub (hαI (φ m))
    rw [← ofReal_integral_eq_lintegral_ofReal hI hnn]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub (hRi.const_mul B) (hαI (φ m)), integral_const_mul]
    have h1 := hαlt (φ m)
    have h2 : 1 / ((φ m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ φ m := by exact_mod_cast hφ.id_le m
      linarith
    rw [hc]; linarith
  have hfat := lintegral_liminf_le (μ := P) (u := atTop) hhm
  have hHint : ∫⁻ ω, H ω ∂P ≤ ENNReal.ofReal c := by
    calc ∫⁻ ω, H ω ∂P = ∫⁻ ω, liminf (fun m => h m ω) atTop ∂P :=
          lintegral_congr_ae (hpt.mono fun ω hω => hω.liminf_eq.symm)
      _ ≤ liminf (fun m => ∫⁻ ω, h m ω ∂P) atTop := hfat
      _ ≤ liminf (fun m : ℕ => ENNReal.ofReal (c + 1 / ((m : ℝ) + 1))) atTop :=
          liminf_le_liminf (Filter.Eventually.of_forall hint_m)
      _ = ENNReal.ofReal c := by
          refine Tendsto.liminf_eq ?_
          refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
          simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hHlt : ∀ᵐ ω ∂P, H ω < ⊤ := ae_lt_top hHm (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hHint)
  have hαsA : αs ∈ luA P R := by
    show ∀ᵐ ω ∂P, 0 < 1 + ∑ k, αs k * R ω k
    filter_upwards [hHlt] with ω hω
    by_contra hneg
    simp only [H, if_neg hneg] at hω
    exact lt_irrefl _ hω
  have hHeq : H =ᵐ[P] fun ω => ENNReal.ofReal (B * s ω - luL R αs ω) := by
    filter_upwards [lu_mem.1 hαsA] with ω hω
    simp only [H, if_pos hω]
  have hgnn : 0 ≤ᵐ[P] fun ω => B * s ω - luL R αs ω := by
    filter_upwards [lu_mem.1 hαsA] with ω hω
    have := hLB _ hαsn ω hω
    simp only [Pi.zero_apply]; linarith
  have hgm : Measurable fun ω => B * s ω - luL R αs ω :=
    (measurable_const.mul hsm).sub (lu_L_meas hRm hRi _)
  have hglin : ∫⁻ ω, ENNReal.ofReal (B * s ω - luL R αs ω) ∂P ≤ ENNReal.ofReal c := by
    rw [← lintegral_congr_ae hHeq]; exact hHint
  have hgI : Integrable (fun ω => B * s ω - luL R αs ω) P :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable hgnn).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hglin)
  have hLI : Integrable (luL R αs) P := by
    have := (hRi.const_mul B).sub hgI
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]; ring
  have hgval : ∫ ω, (B * s ω - luL R αs ω) ∂P ≤ c := by
    rw [← ENNReal.ofReal_le_ofReal_iff hc0, ofReal_integral_eq_lintegral_ofReal hgI hgnn]
    exact hglin
  rw [integral_sub (hRi.const_mul B) hLI, integral_const_mul] at hgval
  refine ⟨αs, hαsA, hLI, le_antisymm (lu_le_v hRm hRi hB0 hB αs hαsA) ?_⟩
  rw [hc] at hgval; linarith

end OneP

section Det

noncomputable def luκ (m : ℝ) : ℝ := Real.log (1 / (m + 1)) + m * Real.log (m / (m + 1))

lemma lu_det {m y c : ℝ} (hm : 0 < m) (hy : 0 < y) (hc : 0 < c) (hcy : c < y) :
    Real.log c + m * Real.log (y - c) - (m + 1) * Real.log y - luκ m ≤ 0 := by
  have hyc : 0 < y - c := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < c * (m + 1) / y by positivity)
  rw [Real.log_div (by positivity) hy.ne', Real.log_mul hc.ne' hm1.ne'] at h1
  have h2 := Real.log_le_sub_one_of_pos (show 0 < (y - c) * (m + 1) / (m * y) by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hyc.ne' hm1.ne',
    Real.log_mul hm.ne' hy.ne'] at h2
  have hk : luκ m = -Real.log (m + 1) + m * (Real.log m - Real.log (m + 1)) := by
    unfold luκ
    rw [one_div, Real.log_inv, Real.log_div hm.ne' hm1.ne']
  have hid : c * (m + 1) / y - 1 + m * ((y - c) * (m + 1) / (m * y) - 1) = 0 := by
    field_simp; ring
  have h2' := mul_le_mul_of_nonneg_left h2 hm.le
  rw [hk]
  nlinarith

lemma lu_det_eq {m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    Real.log (y / (m + 1)) + m * Real.log (y - y / (m + 1)) - (m + 1) * Real.log y - luκ m = 0 := by
  have hm1 : 0 < m + 1 := by linarith
  have e : y - y / (m + 1) = y * m / (m + 1) := by field_simp; ring
  rw [e, Real.log_div hy.ne' hm1.ne', Real.log_div (by positivity) hm1.ne',
    Real.log_mul hy.ne' hm.ne']
  unfold luκ
  rw [one_div, Real.log_inv, Real.log_div hm.ne' hm1.ne']
  ring

end Det

section Glue

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def ciT (g : ℝ → ℝ × (Fin d → ℝ)) (ρ y : ℝ) (z : Fin d → ℝ) : ℝ :=
  ρ * (y - (g y).1 + ∑ j, (g y).2 j * z j)

lemma ciT_meas {g : ℝ → ℝ × (Fin d → ℝ)} (hg : Measurable g) (ρ : ℝ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) => ciT g ρ p.1 p.2) := by
  unfold ciT
  have h1 : Measurable (fun p : ℝ × (Fin d → ℝ) => (g p.1).1) := measurable_fst.comp (hg.comp measurable_fst)
  have h2 : ∀ j, Measurable (fun p : ℝ × (Fin d → ℝ) => (g p.1).2 j) := fun j =>
    (measurable_pi_apply j).comp (measurable_snd.comp (hg.comp measurable_fst))
  have h3 : ∀ j, Measurable (fun p : ℝ × (Fin d → ℝ) => p.2 j) := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  refine measurable_const.mul ((measurable_fst.sub h1).add ?_)
  exact Finset.measurable_sum _ (fun j _ => (h2 j).mul (h3 j))

lemma ci_erealIntegral_of_integrable {P : Measure Ω} {f : Ω → ℝ} (hf : Integrable f P) :
    erealIntegral P (fun ω => (f ω : EReal)) = ((∫ ω, f ω ∂P : ℝ) : EReal) := by
  unfold erealIntegral
  have e1 : ∀ ω, ((f ω : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (f ω) := by
    intro ω
    rcases le_total 0 (f ω) with h | h
    · rw [sup_eq_left.2 (EReal.coe_nonneg.2 h), EReal.real_coe_toENNReal]
    · rw [sup_eq_right.2 (EReal.coe_nonpos.2 h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  have e2 : ∀ ω, ((-(f ω : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-f ω) := by
    intro ω
    rw [← EReal.coe_neg]
    rcases le_total 0 (-f ω) with h | h
    · rw [sup_eq_left.2 (EReal.coe_nonneg.2 h), EReal.real_coe_toENNReal]
    · rw [sup_eq_right.2 (EReal.coe_nonpos.2 h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  simp_rw [e1, e2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have h1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono (fun ω => by
      rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _))) hf.2).ne
  have h2 : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂P ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono (fun ω => by
      rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _))) hf.2).ne
  rw [← EReal.coe_ennreal_toReal h1, ← EReal.coe_ennreal_toReal h2]
  rfl

lemma ci_erealIntegral_congr {P : Measure Ω} {f g : Ω → ℝ} (h : f =ᵐ[P] g) :
    erealIntegral P (fun ω => (f ω : EReal)) = erealIntegral P (fun ω => (g ω : EReal)) := by
  unfold erealIntegral
  have e : ∀ (F : EReal → ENNReal), ∫⁻ ω, F (f ω) ∂P = ∫⁻ ω, F (g ω) ∂P := fun F =>
    lintegral_congr_ae (h.mono fun ω hω => by simp only [hω])
  have a1 := e (fun t => (t ⊔ 0).toENNReal)
  have a2 := e (fun t => ((-t) ⊔ 0).toENNReal)
  rw [a1, a2]

lemma lu_erealIntegral_bot {P : Measure Ω} {f : Ω → ℝ}
    (h : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂P = ⊤) :
    erealIntegral P (fun ω => (f ω : EReal)) = ⊥ := by
  unfold erealIntegral
  have e2 : ∀ ω, ((-(f ω : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-f ω) := by
    intro ω
    rw [← EReal.coe_neg]
    rcases le_total 0 (-f ω) with h | h
    · rw [sup_eq_left.2 (EReal.coe_nonneg.2 h), EReal.real_coe_toENNReal]
    · rw [sup_eq_right.2 (EReal.coe_nonpos.2 h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  simp_rw [e2, h]
  simp

variable (M : ConsumptionInvestmentMarket Ω d)

lemma ci_stateAcc_succ (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) : ∀ k n x ω,
    M.stateAcc π (k + 1) n x ω =
      (ciT (π (n + k)) (1 + M.i (n + k + 1)) (M.stateAcc π k n x ω).1 (M.R (n + k + 1) ω),
        (M.stateAcc π k n x ω).2 + M.Uc (π (n + k) (M.stateAcc π k n x ω).1).1) := by
  intro k
  induction k with
  | zero =>
    intro n x ω
    simp [ConsumptionInvestmentMarket.stateAcc, ciT]
  | succ k ih =>
    intro n x ω
    rw [ConsumptionInvestmentMarket.stateAcc, ih (n + 1)]
    conv_rhs => rw [ConsumptionInvestmentMarket.stateAcc]
    simp only
    have e1 : n + 1 + k = n + (k + 1) := by omega
    rw [e1]
    congr 1
    ring

def ciF (k : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ {j : Fin M.N | j.val < k}, MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance

lemma ciF_mono {k k' : ℕ} (h : k ≤ k') : ciF M k ≤ ciF M k' :=
  iSup₂_le fun j hj => le_iSup₂_of_le (f := fun (j : Fin M.N) (_ : j ∈ {j : Fin M.N | j.val < k'}) =>
    MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance) j
    (show j.val < k' from lt_of_lt_of_le hj h) le_rfl

lemma ciF_le (k : ℕ) : ciF M k ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun j _ => (M.hR_meas (j.val + 1) (by omega) (by omega)).comap_le

lemma ciR_meas_F (k : ℕ) (hk : k < M.N) : Measurable[ciF M (k + 1)] (M.R (k + 1)) := by
  have : MeasurableSpace.comap (M.R (k + 1)) inferInstance ≤ ciF M (k + 1) :=
    le_iSup₂_of_le (f := fun (j : Fin M.N) (_ : j ∈ {j : Fin M.N | j.val < k + 1}) =>
      MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance) ⟨k, hk⟩
      (show k < k + 1 by omega) le_rfl
  exact Measurable.of_comap_le this

def luX (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (x : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  (M.stateAcc π j n x ω).1

lemma luX_succ (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (x : ℝ) (j : ℕ) (ω : Ω) :
    luX M π n x (j + 1) ω =
      ciT (π (n + j)) (1 + M.i (n + j + 1)) (luX M π n x j ω) (M.R (n + j + 1) ω) := by
  unfold luX
  rw [ci_stateAcc_succ M π j n x ω]

lemma luAcc (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (x : ℝ) : ∀ (j : ℕ) (ω : Ω),
    (M.stateAcc π j n x ω).2 = ∑ i ∈ Finset.range j, M.Uc (π (n + i) (luX M π n x i ω)).1 := by
  intro j
  induction j with
  | zero => intro ω; rfl
  | succ j ih =>
    intro ω
    rw [ci_stateAcc_succ M π j n x ω, Finset.sum_range_succ]
    rw [ih ω]; rfl

lemma luX_meas (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (x : ℝ) :
    ∀ j, n + j ≤ M.N → Measurable[ciF M (n + j)] (luX M π n x j) := by
  intro j
  induction j with
  | zero => intro _; exact measurable_const
  | succ j ih =>
    intro hj
    have h1 : Measurable[ciF M (n + j + 1)] (luX M π n x j) :=
      (ih (by omega)).mono (ciF_mono M (by omega)) le_rfl
    have h2 := ciR_meas_F M (n + j) (by omega)
    have hg := (hπ (n + j) (by omega) (by omega)).2
    have : luX M π n x (j + 1) = (fun p : ℝ × (Fin d → ℝ) =>
        ciT (π (n + j)) (1 + M.i (n + j + 1)) p.1 p.2) ∘
        (fun ω => (luX M π n x j ω, M.R (n + j + 1) ω)) := by
      funext ω; exact luX_succ M π n x j ω
    rw [this, show n + (j + 1) = n + j + 1 by omega]
    exact (ciT_meas hg _).comp (h1.prodMk h2)

lemma luX_indep (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (x : ℝ)
    (j : ℕ) (hj : n + j < M.N) : IndepFun (luX M π n x j) (M.R (n + j + 1)) M.measIP := by
  rw [IndepFun_iff_Indep]
  have hle : ∀ j : Fin M.N, MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) :=
    fun j => (M.hR_meas (j.val + 1) (by omega) (by omega)).comap_le
  have hI := indep_iSup_of_disjoint hle M.hR_indep.iIndep
    (S := {j' : Fin M.N | j'.val < n + j}) (T := {j' : Fin M.N | j'.val = n + j}) (by
      rw [Set.disjoint_left]; intro j' h1 h2; simp at h1 h2; omega)
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
  · exact (luX_meas M π n hπ x j hj.le).comap_le
  · exact le_iSup₂_of_le (f := fun (j' : Fin M.N) (_ : j' ∈ {j' : Fin M.N | j'.val = n + j}) =>
      MeasurableSpace.comap (fun ω => M.R (j'.val + 1) ω) inferInstance) ⟨n + j, hj⟩ rfl le_rfl

end Glue

section Ind

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  {Y : Ω → ℝ} {Rr : Ω → Fin d → ℝ}

lemma lu_ind_ae (hY : Measurable Y) (hR : Measurable Rr) (hind : IndepFun Y Rr P)
    (S : Set (ℝ × (Fin d → ℝ))) (hS : MeasurableSet S) (hY0 : ∀ᵐ ω ∂P, 0 < Y ω)
    (hgood : ∀ y, 0 < y → ∀ᵐ ω ∂P, (y, Rr ω) ∈ S) : ∀ᵐ ω ∂P, (Y ω, Rr ω) ∈ S := by
  have hpair : Measurable (fun ω => (Y ω, Rr ω)) := hY.prodMk hR
  have hprod : P.map (fun ω => (Y ω, Rr ω)) = (P.map Y).prod (P.map Rr) :=
    (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable).1 hind
  haveI : IsProbabilityMeasure (P.map Rr) := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hYae : ∀ᵐ y ∂(P.map Y), 0 < y := (ae_map_iff hY.aemeasurable measurableSet_Ioi).2 hY0
  rw [ae_iff]
  have : {ω | ¬ (Y ω, Rr ω) ∈ S} = (fun ω => (Y ω, Rr ω)) ⁻¹' Sᶜ := by ext ω; simp
  rw [this, ← Measure.map_apply hpair hS.compl, hprod, Measure.prod_apply hS.compl]
  rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
  filter_upwards [hYae] with y hy
  rw [Measure.map_apply hR (measurable_prodMk_left hS.compl)]
  have := hgood y hy
  rw [ae_iff] at this
  exact this

lemma lu_ind_int (hY : Measurable Y) (hR : Measurable Rr) (hind : IndepFun Y Rr P)
    (g : ℝ × (Fin d → ℝ) → ℝ) (hg : Measurable g) (hY0 : ∀ᵐ ω ∂P, 0 < Y ω) (K V : ℝ)
    (hK : ∀ y, 0 < y → ∫⁻ ω, ENNReal.ofReal (g (y, Rr ω)) ∂P ≤ ENNReal.ofReal K)
    (hV : ∀ y, 0 < y → Integrable (fun ω => g (y, Rr ω)) P → ∫ ω, g (y, Rr ω) ∂P ≤ V) :
    ∫⁻ ω, ENNReal.ofReal (g (Y ω, Rr ω)) ∂P ≤ ENNReal.ofReal K ∧
      (Integrable (fun ω => g (Y ω, Rr ω)) P → ∫ ω, g (Y ω, Rr ω) ∂P ≤ V) := by
  have hpair : Measurable (fun ω => (Y ω, Rr ω)) := hY.prodMk hR
  have hprod : P.map (fun ω => (Y ω, Rr ω)) = (P.map Y).prod (P.map Rr) :=
    (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable).1 hind
  haveI : IsProbabilityMeasure (P.map Rr) := Measure.isProbabilityMeasure_map hR.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hYae : ∀ᵐ y ∂(P.map Y), 0 < y := (ae_map_iff hY.aemeasurable measurableSet_Ioi).2 hY0
  have hgy : ∀ y, Measurable fun r : Fin d → ℝ => g (y, r) :=
    fun y => hg.comp (measurable_const.prodMk measurable_id)
  constructor
  · have hF : Measurable fun p : ℝ × (Fin d → ℝ) => ENNReal.ofReal (g p) :=
      ENNReal.measurable_ofReal.comp hg
    have e : ∫⁻ ω, ENNReal.ofReal (g (Y ω, Rr ω)) ∂P =
        ∫⁻ y, ∫⁻ r, ENNReal.ofReal (g (y, r)) ∂(P.map Rr) ∂(P.map Y) := by
      rw [← lintegral_prod _ hF.aemeasurable, ← hprod, lintegral_map hF hpair]
    rw [e]
    calc ∫⁻ y, ∫⁻ r, ENNReal.ofReal (g (y, r)) ∂(P.map Rr) ∂(P.map Y)
        ≤ ∫⁻ y, ENNReal.ofReal K ∂(P.map Y) := by
          apply lintegral_mono_ae
          filter_upwards [hYae] with y hy
          rw [lintegral_map (f := fun r => ENNReal.ofReal (g (y, r))) (ENNReal.measurable_ofReal.comp (hgy y)) hR]
          exact hK y hy
      _ = ENNReal.ofReal K := by simp
  · intro hI
    have hint : Integrable g ((P.map Y).prod (P.map Rr)) := by
      rw [← hprod, integrable_map_measure hg.aestronglyMeasurable hpair.aemeasurable]
      exact hI
    have eL : ∫ ω, g (Y ω, Rr ω) ∂P = ∫ y, ∫ r, g (y, r) ∂(P.map Rr) ∂(P.map Y) := by
      rw [← integral_prod _ hint, ← hprod,
        integral_map hpair.aemeasurable hg.aestronglyMeasurable]
    rw [eL]
    calc ∫ y, ∫ r, g (y, r) ∂(P.map Rr) ∂(P.map Y) ≤ ∫ y, V ∂(P.map Y) := by
          apply integral_mono_ae hint.integral_prod_left (integrable_const _)
          filter_upwards [hYae, hint.prod_right_ae] with y hy hiy
          rw [integral_map hR.aemeasurable (hgy y).aestronglyMeasurable]
          refine hV y hy ?_
          rw [integrable_map_measure (hgy y).aestronglyMeasurable hR.aemeasurable] at hiy
          exact hiy
      _ = V := by simp

end Ind

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : ConsumptionInvestmentMarket Ω d)

noncomputable def luDj : ℕ → ℝ
  | 0 => 0
  | j + 1 => luDj j + luκ ((j : ℝ) + 1) +
      ((j : ℝ) + 1) * (Real.log (1 + M.i (M.N - j)) + M.vLog (M.N - j - 1))

noncomputable def luD (n : ℕ) : ℝ := luDj M (M.N - n)

noncomputable def luW (n : ℕ) (y : ℝ) : ℝ := ((M.N : ℝ) - n + 1) * Real.log y + luD M n

lemma luD_succ (n : ℕ) (hn : n < M.N) :
    luD M n = luD M (n + 1) + luκ ((M.N : ℝ) - n) +
      ((M.N : ℝ) - n) * (Real.log (1 + M.i (n + 1)) + M.vLog n) := by
  unfold luD
  obtain ⟨j, hj⟩ : ∃ j, M.N - n = j + 1 := ⟨M.N - n - 1, by omega⟩
  rw [hj, luDj, show M.N - (n + 1) = j by omega, show M.N - j = n + 1 by omega,
    show n + 1 - 1 = n by omega]
  have : ((j : ℝ) + 1) = (M.N : ℝ) - n := by
    have : (M.N : ℝ) = n + j + 1 := by exact_mod_cast (show M.N = n + j + 1 by omega)
    linarith
  rw [this]

lemma luW_N (y : ℝ) : luW M M.N y = Real.log y := by
  simp [luW, luD, luDj]

noncomputable def luα (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (k : ℕ) (y : ℝ) : Fin d → ℝ :=
  (y - (π k y).1)⁻¹ • (π k y).2

noncomputable def luGap (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (k : ℕ) (y : ℝ) : ℝ :=
  Real.log (π k y).1 + ((M.N : ℝ) - k) * Real.log (y - (π k y).1) -
    ((M.N : ℝ) - k + 1) * Real.log y - luκ ((M.N : ℝ) - k)

noncomputable def luG (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (x : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  Real.log (1 + ∑ l, luα π (n + i) (luX M π n x i ω) l * M.R (n + i + 1) ω l)

lemma lu_log_next {ρ y c : ℝ} {a r : Fin d → ℝ} (hρ : 0 < ρ) (hyc : 0 < y - c)
    (h : 0 < ρ * (y - c + ∑ l, a l * r l)) :
    0 < 1 + ∑ l, ((y - c)⁻¹ • a) l * r l ∧
    Real.log (ρ * (y - c + ∑ l, a l * r l)) =
      Real.log ρ + Real.log (y - c) + Real.log (1 + ∑ l, ((y - c)⁻¹ • a) l * r l) := by
  have hs : ∑ l, ((y - c)⁻¹ • a) l * r l = (y - c)⁻¹ * ∑ l, a l * r l := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have h1 : 0 < y - c + ∑ l, a l * r l := pos_of_mul_pos_right h hρ.le
  have e : y - c + ∑ l, a l * r l = (y - c) * (1 + (y - c)⁻¹ * ∑ l, a l * r l) := by
    field_simp
  have h2 : 0 < 1 + (y - c)⁻¹ * ∑ l, a l * r l := by
    rw [e] at h1; exact pos_of_mul_pos_right h1 hyc.le
  rw [hs]
  refine ⟨h2, ?_⟩
  rw [e, Real.log_mul hρ.ne' (mul_pos hyc h2).ne', Real.log_mul hyc.ne' h2.ne']
  ring

lemma lu_W_step (k : ℕ) (hk : k < M.N) (y c : ℝ) (a r : Fin d → ℝ) (hy : 0 < y) (hc : 0 < c)
    (hcy : c < y) (hnext : 0 < (1 + M.i (k + 1)) * (y - c + ∑ l, a l * r l)) :
    0 < 1 + ∑ l, ((y - c)⁻¹ • a) l * r l ∧
    Real.log c + luW M (k + 1) ((1 + M.i (k + 1)) * (y - c + ∑ l, a l * r l)) =
      luW M k y + (Real.log c + ((M.N : ℝ) - k) * Real.log (y - c) -
        ((M.N : ℝ) - k + 1) * Real.log y - luκ ((M.N : ℝ) - k)) +
      ((M.N : ℝ) - k) * (Real.log (1 + ∑ l, ((y - c)⁻¹ • a) l * r l) - M.vLog k) := by
  have hρ : 0 < 1 + M.i (k + 1) := M.hi_pos _ (by omega) (by omega)
  obtain ⟨hpos, hlog⟩ := lu_log_next hρ (sub_pos.2 hcy) hnext
  refine ⟨hpos, ?_⟩
  unfold luW
  rw [hlog, luD_succ M k hk]
  push_cast
  ring

variable (hdomU : M.domU = Set.Ioi (0 : ℝ)) (hUc : ∀ x > (0 : ℝ), M.Uc x = Real.log x)
  (hUp : ∀ x > (0 : ℝ), M.Up x = Real.log x) (hFM2 : M.FM2)

include hdomU in
lemma lu_adm (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (k : ℕ)
    (hnk : n ≤ k) (hk : k < M.N) (y : ℝ) (hy : 0 < y) :
    0 < (π k y).1 ∧ (π k y).1 < y ∧
      ∀ᵐ ω ∂M.measIP, 0 < ciT (π k) (1 + M.i (k + 1)) y (M.R (k + 1) ω) := by
  haveI := M.isProb
  obtain ⟨h0, h1, h2, h3⟩ := (hπ k hnk hk).1 y (by rw [hdomU]; exact hy)
  rw [hdomU] at h2
  have h3' : ∀ᵐ ω ∂M.measIP, 0 < ciT (π k) (1 + M.i (k + 1)) y (M.R (k + 1) ω) := by
    filter_upwards [h3] with ω h; rw [hdomU] at h; exact h
  refine ⟨h2, lt_of_le_of_ne h1 ?_, h3'⟩
  intro heq
  have hρ : 0 < 1 + M.i (k + 1) := M.hi_pos _ (by omega) (by omega)
  have hpos : ∀ᵐ ω ∂M.measIP, 0 < ∑ j, (π k y).2 j * M.R (k + 1) ω j := by
    filter_upwards [h3'] with ω h
    unfold ciT at h
    rw [heq, sub_self, zero_add] at h
    exact pos_of_mul_pos_right h hρ.le
  apply M.hNA (k + 1) (by omega) (by omega)
  refine ⟨(π k y).2, hpos.mono fun ω h => h.le, ?_⟩
  rw [gt_iff_lt, pos_iff_ne_zero]
  intro h0'
  have := measure_eq_zero_iff_ae_notMem.1 h0'
  have hF : ∀ᵐ ω ∂M.measIP, False := by
    filter_upwards [this, hpos] with ω a b; exact a b
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hF
  exact IsProbabilityMeasure.ne_zero M.measIP hF

include hdomU hUc in
lemma lu_path (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (x : ℝ) :
    ∀ j, n + j ≤ M.N → ∀ ω, (∀ i ≤ j, 0 < luX M π n x i ω) →
      (M.stateAcc π j n x ω).2 + luW M (n + j) (luX M π n x j ω) =
        luW M n x + ∑ i ∈ Finset.range j, (luGap M π (n + i) (luX M π n x i ω) +
          ((M.N : ℝ) - ((n + i : ℕ) : ℝ)) * (luG M π n x i ω - M.vLog (n + i))) := by
  intro j
  induction j with
  | zero =>
    intro _ ω _
    simp [ConsumptionInvestmentMarket.stateAcc, luX]
  | succ j ih =>
    intro hj ω hpos
    have ih' := ih (by omega) ω (fun i hi => hpos i (by omega))
    have hy := hpos j (by omega)
    obtain ⟨hc, hcy, -⟩ := lu_adm M hdomU π n hπ (n + j) (by omega) (by omega) _ hy
    have hnext := hpos (j + 1) le_rfl
    rw [luX_succ] at hnext
    unfold ciT at hnext
    obtain ⟨-, hstep⟩ := lu_W_step M (n + j) (by omega) _ _ _ (M.R (n + j + 1) ω) hy hc hcy hnext
    have e1 : (M.stateAcc π (j + 1) n x ω).2 = (M.stateAcc π j n x ω).2 +
        Real.log (π (n + j) (luX M π n x j ω)).1 := by
      rw [ci_stateAcc_succ M π j n x ω]
      simp only
      rw [show luX M π n x j ω = (M.stateAcc π j n x ω).1 from rfl] at hc ⊢
      rw [hUc _ hc]
    have e2 : luX M π n x (j + 1) ω = (1 + M.i (n + j + 1)) * (luX M π n x j ω -
        (π (n + j) (luX M π n x j ω)).1 + ∑ l, (π (n + j) (luX M π n x j ω)).2 l *
          M.R (n + j + 1) ω l) := by
      rw [luX_succ]; rfl
    rw [Finset.sum_range_succ, e1, show n + (j + 1) = n + j + 1 by omega, e2]
    have e3 : luGap M π (n + j) (luX M π n x j ω) + ((M.N : ℝ) - ((n + j : ℕ) : ℝ)) *
        (luG M π n x j ω - M.vLog (n + j)) =
        (Real.log (π (n + j) (luX M π n x j ω)).1 + ((M.N : ℝ) - ((n + j : ℕ) : ℝ)) *
          Real.log (luX M π n x j ω - (π (n + j) (luX M π n x j ω)).1) -
          ((M.N : ℝ) - ((n + j : ℕ) : ℝ) + 1) * Real.log (luX M π n x j ω) -
          luκ ((M.N : ℝ) - ((n + j : ℕ) : ℝ))) +
        ((M.N : ℝ) - ((n + j : ℕ) : ℝ)) * (Real.log (1 + ∑ l, ((luX M π n x j ω -
          (π (n + j) (luX M π n x j ω)).1)⁻¹ • (π (n + j) (luX M π n x j ω)).2) l *
            M.R (n + j + 1) ω l) - M.vLog (n + j)) := rfl
    linarith [ih', hstep, e3]

include hdomU in
lemma lu_pos (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (x : ℝ)
    (hx : 0 < x) : ∀ j, n + j ≤ M.N → ∀ᵐ ω ∂M.measIP, 0 < luX M π n x j ω := by
  haveI := M.isProb
  intro j
  induction j with
  | zero => intro _; exact Filter.Eventually.of_forall fun ω => hx
  | succ j ih =>
    intro hj
    have hY : Measurable (luX M π n x j) :=
      (luX_meas M π n hπ x j (by omega)).mono (ciF_le M _) le_rfl
    have hR : Measurable (M.R (n + j + 1)) := M.hR_meas _ (by omega) (by omega)
    have hind := luX_indep M π n hπ x j (by omega)
    have hg := (hπ (n + j) (by omega) (by omega)).2
    have hS : MeasurableSet {p : ℝ × (Fin d → ℝ) |
        0 < ciT (π (n + j)) (1 + M.i (n + j + 1)) p.1 p.2} :=
      measurableSet_lt measurable_const (ciT_meas hg _)
    have := lu_ind_ae hY hR hind _ hS (ih (by omega)) (fun y hy =>
      (lu_adm M hdomU π n hπ (n + j) (by omega) (by omega) y hy).2.2)
    filter_upwards [this] with ω h
    rw [luX_succ]; exact h

include hFM2 in
lemma lu_period (k : ℕ) (hk : k < M.N) : ∃ K : ℝ,
    (∀ α ∈ M.AfracLog k, ∫⁻ ω, ENNReal.ofReal (Real.log (1 + ∑ l, α l * M.R (k + 1) ω l))
      ∂M.measIP ≤ ENNReal.ofReal K) ∧
    (∀ α ∈ M.AfracLog k, Integrable (fun ω => Real.log (1 + ∑ l, α l * M.R (k + 1) ω l))
      M.measIP → ∫ ω, Real.log (1 + ∑ l, α l * M.R (k + 1) ω l) ∂M.measIP ≤ M.vLog k) ∧
    0 ≤ M.vLog k ∧
    ∃ αs ∈ M.AfracLog k, Integrable (fun ω => Real.log (1 + ∑ l, αs l * M.R (k + 1) ω l))
      M.measIP ∧ ∫ ω, Real.log (1 + ∑ l, αs l * M.R (k + 1) ω l) ∂M.measIP = M.vLog k := by
  haveI := M.isProb
  have hRm : Measurable (M.R (k + 1)) := M.hR_meas _ (by omega) (by omega)
  have hRi := hFM2 (k + 1) (by omega) (by omega)
  obtain ⟨B, hB0, hB⟩ := lu_bounded_rep (M.hNA (k + 1) (by omega) (by omega))
  refine ⟨B * ∫ ω, ∑ l, |M.R (k + 1) ω l| ∂M.measIP, fun α hα => ?_, fun α hα hI => ?_,
    lu_v_nonneg hRm hRi hB0 hB, lu_exists hRm hRi hB0 hB⟩
  · calc ∫⁻ ω, ENNReal.ofReal (Real.log (1 + ∑ l, α l * M.R (k + 1) ω l)) ∂M.measIP
        ≤ ∫⁻ ω, ENNReal.ofReal |∑ l, α l * M.R (k + 1) ω l| ∂M.measIP := by
          apply lintegral_mono_ae
          filter_upwards [lu_mem.1 hα] with ω h
          exact ENNReal.ofReal_le_ofReal (lu_log_le_abs h)
      _ = ENNReal.ofReal (∫ ω, |∑ l, α l * M.R (k + 1) ω l| ∂M.measIP) :=
          (ofReal_integral_eq_lintegral_ofReal (lu_dot_int hRm hRi α).abs
            (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (lu_int_abs_le hRm hRi hB0 hB α ((lu_mem.1 hα).mono fun ω h => h.le))
  · exact lu_le_v hRm hRi hB0 hB α hα

lemma luα_meas (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (k : ℕ) (hg : Measurable (π k)) :
    Measurable (luα π k) :=
  ((measurable_id.sub (measurable_fst.comp hg)).inv).smul (measurable_snd.comp hg)

lemma lu_gfun_meas (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (k : ℕ) (hg : Measurable (π k)) :
    Measurable (fun p : ℝ × (Fin d → ℝ) => Real.log (1 + ∑ l, luα π k p.1 l * p.2 l)) :=
  Real.measurable_log.comp (measurable_const.add (Finset.measurable_sum _ fun l _ =>
    ((measurable_pi_apply l).comp ((luα_meas π k hg).comp measurable_fst)).mul
      ((measurable_pi_apply l).comp measurable_snd)))

lemma luGap_meas (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (k : ℕ) (hg : Measurable (π k)) :
    Measurable (luGap M π k) := by
  unfold luGap
  have h1 : Measurable fun y => (π k y).1 := measurable_fst.comp hg
  exact (((Real.measurable_log.comp h1).add (measurable_const.mul
    (Real.measurable_log.comp (measurable_id.sub h1)))).sub
    (measurable_const.mul Real.measurable_log)).sub measurable_const

include hdomU hUc hUp in
lemma lu_Feq (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (hn : n ≤ M.N)
    (x : ℝ) (hx : 0 < x) :
    (∀ᵐ ω ∂M.measIP, ∀ i, i ≤ M.N - n → 0 < luX M π n x i ω) ∧
    (fun ω => (M.stateAcc π (M.N - n) n x ω).2 + M.Up (M.stateAcc π (M.N - n) n x ω).1) =ᵐ[M.measIP]
      fun ω => luW M n x + ∑ i ∈ Finset.range (M.N - n),
        (luGap M π (n + i) (luX M π n x i ω) +
          ((M.N : ℝ) - ((n + i : ℕ) : ℝ)) * (luG M π n x i ω - M.vLog (n + i))) := by
  have hall : ∀ᵐ ω ∂M.measIP, ∀ i, i ≤ M.N - n → 0 < luX M π n x i ω := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ≤ M.N - n
    · filter_upwards [lu_pos M hdomU π n hπ x hx i (by omega)] with ω h _ using h
    · exact Filter.Eventually.of_forall (fun ω h => absurd h hi)
  refine ⟨hall, ?_⟩
  filter_upwards [hall] with ω hω
  have := lu_path M hdomU hUc π n hπ x (M.N - n) (by omega) ω hω
  rw [show n + (M.N - n) = M.N by omega, luW_N] at this
  rw [← this]
  exact congrArg ((M.stateAcc π (M.N - n) n x ω).2 + ·) (hUp _ (hω _ le_rfl))

include hdomU hFM2 in
lemma lu_Gfacts (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (x : ℝ)
    (hx : 0 < x) (i : ℕ) (hi : n + i < M.N) :
    Measurable (luG M π n x i) ∧ ∫⁻ ω, ENNReal.ofReal (luG M π n x i ω) ∂M.measIP < ⊤ ∧
    (Integrable (luG M π n x i) M.measIP → ∫ ω, luG M π n x i ω ∂M.measIP ≤ M.vLog (n + i)) ∧
    0 ≤ M.vLog (n + i) := by
  haveI := M.isProb
  have hY : Measurable (luX M π n x i) :=
    (luX_meas M π n hπ x i hi.le).mono (ciF_le M _) le_rfl
  have hR : Measurable (M.R (n + i + 1)) := M.hR_meas _ (by omega) (by omega)
  have hind := luX_indep M π n hπ x i hi
  have hg := (hπ (n + i) (by omega) hi).2
  have hgm := lu_gfun_meas π (n + i) hg
  obtain ⟨K, hK, hV, hv0, -⟩ := lu_period M hFM2 (n + i) hi
  have hmem : ∀ y, 0 < y → luα π (n + i) y ∈ M.AfracLog (n + i) := by
    intro y hy
    obtain ⟨hc, hcy, hae⟩ := lu_adm M hdomU π n hπ (n + i) (by omega) hi y hy
    show ∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ l, luα π (n + i) y l * M.R (n + i + 1) ω l
    filter_upwards [hae] with ω h
    unfold ciT at h
    exact (lu_log_next (M.hi_pos _ (by omega) (by omega)) (sub_pos.2 hcy) h).1
  obtain ⟨g, hgd⟩ : ∃ g : ℝ × (Fin d → ℝ) → ℝ,
      g = fun p => Real.log (1 + ∑ l, luα π (n + i) p.1 l * p.2 l) := ⟨_, rfl⟩
  have hgm' : Measurable g := by rw [hgd]; exact hgm
  have hGeq : luG M π n x i = fun ω => g (luX M π n x i ω, M.R (n + i + 1) ω) := by
    rw [hgd]; rfl
  have hK' : ∀ y, 0 < y → ∫⁻ ω, ENNReal.ofReal (g (y, M.R (n + i + 1) ω)) ∂M.measIP ≤
      ENNReal.ofReal K := fun y hy => by rw [hgd]; beta_reduce; exact hK (luα π (n + i) y) (hmem y hy)
  have hV' : ∀ y, 0 < y → Integrable (fun ω => g (y, M.R (n + i + 1) ω)) M.measIP →
      ∫ ω, g (y, M.R (n + i + 1) ω) ∂M.measIP ≤ M.vLog (n + i) :=
    fun y hy hI => by rw [hgd] at hI ⊢; beta_reduce at hI ⊢; exact hV (luα π (n + i) y) (hmem y hy) hI
  have := lu_ind_int hY hR hind g hgm' (lu_pos M hdomU π n hπ x hx i hi.le) K (M.vLog (n + i))
    hK' hV'
  rw [hGeq]
  exact ⟨hgm'.comp (hY.prodMk hR), lt_of_le_of_lt this.1 ENNReal.ofReal_lt_top, this.2, hv0⟩

include hdomU in
lemma lu_gap_nonpos (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (k : ℕ)
    (hnk : n ≤ k) (hk : k < M.N) (y : ℝ) (hy : 0 < y) : luGap M π k y ≤ 0 := by
  obtain ⟨hc, hcy, -⟩ := lu_adm M hdomU π n hπ k hnk hk y hy
  have hm : (0 : ℝ) < (M.N : ℝ) - k := by
    have : (k : ℝ) + 1 ≤ M.N := by exact_mod_cast hk
    linarith
  exact lu_det hm hy hc hcy

lemma lu_m_ge (n i : ℕ) (hi : n + i < M.N) : (1 : ℝ) ≤ (M.N : ℝ) - ((n + i : ℕ) : ℝ) := by
  have : ((n + i : ℕ) : ℝ) + 1 ≤ M.N := by exact_mod_cast hi
  linarith

include hdomU hUc hUp hFM2 in
lemma lu_upper (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) (hn : n ≤ M.N)
    (x : ℝ) (hx : 0 < x) : M.Vpi π n x ≤ ((luW M n x : ℝ) : EReal) := by
  haveI := M.isProb
  obtain ⟨hall, heq⟩ := lu_Feq M hdomU hUc hUp π n hπ hn x hx
  unfold ConsumptionInvestmentMarket.Vpi
  rw [ci_erealIntegral_congr heq]
  set J := M.N - n with hJ
  set W := luW M n x with hW
  let m : ℕ → ℝ := fun i => (M.N : ℝ) - ((n + i : ℕ) : ℝ)
  let G : ℕ → Ω → ℝ := fun i => luG M π n x i
  let gap : ℕ → Ω → ℝ := fun i ω => luGap M π (n + i) (luX M π n x i ω)
  let v : ℕ → ℝ := fun i => M.vLog (n + i)
  let Fm : Ω → ℝ := fun ω => W + ∑ i ∈ Finset.range J, (gap i ω + m i * (G i ω - v i))
  show erealIntegral M.measIP (fun ω => (Fm ω : EReal)) ≤ (W : EReal)
  have hF := fun i (hi : i ∈ Finset.range J) =>
    lu_Gfacts M hdomU hFM2 π n hπ x hx i (by rw [Finset.mem_range] at hi; omega)
  have hm1 : ∀ i ∈ Finset.range J, 1 ≤ m i := fun i hi =>
    lu_m_ge M n i (by rw [Finset.mem_range] at hi; omega)
  have hgapm : ∀ i ∈ Finset.range J, Measurable (gap i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact (luGap_meas M π (n + i) (hπ (n + i) (by omega) (by omega)).2).comp
      ((luX_meas M π n hπ x i (by omega)).mono (ciF_le M _) le_rfl)
  have hgap0 : ∀ᵐ ω ∂M.measIP, ∀ i ∈ Finset.range J, gap i ω ≤ 0 := by
    filter_upwards [hall] with ω hω i hi
    rw [Finset.mem_range] at hi
    exact lu_gap_nonpos M hdomU π n hπ (n + i) (by omega) (by omega) _ (hω i hi.le)
  have hFmm : Measurable Fm := measurable_const.add (Finset.measurable_sum _ fun i hi =>
    (hgapm i hi).add (measurable_const.mul (((hF i hi).1).sub measurable_const)))
  by_cases htop : ∫⁻ ω, ENNReal.ofReal (-Fm ω) ∂M.measIP = ⊤
  · rw [lu_erealIntegral_bot htop]; exact bot_le
  have hofmax : ∀ a : ℝ, ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
    intro a; rcases le_total a 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  have hGp : ∀ i ∈ Finset.range J, Integrable (fun ω => max (G i ω) 0) M.measIP := by
    intro i hi
    refine (lintegral_ofReal_ne_top_iff_integrable
      ((hF i hi).1.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => le_max_right _ _)).1 ?_
    exact ne_of_eq_of_ne (lintegral_congr fun ω => hofmax (G i ω)) (hF i hi).2.1.ne
  have hFn : Integrable (fun ω => max (-Fm ω) 0) M.measIP := by
    refine (lintegral_ofReal_ne_top_iff_integrable
      (hFmm.neg.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => le_max_right _ _)).1 ?_
    exact ne_of_eq_of_ne (lintegral_congr fun ω => hofmax (-Fm ω)) htop
  have hSp : Integrable (fun ω => ∑ i ∈ Finset.range J, m i * max (G i ω) 0) M.measIP :=
    integrable_finset_sum _ fun i hi => (hGp i hi).const_mul _
  have hv0 : ∀ i ∈ Finset.range J, 0 ≤ v i := fun i hi => (hF i hi).2.2.2
  have hFmI : Integrable Fm M.measIP := by
    refine (((integrable_const |W|).add hSp).add hFn).mono' hFmm.aestronglyMeasurable ?_
    filter_upwards [hgap0] with ω hω
    have hup : Fm ω ≤ W + ∑ i ∈ Finset.range J, m i * max (G i ω) 0 := by
      show W + _ ≤ _
      have : ∑ i ∈ Finset.range J, (gap i ω + m i * (G i ω - v i)) ≤
          ∑ i ∈ Finset.range J, m i * max (G i ω) 0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have := hω i hi
        have h1 := hm1 i hi
        have h2 := hv0 i hi
        have h3 : G i ω - v i ≤ max (G i ω) 0 := by linarith [le_max_left (G i ω) 0]
        nlinarith
      linarith
    have hS0 : 0 ≤ ∑ i ∈ Finset.range J, m i * max (G i ω) 0 :=
      Finset.sum_nonneg fun i hi => mul_nonneg (by linarith [hm1 i hi]) (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor
    · linarith [le_max_left (-Fm ω) 0, abs_nonneg W]
    · linarith [le_abs_self W, le_max_right (-Fm ω) 0]
  -- integrability of each G
  have hGI : ∀ j ∈ Finset.range J, Integrable (G j) M.measIP := by
    intro j hj
    have hbI : Integrable (fun ω => max (G j ω) 0 + (∑ i ∈ Finset.range J, m i * max (G i ω) 0 -
        (Fm ω - W + ∑ i ∈ Finset.range J, m i * v i))) M.measIP :=
      (hGp j hj).add (hSp.sub ((hFmI.sub (integrable_const W)).add (integrable_const _)))
    refine hbI.mono' (hF j hj).1.aestronglyMeasurable ?_
    filter_upwards [hgap0] with ω hω
    have e : ∑ i ∈ Finset.range J, m i * max (G i ω) 0 -
        (Fm ω - W + ∑ i ∈ Finset.range J, m i * v i) =
        ∑ i ∈ Finset.range J, (m i * (max (G i ω) 0 - G i ω) - gap i ω) := by
      show _ - (W + _ - W + _) = _
      rw [Finset.sum_sub_distrib]
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    rw [e, Real.norm_eq_abs]
    have hnn : ∀ i ∈ Finset.range J, 0 ≤ m i * (max (G i ω) 0 - G i ω) - gap i ω := by
      intro i hi
      have := hω i hi
      have : 0 ≤ m i * (max (G i ω) 0 - G i ω) :=
        mul_nonneg (by linarith [hm1 i hi]) (by linarith [le_max_left (G i ω) 0])
      linarith
    have hsingle := Finset.single_le_sum hnn hj
    have hmj := hm1 j hj
    have hgj := hω j hj
    have hd : 0 ≤ max (G j ω) 0 - G j ω := by linarith [le_max_left (G j ω) 0]
    have hmd : max (G j ω) 0 - G j ω ≤ m j * (max (G j ω) 0 - G j ω) := by nlinarith
    rcases le_total 0 (G j ω) with h | h
    · rw [abs_of_nonneg h]; linarith [le_max_left (G j ω) 0]
    · rw [abs_of_nonpos h, max_eq_right h] at *; linarith
  have hint_le : ∫ ω, Fm ω ∂M.measIP ≤ W := by
    have hRI : Integrable (fun ω => W + ∑ i ∈ Finset.range J, m i * (G i ω - v i)) M.measIP :=
      (integrable_const W).add (integrable_finset_sum _ fun i hi =>
        ((hGI i hi).sub (integrable_const _)).const_mul _)
    calc ∫ ω, Fm ω ∂M.measIP
        ≤ ∫ ω, (W + ∑ i ∈ Finset.range J, m i * (G i ω - v i)) ∂M.measIP := by
          refine integral_mono_ae hFmI hRI ?_
          filter_upwards [hgap0] with ω hω
          show W + _ ≤ W + _
          have : ∑ i ∈ Finset.range J, (gap i ω + m i * (G i ω - v i)) ≤
              ∑ i ∈ Finset.range J, m i * (G i ω - v i) :=
            Finset.sum_le_sum fun i hi => by linarith [hω i hi]
          linarith
      _ = W + ∑ i ∈ Finset.range J, m i * (∫ ω, G i ω ∂M.measIP - v i) := by
          have hterm : ∀ i ∈ Finset.range J, Integrable (fun ω => m i * (G i ω - v i)) M.measIP :=
            fun i hi => ((hGI i hi).sub (integrable_const (v i))).const_mul (m i)
          rw [integral_add (integrable_const W) (integrable_finset_sum _ hterm),
            integral_finset_sum _ hterm]
          congr 1
          · simp
          · refine Finset.sum_congr rfl fun i hi => ?_
            rw [integral_const_mul, integral_sub (hGI i hi) (integrable_const _)]
            simp
      _ ≤ W := by
          have : ∑ i ∈ Finset.range J, m i * (∫ ω, G i ω ∂M.measIP - v i) ≤ 0 :=
            Finset.sum_nonpos fun i hi => mul_nonpos_of_nonneg_of_nonpos
              (by linarith [hm1 i hi]) (by linarith [(hF i hi).2.2.1 (hGI i hi)])
          linarith
  rw [ci_erealIntegral_of_integrable hFmI]
  exact EReal.coe_le_coe_iff.2 hint_le

noncomputable def luFstar (αs : ℕ → Fin d → ℝ) (k : ℕ) (y : ℝ) : ℝ × (Fin d → ℝ) :=
  (y / ((M.N : ℝ) - k + 1), fun l => y * (((M.N : ℝ) - k) / ((M.N : ℝ) - k + 1)) * αs k l)

lemma lu_m1 (k : ℕ) (hk : k < M.N) : (1 : ℝ) ≤ (M.N : ℝ) - k := by
  have : (k : ℝ) + 1 ≤ M.N := by exact_mod_cast hk
  linarith

lemma luFstar_next (αs : ℕ → Fin d → ℝ) (k : ℕ) (hk : k < M.N) (y : ℝ) (r : Fin d → ℝ) :
    y - (luFstar M αs k y).1 + ∑ l, (luFstar M αs k y).2 l * r l =
      y * (((M.N : ℝ) - k) / ((M.N : ℝ) - k + 1)) * (1 + ∑ l, αs k l * r l) := by
  have hm := lu_m1 M k hk
  simp only [luFstar]
  rw [show ∑ l, y * (((M.N : ℝ) - k) / ((M.N : ℝ) - k + 1)) * αs k l * r l =
      y * (((M.N : ℝ) - k) / ((M.N : ℝ) - k + 1)) * ∑ l, αs k l * r l by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring]
  have : (M.N : ℝ) - k + 1 ≠ 0 := by linarith
  field_simp
  ring

include hdomU in
lemma luFstar_adm (αs : ℕ → Fin d → ℝ) (hαs : ∀ k < M.N, αs k ∈ M.AfracLog k) (n : ℕ) :
    M.IsAdmissible n (luFstar M αs) := by
  intro k _ hk
  have hm := lu_m1 M k hk
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [hdomU] at hy
    have hy : 0 < y := hy
    have hc : 0 < y / ((M.N : ℝ) - k + 1) := div_pos hy (by linarith)
    refine ⟨hc.le, div_le_self hy.le (by linarith), by rw [hdomU]; exact hc, ?_⟩
    filter_upwards [hαs k hk] with ω h
    rw [hdomU, luFstar_next M αs k hk y]
    exact mul_pos (M.hi_pos _ (by omega) (by omega))
      (mul_pos (mul_pos hy (div_pos (by linarith) (by linarith))) h)
  · unfold luFstar
    exact (measurable_id.div_const _).prodMk (measurable_pi_lambda _ fun l =>
      (measurable_id.mul_const _).mul_const _)

lemma luFstar_α (αs : ℕ → Fin d → ℝ) (k : ℕ) (hk : k < M.N) (y : ℝ) (hy : 0 < y) :
    luα (luFstar M αs) k y = αs k := by
  have hm := lu_m1 M k hk
  have e : y - y / ((M.N : ℝ) - k + 1) = y * (((M.N : ℝ) - k) / ((M.N : ℝ) - k + 1)) := by
    have : (M.N : ℝ) - k + 1 ≠ 0 := by linarith
    field_simp; ring
  have hne : y * (((M.N : ℝ) - k) / ((M.N : ℝ) - k + 1)) ≠ 0 :=
    (mul_pos hy (div_pos (by linarith) (by linarith))).ne'
  funext l
  simp only [luα, luFstar, Pi.smul_apply, smul_eq_mul]
  rw [e, inv_mul_cancel_left₀ hne]

lemma luFstar_gap (αs : ℕ → Fin d → ℝ) (k : ℕ) (hk : k < M.N) (y : ℝ) (hy : 0 < y) :
    luGap M (luFstar M αs) k y = 0 := by
  have hm := lu_m1 M k hk
  unfold luGap luFstar
  exact lu_det_eq (by linarith) hy

include hdomU hUc hUp hFM2 in
lemma luFstar_value (αs : ℕ → Fin d → ℝ) (hαs : ∀ k < M.N, αs k ∈ M.AfracLog k ∧
      Integrable (fun ω => Real.log (1 + ∑ l, αs k l * M.R (k + 1) ω l)) M.measIP ∧
      ∫ ω, Real.log (1 + ∑ l, αs k l * M.R (k + 1) ω l) ∂M.measIP = M.vLog k)
    (n : ℕ) (hn : n ≤ M.N) (x : ℝ) (hx : 0 < x) :
    M.Vpi (luFstar M αs) n x = ((luW M n x : ℝ) : EReal) := by
  haveI := M.isProb
  have hadm := luFstar_adm M hdomU αs (fun k hk => (hαs k hk).1) n
  obtain ⟨hall, heq⟩ := lu_Feq M hdomU hUc hUp (luFstar M αs) n hadm hn x hx
  unfold ConsumptionInvestmentMarket.Vpi
  rw [ci_erealIntegral_congr heq]
  have heq2 : (fun ω => luW M n x + ∑ i ∈ Finset.range (M.N - n),
        (luGap M (luFstar M αs) (n + i) (luX M (luFstar M αs) n x i ω) +
          ((M.N : ℝ) - ((n + i : ℕ) : ℝ)) * (luG M (luFstar M αs) n x i ω - M.vLog (n + i))))
      =ᵐ[M.measIP] fun ω => luW M n x + ∑ i ∈ Finset.range (M.N - n),
        ((M.N : ℝ) - ((n + i : ℕ) : ℝ)) *
          (Real.log (1 + ∑ l, αs (n + i) l * M.R (n + i + 1) ω l) - M.vLog (n + i)) := by
    filter_upwards [hall] with ω hω
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [luFstar_gap M αs (n + i) (by omega) _ (hω i hi.le), zero_add]
    unfold luG
    rw [luFstar_α M αs (n + i) (by omega) _ (hω i hi.le)]
  have hterm : ∀ i ∈ Finset.range (M.N - n), Integrable (fun ω => ((M.N : ℝ) - ((n + i : ℕ) : ℝ)) *
      (Real.log (1 + ∑ l, αs (n + i) l * M.R (n + i + 1) ω l) - M.vLog (n + i))) M.measIP := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact ((hαs (n + i) (by omega)).2.1.sub (integrable_const _)).const_mul _
  have hI : Integrable (fun ω => luW M n x + ∑ i ∈ Finset.range (M.N - n),
        ((M.N : ℝ) - ((n + i : ℕ) : ℝ)) *
          (Real.log (1 + ∑ l, αs (n + i) l * M.R (n + i + 1) ω l) - M.vLog (n + i))) M.measIP :=
    (integrable_const (luW M n x)).add (integrable_finset_sum _ hterm)
  rw [ci_erealIntegral_congr heq2, ci_erealIntegral_of_integrable hI]
  congr 1
  rw [integral_add (integrable_const _) (integrable_finset_sum _ hterm),
    integral_finset_sum _ hterm]
  have : ∀ i ∈ Finset.range (M.N - n), ∫ ω, ((M.N : ℝ) - ((n + i : ℕ) : ℝ)) *
      (Real.log (1 + ∑ l, αs (n + i) l * M.R (n + i + 1) ω l) - M.vLog (n + i)) ∂M.measIP = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [integral_const_mul, integral_sub (hαs (n + i) (by omega)).2.1 (integrable_const _),
      (hαs (n + i) (by omega)).2.2]
    simp
  rw [Finset.sum_congr rfl this]
  simp

include hdomU hUc hUp hFM2 in
lemma lu_V (αs : ℕ → Fin d → ℝ) (hαs : ∀ k < M.N, αs k ∈ M.AfracLog k ∧
      Integrable (fun ω => Real.log (1 + ∑ l, αs k l * M.R (k + 1) ω l)) M.measIP ∧
      ∫ ω, Real.log (1 + ∑ l, αs k l * M.R (k + 1) ω l) ∂M.measIP = M.vLog k)
    (n : ℕ) (hn : n ≤ M.N) (x : ℝ) (hx : 0 < x) :
    M.V n x = ((luW M n x : ℝ) : EReal) := by
  apply le_antisymm
  · exact iSup₂_le fun π hπ => lu_upper M hdomU hUc hUp hFM2 π n hπ hn x hx
  · rw [← luFstar_value M hdomU hUc hUp hFM2 αs hαs n hn x hx]
    exact le_iSup₂ (f := fun π (_ : π ∈ {π : ℕ → ℝ → ℝ × (Fin d → ℝ) | M.IsAdmissible n π}) =>
      M.Vpi π n x) (luFstar M αs) (luFstar_adm M hdomU αs (fun k hk => (hαs k hk).1) n)

end Main

theorem log_utility_ci_solution_core {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hFM2 : M.FM2) (hdomU : M.domU = Set.Ioi (0 : ℝ))
    (hUc : ∀ x > (0 : ℝ), M.Uc x = Real.log x) (hUp : ∀ x > (0 : ℝ), M.Up x = Real.log x) :
    (∃ dseq : ℕ → ℝ, ∀ n ≤ M.N, ∀ x > (0 : ℝ),
        M.V n x = ((((M.N : ℝ) - n + 1) * Real.log x + dseq n : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.AfracLog n ∧
          ∫ ω, Real.log (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ∂M.measIP = M.vLog n) ∧
        ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), (fstar n x).1 = x / ((M.N : ℝ) - n + 1)) ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), (fstar n x).2 =
            fun k => x * (((M.N : ℝ) - n) / ((M.N : ℝ) - n + 1)) * αstar n k) ∧
          ∀ x > (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by
  have hex : ∀ k, ∃ α : Fin d → ℝ, k < M.N → (α ∈ M.AfracLog k ∧
      Integrable (fun ω => Real.log (1 + ∑ l, α l * M.R (k + 1) ω l)) M.measIP ∧
      ∫ ω, Real.log (1 + ∑ l, α l * M.R (k + 1) ω l) ∂M.measIP = M.vLog k) := by
    intro k
    by_cases hk : k < M.N
    · obtain ⟨K, -, -, -, αs, h1, h2, h3⟩ := lu_period M hFM2 k hk
      exact ⟨αs, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose αs hαs using hex
  refine ⟨⟨luD M, fun n hn x hx => ?_⟩, ⟨αs, fun n hn => ⟨(hαs n hn).1, (hαs n hn).2.2⟩,
    luFstar M αs, luFstar_adm M hdomU αs (fun k hk => (hαs k hk).1) 0,
    fun n hn x hx => rfl, fun n hn x hx => rfl, fun x hx => ?_⟩⟩
  · rw [lu_V M hdomU hUc hUp hFM2 αs hαs n hn x hx]; rfl
  · rw [lu_V M hdomU hUc hUp hFM2 αs hαs 0 (Nat.zero_le _) x hx,
      luFstar_value M hdomU hUc hUp hFM2 αs hαs 0 (Nat.zero_le _) x hx]

end MDPFinance.ConsumptionInvestment

open MDPFinance.ConsumptionInvestment


theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hFM2 : M.FM2) (hdomU : M.domU = Set.Ioi (0 : ℝ))
    (hUc : ∀ x > (0 : ℝ), M.Uc x = Real.log x) (hUp : ∀ x > (0 : ℝ), M.Up x = Real.log x) :
    (∃ dseq : ℕ → ℝ, ∀ n ≤ M.N, ∀ x > (0 : ℝ),
        M.V n x = ((((M.N : ℝ) - n + 1) * Real.log x + dseq n : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.AfracLog n ∧
          ∫ ω, Real.log (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ∂M.measIP = M.vLog n) ∧
        ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), (fstar n x).1 = x / ((M.N : ℝ) - n + 1)) ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), (fstar n x).2 =
            fun k => x * (((M.N : ℝ) - n) / ((M.N : ℝ) - n + 1)) * αstar n k) ∧
          ∀ x > (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by
  exact log_utility_ci_solution_core M hFM2 hdomU hUc hUp
