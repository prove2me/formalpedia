-- Prove2me | solution 1 for HedgePSNV.tilted_bayes_conditional_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T17:32:32.391638+00:00
-- url     : https://prove2.me/submissions/f7a3e93b-0b5e-496a-bc83-7949196c0b58

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Theorems.Thm_HedgePSNV_tilted_density_increment_representation
import Theorems.Thm_HedgePSNV_subfiltration_projection_zero
import Theorems.Thm_HedgePSNV_conditional_tail_integrand_representation

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false




-- ===== slice of Solutions.Sol_pv_1558a108 (scratch/probe/slice8c/cuts/r_tce3.lean.src/Solutions.Sol_pv_1558a108.lean): 24/153 top-level decls kept =====

set_option linter.all false
-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

/-- The coordinates of a standard `d`-dimensional Brownian motion form one real Gaussian
process indexed by `time × coordinate`. -/
theorem stdBrownian_isGaussianProcess {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) :
    IsGaussianProcess (fun (p : ℝ≥0 × Fin d) ω => W p.1 ω p.2) P := by
  obtain ⟨_, _, hBM, hind⟩ := hW
  refine ⟨fun I => ?_⟩
  classical
  let I' : Finset ℝ≥0 := I.image Prod.fst
  let V : Fin d → Ω → (I' → ℝ) := fun i ω => fun t => W t ω i
  have hV : ∀ i, HasGaussianLaw (V i) P := fun i =>
    (hBM i).isGaussianProcess.hasGaussianLaw I'
  have hVind : iIndepFun V P :=
    hind.comp (fun _ (f : ℝ≥0 → ℝ) => fun t : I' => f t) (fun _ => by fun_prop)
  have hjoint := hVind.hasGaussianLaw hV
  let L0 : (Fin d → (I' → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x p => x p.1.2 ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have := hjoint.map (LinearMap.toContinuousLinearMap L0)
  have heq : (fun ω => I.restrict (fun p : ℝ≥0 × Fin d => W p.1 ω p.2)) =
      (LinearMap.toContinuousLinearMap L0) ∘ (fun ω x => V x ω) := by
    funext ω p; rfl
  rw [heq]; exact this

/-- The covariance of two coordinates of a standard Brownian motion. -/
theorem stdBrownian_cov {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s t : ℝ≥0) (i j : Fin d) :
    cov[fun ω => W s ω i, fun ω => W t ω j; P] = if i = j then ((min s t : ℝ≥0) : ℝ) else 0 := by
  obtain ⟨hm, _, hBM, hind⟩ := hW
  split_ifs with hij
  · subst hij
    exact (hBM i).covariance_fun_eval s t
  · have h2 : IndepFun (fun ω => W s ω i) (fun ω => W t ω j) P := by
      have := hind.indepFun hij
      exact this.comp (φ := fun f : ℝ≥0 → ℝ => f s) (ψ := fun f : ℝ≥0 → ℝ => f t)
        (by fun_prop) (by fun_prop)
    have hP : IsProbabilityMeasure P := (hBM i).isGaussianProcess.isProbabilityMeasure
    exact h2.covariance_eq_zero ((hBM i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      ((hBM j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem stdBrownian_coord_measurable {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : Measurable (fun ω => W t ω i) := by
  have := hW.1 t
  fun_prop

theorem stdBrownian_memLp_two {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : MemLp (fun ω => W t ω i) 2 P :=
  ((hW.2.2.1 i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two


end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

/-- The `P`-a.e. closure of a σ-algebra `G`: sets a.e. equal to a `G`-set (null sets taken
for the outer measure, so arbitrary subsets of null sets qualify). -/
@[instance_reducible]
def aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B, MeasurableSet[G] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ G, EventuallyEq.rfl⟩
  measurableSet_compl A := fun ⟨B, hB, h⟩ => ⟨Bᶜ, hB.compl, h.compl⟩
  measurableSet_iUnion f hf := by
    choose B hB h using hf
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, Filter.EventuallyEq.countable_iUnion h⟩

theorem le_aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : G ≤ aeClosure P G :=
  fun A hA => ⟨A, hA, EventuallyEq.rfl⟩

/-- Independence passes to the a.e. closure. -/
theorem indep_aeClosure {P : Measure Ω} {G H : MeasurableSpace Ω} (h : Indep G H P) :
    Indep (aeClosure P G) H P := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨B, hB, hAB⟩ hC
  rw [measure_congr (hAB.inter (EventuallyEq.refl _ C)), measure_congr hAB]
  exact h B C hB hC

end AEC

section CP
variable [MeasurableSpace Ω]

/-- With a constant initial value, the completed Brownian past lies in the a.e. closure of the
natural Brownian past. -/
theorem completedBrownianPast_const_le (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : ℝ≥0) :
    completedBrownianPast P W (fun _ => x₀) s ≤
      aeClosure P (⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance) := by
  set G : MeasurableSpace Ω := ⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance
  refine sup_le (sup_le (le_aeClosure _ _) ?_) ?_
  · rintro A ⟨T, -, rfl⟩
    by_cases hx : x₀ ∈ T
    · refine ⟨Set.univ, @MeasurableSet.univ Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = Set.univ := Set.preimage_const_of_mem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
    · refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = ∅ := Set.preimage_const_of_notMem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨N, -, hN, hAN⟩
    refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
    rw [ae_eq_empty]
    exact measure_mono_null hAN hN


end CP

section M2


variable [MeasurableSpace Ω]






end M2

section M3
variable [MeasurableSpace Ω]

theorem completedBrownianPast_mono (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩




end M3

section M4
variable [MeasurableSpace Ω]


end M4


section StopCoef






end StopCoef

section M5
variable [MeasurableSpace Ω]




end M5


section M5b

theorem tendstoInMeasure_zero_of_abs_le [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {F A B : ι → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hA : TendstoInMeasure P A l (fun _ => 0)) (hB : TendstoInMeasure P B l (fun _ => 0))
    (hF : ∀ i ω, |F i ω| ≤ K * (|A i ω| + |B i ω|)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hA hB ⊢
  intro ε hε
  have hε' : 0 < ε / (2 * K) := by positivity
  have hsum := (hA _ hε').add (hB _ hε')
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hF i ω
  have h2 : K * (|A i ω| + |B i ω|) < K * (ε / (2 * K) + ε / (2 * K)) :=
    mul_lt_mul_of_pos_left (add_lt_add hcon.1 hcon.2) hK
  have h3 : K * (ε / (2 * K) + ε / (2 * K)) = ε := by field_simp; ring
  linarith only [hω, h1, h2, h3]





theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]

theorem itoStepValue_sq (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    (itoStepValue t n c u ω) ^ 2 = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key : ∀ p q : ℕ, p < q →
      ((p : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ (q : ℝ) * t.val / (2 : ℝ) ^ n := by
    intro p q hpq
    have : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hT) h2.le
  unfold itoStepValue
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single k]
  · simp only [Set.indicator_apply, Set.mem_Ioc]; split_ifs <;> ring
  · intro l _ hlk
    split_ifs with h1 h2 <;> try ring
    exfalso
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · linarith only [key l k hlt, h1.1, h2.2]
    · linarith only [key k l hgt, h1.2, h2.1]
  · intro hk'; exact absurd hk hk'

theorem intervalIntegrable_indicator_Ioc_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ioc a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ioc

theorem itoStepValue_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => itoStepValue t n c u ω) volume 0 t.val := by
  have heq : (fun u => itoStepValue t n c u ω) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_eq_sum_indicator]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

theorem itoStepValue_sq_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue t n c u ω) ^ 2) volume 0 t.val := by
  have heq : (fun u => (itoStepValue t n c u ω) ^ 2) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_sq]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)


end M5b

section M5c
variable [MeasurableSpace Ω]


end M5c


section M6refine



end M6refine


section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N


/-- Oscillation event: two dyadic times in `[0,t]` at distance at most `δ` at which `H` differs
by more than `η`. -/
def oscSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (δ η : ℝ) : Set Ω :=
  ⋃ p : (ℕ × ℕ) × (ℕ × ℕ), {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
    |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
    η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|}

theorem dyTime_le (t : ℝ≥0) {N j : ℕ} (h : j ≤ 2 ^ N) : dyTime t N j ≤ t := by
  unfold dyTime
  rw [div_le_iff₀ (by positivity)]
  calc (j : ℝ≥0) * t ≤ (2 : ℝ≥0) ^ N * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
    _ = t * 2 ^ N := mul_comm _ _


theorem oscSet_mono (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (η : ℝ) :
    oscSet H t δ η ⊆ oscSet H t δ' η := by
  intro ω hω
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
  exact Set.mem_iUnion.2 ⟨p, hp.1, hp.2.1, hp.2.2.1.trans hδ, hp.2.2.2⟩


theorem iInter_oscSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  have huc : UniformContinuousOn (fun s => H s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hHc ω).continuousOn
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / δ)
  have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have htn : (t : ℝ) / 2 ^ n < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    have hnδ := mul_lt_mul_of_pos_right h2n hδ
    linarith only [hn, hnδ]
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  exact absurd hp4 (not_lt.2 this.le)


end M6osc


section M6cauchy
variable [MeasurableSpace Ω]


end M6cauchy


section M6limit
variable [MeasurableSpace Ω]



end M6limit


section M6trunc











/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht, mul_comm (2 ^ n : ℝ)]; exact mul_le_mul_of_nonneg_right hu.2 h2.le
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith only [this, hkR]
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith only [hlt]
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith only [hge]
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1', this, hlo]
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1, this, hhi]
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'

/-- Off the oscillation event of mesh `t/2^n`, `H` at the left grid point `t_k` is within `η` of
`H u` for every `u ∈ [t_k, t_{k+1}]` (dyadic approximation of `u` from the left + continuity). -/
theorem abs_H_sub_le_of_not_mem_oscSet {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n k : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω}
    (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η) (hk : k < 2 ^ n) {u : ℝ} (hu0 : 0 ≤ u)
    (hlo : (k : ℝ) * t.val / 2 ^ n ≤ u) (hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n)
    (hut : u ≤ t.val) :
    |H (dyTime t n k) ω - H u.toNNReal ω| ≤ η := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · have hu : u = 0 := le_antisymm (h0 ▸ hut) hu0
    have hd : dyTime t n k = 0 := by
      have : t = 0 := NNReal.coe_eq_zero.1 h0.symm
      simp [dyTime, this]
    rw [hu, hd, Real.toNNReal_zero, sub_self, abs_zero]
    exact hη
  set y : ℕ → ℝ := fun m => u * 2 ^ (m + n) / t.val with hy
  set s : ℕ → ℝ≥0 := fun m => dyTime t (m + n) ⌊y m⌋₊ with hs
  have hsR : ∀ m, (s m : ℝ) = (⌊y m⌋₊ : ℝ) * t.val / 2 ^ (m + n) := fun m => by
    simp [hs, dyTime]
  have hy0 : ∀ m, 0 ≤ y m := fun m => by simp only [hy]; positivity
  have hyt : ∀ m, y m * t.val / 2 ^ (m + n) = u := fun m => by
    simp only [hy]; field_simp
  have hs_le : ∀ m, (s m : ℝ) ≤ u := fun m => by
    rw [hsR, ← hyt m]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le (hy0 m)) ht)
      (by positivity)
  have hs_gt : ∀ m, u - t.val / 2 ^ (m + n) ≤ (s m : ℝ) := fun m => by
    have h1 := Nat.lt_floor_add_one (y m)
    have h3 : u - t.val / 2 ^ (m + n) = (y m - 1) * t.val / 2 ^ (m + n) := by
      rw [← hyt m]; field_simp; try ring
    rw [hsR, h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [h1]) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      have h2m := mul_le_mul_of_nonneg_left hlo (pow_pos (two_pos (α := ℝ)) m).le
      linarith only [h2m]
    have hfl : ((k * 2 ^ m : ℕ) : ℝ) ≤ (⌊y m⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor hkm
    have e : (dyTime t n k : ℝ) = ((k * 2 ^ m : ℕ) : ℝ) * t.val / 2 ^ (m + n) := by
      simp only [dyTime]; push_cast; rw [pow_add]; field_simp; try rfl
    rw [e, hsR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfl ht) (by positivity)
  have hdk : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by simp [dyTime]
  have hbound : ∀ m, |H (dyTime t n k) ω - H (s m) ω| ≤ η := fun m => by
    by_contra hc
    refine hω (Set.mem_iUnion.2 ⟨((n, k), (m + n, ⌊y m⌋₊)), hk.le, ?_, ?_, lt_of_not_ge hc⟩)
    · refine Nat.floor_le_of_le ?_
      simp only [hy]
      rw [div_le_iff₀ hpos]; push_cast
      exact (mul_le_mul_of_nonneg_right hut (by positivity)).trans_eq (mul_comm _ _)
    · show |(dyTime t n k : ℝ) - (s m : ℝ)| ≤ (t : ℝ) / 2 ^ n
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hs_ge m])]
      have hcell : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by
        ring
      have hsm := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith only [hcell, hsm, hhi]
  have hreal : Tendsto (fun m => (s m : ℝ)) atTop (𝓝 u) := by
    have hpow : Tendsto (fun m : ℕ => t.val / 2 ^ (m + n)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))).comp
        (tendsto_add_atTop_nat n)
      exact Tendsto.div_atTop tendsto_const_nhds h
    have hlow : Tendsto (fun m : ℕ => u - t.val / 2 ^ (m + n)) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_gt hs_le
  have hnn : Tendsto s atTop (𝓝 u.toNNReal) := by
    have := (continuous_real_toNNReal.tendsto u).comp hreal
    simpa [Function.comp_def] using this
  have hcont : Continuous fun x : ℝ≥0 => |H (dyTime t n k) ω - H x ω| :=
    (continuous_const.sub (hHc ω)).abs
  exact le_of_tendsto' ((hcont.tendsto u.toNNReal).comp hnn) (fun m => hbound m)





end M6trunc

section M6exist
variable [MeasurableSpace Ω]




end M6exist


section M7grid







end M7grid

section M7zero
variable [MeasurableSpace Ω]



end M7zero


section M7qv
variable [MeasurableSpace Ω]











end M7qv

section M7c
variable [MeasurableSpace Ω]



end M7c

section M8a
variable [MeasurableSpace Ω]








end M8a

section M8b
variable [MeasurableSpace Ω]


end M8b

section M8c
variable [MeasurableSpace Ω]



end M8c

section M8d
variable [MeasurableSpace Ω]




end M8d

section M8e
variable [MeasurableSpace Ω]






end M8e


section M8f
variable [MeasurableSpace Ω]


end M8f


section M8f2
variable [MeasurableSpace Ω]

theorem itoStepValue_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, itoStepValue t n c u ω =
      (∑ k ∈ Finset.range (2 ^ n), c k ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith only [this]
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

/-- M8f: left-point Riemann sums of a pathwise continuous process converge pathwise. -/
theorem riemann_tendsto {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 (∫ u in (0 : ℝ)..t.val, H u.toNNReal ω)) := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (t.val + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hempty := iInter_oscSet_eq_empty hHc t hη
  have hex : ∃ n0 : ℕ, ω ∉ oscSet H t ((t : ℝ) / 2 ^ n0) η := by
    by_contra h
    push_neg at h
    have hmem : ω ∈ (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) := Set.mem_iInter.2 h
    rw [hempty] at hmem
    exact hmem
  obtain ⟨n0, hn0⟩ := hex
  refine ⟨n0, fun n hn => ?_⟩
  have hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h => hn0 (oscSet_mono H t
    (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hn)) η h)
  have hI := itoStepValue_integral t n (fun k ω => H (dyTime t n k) ω) ω
  have hHi : IntervalIntegrable (fun u : ℝ => H u.toNNReal ω) volume 0 t.val :=
    ((hHc ω).comp continuous_real_toNNReal).intervalIntegrable _ _
  rw [Real.dist_eq, ← hI, ← intervalIntegral.integral_sub
    (itoStepValue_intervalIntegrable _ _ _ _) hHi]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖itoStepValue t n (fun k ω => H (dyTime t n k) ω) u ω - H u.toNNReal ω‖ ≤ η := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ :=
      itoStepValue_eq_cell t n (fun k ω => H (dyTime t n k) ω) hu ω
    rw [hval, Real.norm_eq_abs]
    exact abs_H_sub_le_of_not_mem_oscSet hHc t n k hη.le hω hk hu.1.le hlo.le hhi hu.2
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at hle
  refine lt_of_le_of_lt hle ?_
  rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  linarith only [mul_nonneg hε.le ht, hε]





end M8f2


section M8f3
variable [MeasurableSpace Ω]







end M8f3


section M8gTaylor
open Set



end M8gTaylor

section M8g
variable [MeasurableSpace Ω]



end M8g


section M8g2







end M8g2


section M8g3
variable [MeasurableSpace Ω]








end M8g3

section M8g4
variable [MeasurableSpace Ω]





end M8g4

section M8g5
variable [MeasurableSpace Ω]





end M8g5

section M9a
variable [MeasurableSpace Ω]




end M9a


section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib


-- ===== slice of P8c066573M16 (scratch/probe/slice8c/cuts/r_tce3.lean.src/P8c066573M16.lean): 131/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


lemma pair_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    Measurable (fun ω => (M.B t ω, M.Bt t ω)) := by
  have h1 : MeasurableSpace.comap (fun ω => (M.B t ω, M.Bt t ω)) inferInstance ≤ M.F t := by
    rw [hM.filtF t]
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le (f := fun s (_ : s ≤ t) =>
      MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance) t le_rfl le_rfl
  exact Measurable.of_comap_le (h1.trans (M.F.le t))

lemma B_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.B t) :=
  measurable_fst.comp (pair_measurable M hM t)

lemma Bt_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.Bt t) :=
  measurable_snd.comp (pair_measurable M hM t)

/-- The exceptional null set off which both Brownian paths are continuous. -/
def Nbad (M : Model p Ω) : Set Ω :=
  toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}

lemma Nbad_meas (M : Model p Ω) : MeasurableSet (Nbad M) := measurableSet_toMeasurable _ _

lemma Nbad_null (M : Model p Ω) (hM : M.Standing) : M.P (Nbad M) = 0 := by
  rw [Nbad, measure_toMeasurable]
  exact ae_iff.1 (hM.brownB.cont.and hM.brownBt.cont)

lemma not_Nbad (M : Model p Ω) {ω : Ω} (h : ω ∉ Nbad M) :
    Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω) := by
  by_contra h'
  exact h (subset_toMeasurable _ _ h')

lemma ae_not_Nbad (M : Model p Ω) (hM : M.Standing) : ∀ᵐ ω ∂M.P, ω ∉ Nbad M := by
  rw [ae_iff]; simpa using Nbad_null M hM

open Classical in
/-- The two coordinates, set to `0` on `Nbad`. -/
noncomputable def gB (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ Nbad M then 0 else M.B t ω

open Classical in
noncomputable def gBt (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ Nbad M then 0 else M.Bt t ω

/-- The standard 2-d Brownian motion `(B, B~)` with everywhere continuous paths. -/
noncomputable def W (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : SDEState 2 :=
  WithLp.toLp 2 ![gB M t ω, gBt M t ω]

@[simp] lemma W_zero (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : W M t ω 0 = gB M t ω := by
  simp [W]

@[simp] lemma W_one (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : W M t ω 1 = gBt M t ω := by
  simp [W]

lemma ae_W (M : Model p Ω) (hM : M.Standing) :
    ∀ᵐ ω ∂M.P, ∀ t, W M t ω 0 = M.B t ω ∧ W M t ω 1 = M.Bt t ω := by
  filter_upwards [ae_not_Nbad M hM] with ω hω t
  simp [gB, gBt, hω]

lemma gB_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (gB M t) :=
  Measurable.ite (Nbad_meas M) measurable_const (B_measurable M hM t)

lemma gBt_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (gBt M t) :=
  Measurable.ite (Nbad_meas M) measurable_const (Bt_measurable M hM t)

lemma W_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (W M t) := by
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  fin_cases i
  · simpa using gB_measurable M hM t
  · simpa using gBt_measurable M hM t

lemma gB_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => gB M t ω) := by
  by_cases h : ω ∈ Nbad M
  · simp only [gB, h, if_true]; exact continuous_const
  · simp only [gB, h, if_false]; exact (not_Nbad M h).1

lemma gBt_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => gBt M t ω) := by
  by_cases h : ω ∈ Nbad M
  · simp only [gBt, h, if_true]; exact continuous_const
  · simp only [gBt, h, if_false]; exact (not_Nbad M h).2

lemma W_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => W M t ω) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · simpa using gB_cont M ω
  · simpa using gBt_cont M ω

lemma gB_brownian (M : Model p Ω) (hM : M.Standing) : IsBrownianReal (gB M) M.P := by
  have hae : ∀ t, M.B t =ᵐ[M.P] gB M t := by
    intro t
    filter_upwards [ae_not_Nbad M hM] with ω hω
    simp [gB, hω]
  exact { toIsPreBrownianReal := hM.brownB.toIsPreBrownianReal.congr hae,
          cont := Eventually.of_forall fun ω => gB_cont M ω }

lemma gBt_brownian (M : Model p Ω) (hM : M.Standing) : IsBrownianReal (gBt M) M.P := by
  have hae : ∀ t, M.Bt t =ᵐ[M.P] gBt M t := by
    intro t
    filter_upwards [ae_not_Nbad M hM] with ω hω
    simp [gBt, hω]
  exact { toIsPreBrownianReal := hM.brownBt.toIsPreBrownianReal.congr hae,
          cont := Eventually.of_forall fun ω => gBt_cont M ω }

lemma gB_indep (M : Model p Ω) (hM : M.Standing) :
    IndepFun (fun ω t => gB M t ω) (fun ω t => gBt M t ω) M.P := by
  refine hM.indep.congr ?_ ?_
  · filter_upwards [ae_not_Nbad M hM] with ω hω
    funext t; simp [gB, hω]
  · filter_upwards [ae_not_Nbad M hM] with ω hω
    funext t; simp [gBt, hω]

lemma iIndepFun_fin_two {β : Type*} [MeasurableSpace β] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Fin 2 → Ω → β} (h : IndepFun (f 0) (f 1) μ) : iIndepFun f μ := by
  have hcases : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hS
  rcases hcases S with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · have h0 := hS 0 (by simp)
    have h1 := hS 1 (by simp)
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
    have := h _ _ h0 h1
    have hI : (⋂ i, f i ⁻¹' sets i) = f 0 ⁻¹' sets 0 ∩ f 1 ⁻¹' sets 1 := by
      ext ω; simp [Fin.forall_fin_two]
    simpa [Fin.prod_univ_two, hI] using this

lemma isStandardBrownian (M : Model p Ω) (hM : M.Standing) : IsStandardBrownian M.P (W M) := by
  refine ⟨W_measurable M hM, W_cont M, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using gB_brownian M hM
    · simpa using gBt_brownian M hM
  · have := hM.prob
    apply iIndepFun_fin_two
    simpa using gB_indep M hM

lemma cBP_null (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) (A : Set Ω) (hA : A ⊆ Nbad M) :
    MeasurableSet[completedBrownianPast M.P (W M) (fun _ => 0) t] A := by
  have h1 : MeasurableSet[MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N}] A :=
    MeasurableSpace.measurableSet_generateFrom ⟨Nbad M, Nbad_meas M, Nbad_null M hM, hA⟩
  exact (le_sup_right : MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N} ≤ _) A h1

lemma cBP_nullset (M : Model p Ω) (t : ℝ≥0) (N : Set Ω) (hN : MeasurableSet N) (hN0 : M.P N = 0) :
    MeasurableSet[completedBrownianPast M.P (W M) (fun _ => 0) t] N := by
  have h1 : MeasurableSet[MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N}] N :=
    MeasurableSpace.measurableSet_generateFrom ⟨N, hN, hN0, subset_rfl⟩
  exact (le_sup_right : MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N} ≤ _) N h1

lemma W_meas_cBP (M : Model p Ω) (t s : ℝ≥0) (hs : s ≤ t) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (W M s) := by
  refine Measurable.of_comap_le ?_
  refine le_sup_of_le_left (le_sup_of_le_left ?_)
  exact le_iSup (f := fun s' : Set.Iic t => MeasurableSpace.comap (W M s'.val) inferInstance)
    ⟨s, hs⟩

lemma pairW_meas_cBP (M : Model p Ω) (t s : ℝ≥0) (hs : s ≤ t) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t]
      (fun ω => (W M s ω 0, W M s ω 1)) :=
  ((measurable_pi_apply 0).comp ((WithLp.measurable_ofLp 2 _).comp (W_meas_cBP M t s hs))).prodMk
    ((measurable_pi_apply 1).comp ((WithLp.measurable_ofLp 2 _).comp (W_meas_cBP M t s hs)))

/-- The model filtration sits inside the completed Brownian past of `W`. -/
lemma F_le_cBP (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    M.F t ≤ completedBrownianPast M.P (W M) (fun _ => 0) t := by
  rw [hM.filtF t]
  refine sup_le (iSup₂_le fun s hs => ?_) ?_
  · refine Measurable.comap_le ?_
    intro S hS
    have hset : (fun ω => (M.B s ω, M.Bt s ω)) ⁻¹' S =
        ((fun ω => (M.B s ω, M.Bt s ω)) ⁻¹' S ∩ Nbad M) ∪
          ((Nbad M)ᶜ ∩ (fun ω => (W M s ω 0, W M s ω 1)) ⁻¹' S) := by
      ext ω
      by_cases h : ω ∈ Nbad M <;> simp [h, gB, gBt]
    rw [hset]
    refine MeasurableSet.union (cBP_null M hM t _ Set.inter_subset_right) ?_
    exact MeasurableSet.inter (cBP_null M hM t _ subset_rfl).compl (pairW_meas_cBP M t s hs hS)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro N ⟨hN, hN0⟩
    exact cBP_nullset M t N hN hN0




end StochCalcBr

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma G_le_F (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : M.G t ≤ M.F t := by
  rw [hM.filtG t, hM.filtF t]
  refine sup_le_sup_right (iSup₂_mono fun s _ => ?_) _
  have h : M.B s = Prod.fst ∘ (fun ω => (M.B s ω, M.Bt s ω)) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le

lemma η_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) : Continuous (fun t => M.η t ω) := by
  unfold Model.η
  exact (hM.μ_cont ω).div (hM.σ_cont ω) (fun t => (hM.σ_pos t ω).ne')

lemma η_meas (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    StronglyMeasurable[M.F s] (M.η s) := by
  have h1 := (hM.μ_adapted s).mono (G_le_F M hM s)
  have h2 := (hM.σ_adapted s).mono (G_le_F M hM s)
  exact h1.div h2







end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcD1b

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- Index set of the "past of coordinate `j`, everything of the others". -/
abbrev PastIdx (d : ℕ) (t₀ : ℝ≥0) (j : Fin d) : Type := {q : ℝ≥0 × Fin d // q.1 ≤ t₀ ∨ q.2 ≠ j}

theorem indep_coord_shift {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) (j : Fin d) :
    IndepFun (fun ω (r : ℝ≥0) => W (t₀ + r) ω j - W t₀ ω j)
      (fun ω (q : PastIdx d t₀ j) => W q.1.1 ω q.1.2) P := by
  have hG := stdBrownian_isGaussianProcess hW
  have hP : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (X := fun (r : ℝ≥0) ω => W (t₀ + r) ω j - W t₀ ω j)
    (Y := fun (q : PastIdx d t₀ j) ω => W q.1.1 ω q.1.2)
  · apply hG.of_isGaussianProcess
    rintro (r | ⟨⟨t, i⟩, hq⟩)
    · exact ⟨{(t₀ + r, j), (t₀, j)},
        { toFun x := x ⟨(t₀ + r, j), by simp⟩ - x ⟨(t₀, j), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(t, i)},
        { toFun x := x ⟨(t, i), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro r; exact ((hm (t₀ + r) j).sub (hm t₀ j)).aemeasurable
  · intro q; exact (hm _ _).aemeasurable
  · rintro r ⟨⟨t, i⟩, hq⟩
    simp only
    rw [covariance_fun_sub_left (stdBrownian_memLp_two hW _ _) (stdBrownian_memLp_two hW _ _)
      (stdBrownian_memLp_two hW _ _), stdBrownian_cov hW, stdBrownian_cov hW]
    by_cases hij : j = i
    · subst hij
      rcases hq with ht | hne
      · have ht' : t ≤ t₀ := ht
        simp only [if_true]
        rw [min_eq_right (ht'.trans (le_add_right le_rfl)), min_eq_right ht', sub_self]
      · exact absurd rfl hne
    · simp [hij]

/-- σ-algebra form: the increments of coordinate `j` after `t₀` are independent of the
a.e.-closure of the past-of-`j`/all-of-the-others σ-algebra. -/
theorem indep_coord_shift_aeClosure {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) (j : Fin d) :
    Indep (aeClosure P (MeasurableSpace.comap
        (fun ω (q : PastIdx d t₀ j) => W q.1.1 ω q.1.2) inferInstance))
      (MeasurableSpace.comap (fun ω (r : ℝ≥0) => W (t₀ + r) ω j - W t₀ ω j) inferInstance) P :=
  indep_aeClosure ((IndepFun_iff_Indep _ _ _).1 (indep_coord_shift hW t₀ j)).symm

end StochCalcIndep

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcHs

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}

lemma integrable_exp_mul (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * ξ ω)) P := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) c
  rw [← hξ.map_eq] at h
  exact (integrable_map_measure h.aestronglyMeasurable hm.aemeasurable).1 h









lemma integrable_exp_abs (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * |ξ ω|)) P := by
  refine Integrable.mono' ((integrable_exp_mul hm hξ c).add (integrable_exp_mul hm hξ (-c)))
    (by fun_prop) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 (ξ ω) with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-c * ξ ω)]
  · rw [abs_of_nonpos h]
    have : c * -ξ ω = -c * ξ ω := by ring
    rw [this]; linarith [Real.exp_pos (c * ξ ω)]


/-- The dominating function of the difference quotients. -/
noncomputable def G (ξ : Ω → ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  (|ξ ω| + v) * Real.exp (|ξ ω| + v)


lemma memLp_G (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    MemLp (G ξ v) 2 P := by
  have hmeas : Measurable (G ξ v) := by unfold G; fun_prop
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ?_
  have hint : Integrable (fun ω => 2 * Real.exp (3 * (v : ℝ)) * Real.exp (3 * |ξ ω|)) P :=
    (integrable_exp_abs hm hξ 3).const_mul _
  refine Integrable.mono' hint (by fun_prop) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  set y := |ξ ω| + (v : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hG : G ξ v ω ^ 2 = y ^ 2 * Real.exp (2 * y) := by
    rw [G, ← hy, mul_pow, sq (Real.exp y), ← Real.exp_add, two_mul]
  have he : 2 * Real.exp (3 * (v : ℝ)) * Real.exp (3 * |ξ ω|) = 2 * Real.exp (3 * y) := by
    rw [mul_assoc, ← Real.exp_add, hy]; ring_nf
  rw [hG, he]
  have h3 : Real.exp (3 * y) = Real.exp y * Real.exp (2 * y) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  have hpos := Real.exp_pos (2 * y)
  nlinarith [Real.exp_pos y]


lemma memLp_xi (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) : MemLp ξ 2 P := by
  refine (memLp_G hm hξ).mono hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have h1 : |ξ ω| ≤ |ξ ω| + v := le_add_of_nonneg_right v.2
  have h2 : 1 ≤ Real.exp (|ξ ω| + v) := Real.one_le_exp (by positivity)
  have h3 : 0 ≤ G ξ v ω := by unfold G; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3]
  unfold G
  have h4 : (0 : ℝ) ≤ |ξ ω| + v := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]


end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The tilted measure. -/
noncomputable abbrev Qd (P : Measure Ω) (D : Ω → ℝ) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (D ω)





lemma setIntegral_Qd {D : Ω → ℝ} (hm : Measurable D) (hpos : ∀ ω, 0 < D ω) (g : Ω → ℝ)
    {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, g ω ∂(Qd P D) = ∫ ω in A, D ω * g ω ∂P := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top) g hA]
  refine setIntegral_congr_fun hA fun ω _ => ?_
  rw [ENNReal.toReal_ofReal (hpos ω).le, smul_eq_mul]

lemma integrable_Qd_iff {D : Ω → ℝ} (hm : Measurable D) (hpos : ∀ ω, 0 < D ω) (g : Ω → ℝ) :
    Integrable g (Qd P D) ↔ Integrable (fun ω => D ω * g ω) P := by
  rw [integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun ω => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpos ω).le]





end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


/-- Its variance. -/
noncomputable def V (u w : ℝ≥0) : ℝ≥0 := nndist (w : ℝ) (u : ℝ)

















end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein







/-- Independence from `comap f` transfers along an a.e. equality of `f`. -/
lemma indep_comap_congr {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    {P : Measure Ω} (m : MeasurableSpace Ω) {f f' : Ω → β} (hf : f =ᵐ[P] f')
    (h : Indep m (MeasurableSpace.comap f' mβ) P) : Indep m (MeasurableSpace.comap f mβ) P := by
  rw [Indep_iff] at h ⊢
  rintro t1 _ ht1 ⟨S, hS, rfl⟩
  have e : (f ⁻¹' S : Set Ω) =ᵐ[P] f' ⁻¹' S := hf.fun_comp (fun y => y ∈ S)
  rw [measure_congr ((ae_eq_refl t1).inter e), measure_congr e]
  exact h t1 _ ht1 ⟨S, hS, rfl⟩

end StochCalcStein
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6




/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_gauss {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    ∫ ω, ξ ω ∂P = 0 := by
  rw [hξ.integral_eq, integral_id_gaussianReal]

lemma integral_sq_gauss {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    ∫ ω, ξ ω ^ 2 ∂P = v := by
  have h := hξ.integral_comp (f := fun x : ℝ => x ^ 2) (continuous_pow 2).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa [integral_id_gaussianReal] using hv


variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)



end StochCalcP6S

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]











end StochCalcHedgeDeg

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcD2

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6




end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)


end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcD3
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `B`-increment. -/
noncomputable def dB (M : Model p Ω) (u w : ℝ≥0) (ω : Ω) : ℝ := M.B w ω - M.B u ω



lemma dB_law (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    HasLaw (dB M u w) (gaussianReal 0 (V u w)) M.P :=
  hM.brownB.hasLaw_sub w u

lemma dB_meas (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) : Measurable (dB M u w) :=
  (B_measurable M hM w).sub (B_measurable M hM u)



end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Past of `B` up to `c`, all of `B~`. -/
noncomputable abbrev YsigB (M : Model p Ω) (c : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (q : PastIdx 2 c 0) => W M q.1.1 ω q.1.2) inferInstance

lemma coordB_meas (M : Model p Ω) (c : ℝ≥0) (q : PastIdx 2 c 0) :
    Measurable[YsigB M c] (fun ω => W M q.1.1 ω q.1.2) := fun S hS =>
  ⟨(fun f : PastIdx 2 c 0 → ℝ => f q) ⁻¹' S, measurable_pi_apply q hS, rfl⟩

lemma pair_aeC0 (M : Model p Ω) (hM : M.Standing) (c s : ℝ≥0) (hs : s ≤ c) :
    MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance ≤
      aeClosure M.P (YsigB M c) := by
  rintro A ⟨S, hS, rfl⟩
  have hq0 : (s, (0 : Fin 2)).1 ≤ c ∨ (s, (0 : Fin 2)).2 ≠ 0 := Or.inl hs
  have hq1 : (s, (1 : Fin 2)).1 ≤ c ∨ (s, (1 : Fin 2)).2 ≠ 0 :=
    Or.inr (show (1 : Fin 2) ≠ 0 by decide)
  have hm : Measurable[YsigB M c] (fun ω => (W M s ω 0, W M s ω 1)) :=
    (coordB_meas M c ⟨(s, 0), hq0⟩).prodMk (coordB_meas M c ⟨(s, 1), hq1⟩)
  refine ⟨(fun ω => (W M s ω 0, W M s ω 1)) ⁻¹' S, hm hS, ?_⟩
  filter_upwards [ae_W M hM] with ω hω
  show ((M.B s ω, M.Bt s ω) ∈ S) = ((W M s ω 0, W M s ω 1) ∈ S)
  rw [(hω s).1, (hω s).2]

lemma null_aeC0 (M : Model p Ω) (c : ℝ≥0) :
    MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ M.P N = 0} ≤
      aeClosure M.P (YsigB M c) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro N ⟨-, hN0⟩
  exact ⟨∅, @MeasurableSet.empty Ω (YsigB M c), ae_eq_empty.2 hN0⟩

lemma F_le0 (M : Model p Ω) (hM : M.Standing) (c : ℝ≥0) :
    M.F c ≤ aeClosure M.P (YsigB M c) := by
  rw [hM.filtF c]
  exact sup_le (iSup₂_le fun s hs => pair_aeC0 M hM c s hs) (null_aeC0 M c)

/-- The `B` increments after `c` are independent of `F_c`. -/
theorem indep_B_incr (M : Model p Ω) (hM : M.Standing) (c : ℝ≥0) :
    Indep (M.F c)
      (MeasurableSpace.comap (fun ω (r : ℝ≥0) => W M (c + r) ω 0 - W M c ω 0) inferInstance)
      M.P :=
  indep_of_indep_of_le_left (indep_coord_shift_aeClosure (isStandardBrownian M hM) c 0)
    (F_le0 M hM c)

lemma dB_ae (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    dB M u w =ᵐ[M.P] fun ω => gB M w ω - gB M u ω := by
  filter_upwards [ae_W M hM] with ω hω
  simp only [dB, ← (hω w).1, ← (hω u).1, W_zero]

lemma indep_dB (M : Model p Ω) (hM : M.Standing) {u w : ℝ≥0} (huw : u ≤ w) :
    Indep (M.F u) (MeasurableSpace.comap (dB M u w) inferInstance) M.P := by
  refine indep_comap_congr _ (dB_ae M hM u w) ?_
  refine indep_of_indep_of_le_right (indep_B_incr M hM u) ?_
  set inc : Ω → ℝ≥0 → ℝ := fun ω r => W M (u + r) ω 0 - W M u ω 0 with hinc
  have heq : (fun ω => gB M w ω - gB M u ω) = (fun f : ℝ≥0 → ℝ => f (w - u)) ∘ inc := by
    funext ω
    simp only [Function.comp, hinc, W_zero, add_tsub_cancel_of_le huw]
  rw [heq]
  exact ((measurable_pi_apply _).comp (comap_measurable inc)).comap_le

lemma B_measF (M : Model p Ω) (hM : M.Standing) {r s : ℝ≥0} (hr : r ≤ s) :
    Measurable[M.F s] (M.B r) := by
  have h : MeasurableSpace.comap (fun ω => (M.B r ω, M.Bt r ω)) inferInstance ≤ M.F s := by
    rw [hM.filtF s]
    exact le_sup_of_le_left (le_iSup₂_of_le r hr le_rfl)
  exact measurable_fst.comp (Measurable.of_comap_le h)

lemma B_measG (M : Model p Ω) (hM : M.Standing) {r s : ℝ≥0} (hr : r ≤ s) :
    Measurable[M.G s] (M.B r) := by
  have h : MeasurableSpace.comap (M.B r) inferInstance ≤ M.G s := by
    rw [hM.filtG s]
    exact le_sup_of_le_left (le_iSup₂_of_le r hr le_rfl)
  exact Measurable.of_comap_le h












end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Increment hypotheses on a real process `W` w.r.t. a family of σ-algebras `m`. -/
structure IncrHyp (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop where
  mono : Monotone m
  le : ∀ t, m t ≤ mΩ
  adapt : ∀ t, Measurable[m t] (W t)
  indep : ∀ u v, u ≤ v →
    Indep (m u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P
  mem2 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P
  mean : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0
  var : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u

variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma dW_meas (hW : IncrHyp m W P) {u v : ℝ≥0} (huv : u ≤ v) :
    Measurable[m v] (fun ω => W v ω - W u ω) :=
  (hW.adapt v).sub ((hW.adapt u).mono (hW.mono huv) le_rfl)

lemma dW_measAmb (hW : IncrHyp m W P) (u v : ℝ≥0) : Measurable (fun ω => W v ω - W u ω) :=
  ((hW.adapt v).mono (hW.le v) le_rfl).sub ((hW.adapt u).mono (hW.le u) le_rfl)

lemma int_mul_dW (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) : ∫ ω, g ω * (W d ω - W c ω) ∂P = 0 := by
  have hind : IndepFun g (fun ω => W d ω - W c ω) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    (dW_measAmb hW c d).aestronglyMeasurable, hW.mean c d hcd, mul_zero]

lemma int_mul_dW_sq (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) :
    ∫ ω, g ω * (W d ω - W c ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * ((d : ℝ) - c) := by
  have hind : IndepFun g (fun ω => (W d ω - W c ω) ^ 2) P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le) ?_
    exact ((comap_measurable (fun ω => W d ω - W c ω)).pow_const 2).comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    ((dW_measAmb hW c d).pow_const 2).aestronglyMeasurable, hW.var c d hcd]

lemma int_mul_dW_dW (hW : IncrHyp m W P) {c x y : ℝ≥0} (hcx : c ≤ x) (hxy : x ≤ y) {g : Ω → ℝ}
    (hg : Measurable[m c] g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * ((W x ω - W c ω) * (W y ω - W c ω)) ∂P = (∫ ω, g ω ∂P) * ((x : ℝ) - c) := by
  have hga : AEStronglyMeasurable g P := (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
  have hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have i1 : Integrable (fun ω => g ω * (W x ω - W c ω) ^ 2) P :=
    (hW.mem2 c x).integrable_sq.bdd_mul hga hgb
  have i2 : Integrable (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W x ω))) P :=
    ((hW.mem2 c x).integrable_mul (hW.mem2 x y)).bdd_mul hga hgb
  have i2' : Integrable (fun ω => g ω * (W x ω - W c ω) * (W y ω - W x ω)) P := by
    simpa only [mul_assoc] using i2
  have e : (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W c ω))) =
      fun ω => g ω * (W x ω - W c ω) ^ 2 + g ω * (W x ω - W c ω) * (W y ω - W x ω) := by
    funext ω; ring
  have hg2 : Measurable[m x] (fun ω => g ω * (W x ω - W c ω)) :=
    (hg.mono (hW.mono hcx) le_rfl).mul (dW_meas hW hcx)
  rw [e, integral_add i1 i2', int_mul_dW_sq hW hcx hg, int_mul_dW hW hxy hg2, add_zero]

/-- Overlap length of `[u,v)` and `[u',v')`. -/
noncomputable def ov (u v u' v' : ℝ≥0) : ℝ := max (min (v : ℝ) v' - max (u : ℝ) u') 0

lemma ov_comm (u v u' v' : ℝ≥0) : ov u v u' v' = ov u' v' u v := by
  unfold ov; rw [min_comm, max_comm (u : ℝ)]

/-- Covariance of two elementary increments (case `u ≤ u'`). -/
lemma cov_le (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    (huu' : u ≤ u') {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  have hYu' : Measurable[m u'] Y := hY.mono (hW.mono huu') le_rfl
  have hYY' : Measurable[m u'] (fun ω => Y ω * Y' ω) := hYu'.mul hY'
  have hbd : ∀ ω, |Y ω * Y' ω| ≤ C * C' := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
  have hu'r : (u : ℝ) ≤ u' := by exact_mod_cast huu'
  rcases le_or_gt v u' with hvu | hu'v
  · have hvu' : (v : ℝ) ≤ u' := by exact_mod_cast hvu
    have hov : ov u v u' v' = 0 := by
      unfold ov
      exact max_eq_right (by linarith [min_le_left (v : ℝ) v', le_max_right (u : ℝ) u'])
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y ω * (W v ω - W u ω) * Y' ω) * (W v' ω - W u' ω) := by
      funext ω; ring
    have hg : Measurable[m u'] (fun ω => Y ω * (W v ω - W u ω) * Y' ω) :=
      (hYu'.mul ((dW_meas hW huv).mono (hW.mono hvu) le_rfl)).mul hY'
    rw [e, int_mul_dW hW hu'v' hg, hov, mul_zero]
  · have hu'v'' : (u' : ℝ) < v := by exact_mod_cast hu'v
    have hu'v1 : u' ≤ v := hu'v.le
    have hga : AEStronglyMeasurable (fun ω => Y ω * Y' ω) P :=
      (hYY'.mono (hW.le u') le_rfl).aestronglyMeasurable
    have hgb : ∀ᵐ ω ∂P, ‖Y ω * Y' ω‖ ≤ C * C' :=
      Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd ω
    have i1 : Integrable (fun ω => Y ω * Y' ω * ((W u' ω - W u ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u u').integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i2 : Integrable (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u' v).integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i1' : Integrable (fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω)) P := by
      simpa only [mul_assoc] using i1
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω) +
          Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω)) := by
      funext ω; ring
    have hg1 : Measurable[m u'] (fun ω => Y ω * Y' ω * (W u' ω - W u ω)) :=
      hYY'.mul (dW_meas hW huu')
    rw [e, integral_add i1' i2, int_mul_dW hW hu'v' hg1, zero_add]
    rcases le_total v v' with hvv | hvv
    · rw [int_mul_dW_dW hW hu'v1 hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v : ℝ) ≤ v' := by exact_mod_cast hvv
      rw [min_eq_left hvv', max_eq_right hu'r, max_eq_left (by linarith)]
    · have e2 : (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) =
          fun ω => Y ω * Y' ω * ((W v' ω - W u' ω) * (W v ω - W u' ω)) := by
        funext ω; ring
      rw [e2, int_mul_dW_dW hW hu'v' hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v' : ℝ) ≤ v := by exact_mod_cast hvv
      have hu'v'r : (u' : ℝ) ≤ v' := by exact_mod_cast hu'v'
      rw [min_eq_right hvv', max_eq_right hu'r, max_eq_left (by linarith)]

lemma cov (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  rcases le_total u u' with h | h
  · exact cov_le hW huv hu'v' h hY hY' hC hC'
  · have := cov_le hW hu'v' huv h hY' hY hC' hC
    have e1 : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y' ω * (W v' ω - W u' ω)) * (Y ω * (W v ω - W u ω)) := by
      funext ω; ring
    have e2 : (fun ω => Y ω * Y' ω) = fun ω => Y' ω * Y ω := by funext ω; ring
    rw [e1, e2, this, ov_comm]

/-- Time indicator of `[u, v)`. -/
noncomputable def ind (u v : ℝ≥0) (r : ℝ) : ℝ := (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) r

lemma ind_mul (u v u' v' : ℝ≥0) (r : ℝ) :
    ind u v r * ind u' v' r =
      (Set.Ico (max (u : ℝ) u') (min (v : ℝ) v')).indicator (fun _ => (1 : ℝ)) r := by
  simp only [ind, Set.indicator_apply, Set.mem_Ico, max_le_iff, lt_min_iff]
  split_ifs <;> simp_all

lemma ind_abs_le (u v : ℝ≥0) (r : ℝ) : |ind u v r| ≤ 1 := by
  unfold ind; rw [Set.indicator_apply]; split_ifs <;> simp

lemma ind_meas (u v : ℝ≥0) : Measurable (ind u v) :=
  (measurable_const.indicator measurableSet_Ico)

/-- The time-space measure `dt|[0,T) ⊗ P`. -/
noncomputable def μT (P : Measure Ω) (T : ℝ≥0) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Ico (0 : ℝ) T)).prod P

instance (T : ℝ≥0) : IsFiniteMeasure (μT P T) := by unfold μT; infer_instance

lemma int_time (T : ℝ≥0) {u v u' v' : ℝ≥0} (hvT : v ≤ T) :
    ∫ r, ind u v r * ind u' v' r ∂(volume.restrict (Set.Ico (0 : ℝ) T)) = ov u v u' v' := by
  unfold ov
  simp_rw [ind_mul]
  have hsub : Set.Ico (max (u : ℝ) u') (min (v : ℝ) v') ⊆ Set.Ico 0 T := fun r hr =>
    ⟨le_trans (le_trans (NNReal.coe_nonneg u) (le_max_left _ _)) hr.1,
      lt_of_lt_of_le hr.2 (le_trans (min_le_left _ _) (by exact_mod_cast hvT))⟩
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 hsub, Real.volume_real_Ico, smul_eq_mul, mul_one]

/-- Elementary adapted processes `Y 1_[u,v)` on `[0,T]`. -/
structure Elem (m : ℝ≥0 → MeasurableSpace Ω) (T : ℝ≥0) where
  u : ℝ≥0
  v : ℝ≥0
  huv : u ≤ v
  hvT : v ≤ T
  Y : Ω → ℝ
  hY : Measurable[m u] Y
  C : ℝ
  hC : ∀ ω, |Y ω| ≤ C

/-- The time-space function of an elementary process. -/
noncomputable def efun {T : ℝ≥0} (i : Elem m T) (z : ℝ × Ω) : ℝ := ind i.u i.v z.1 * i.Y z.2

/-- The elementary stochastic integral. -/
noncomputable def ifun {T : ℝ≥0} (W : ℝ≥0 → Ω → ℝ) (i : Elem m T) (ω : Ω) : ℝ :=
  i.Y ω * (W i.v ω - W i.u ω)

lemma memLp_efun (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i : Elem m T) :
    MemLp (efun i) 2 (μT P T) := by
  have hm : Measurable (efun i) :=
    ((ind_meas i.u i.v).comp measurable_fst).mul ((i.hY.mono (hle i.u) le_rfl).comp measurable_snd)
  refine MemLp.of_bound hm.aestronglyMeasurable i.C (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, efun, abs_mul]
  calc |ind i.u i.v z.1| * |i.Y z.2| ≤ 1 * |i.Y z.2| :=
        mul_le_mul_of_nonneg_right (ind_abs_le _ _ _) (abs_nonneg _)
    _ ≤ i.C := by rw [one_mul]; exact i.hC z.2

lemma memLp_ifun (hW : IncrHyp m W P) {T : ℝ≥0} (i : Elem m T) : MemLp (ifun W i) 2 P := by
  refine ((hW.mem2 i.u i.v).const_mul i.C).of_le
    ((i.hY.mono (hW.le i.u) le_rfl).aestronglyMeasurable.mul (hW.mem2 i.u i.v).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [ifun, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((i.hC ω).trans (le_abs_self _)) (abs_nonneg _)

noncomputable def eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 (μT P T) :=
  (memLp_efun (P := P) hle i).toLp _

noncomputable def eI (hW : IncrHyp m W P) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 P :=
  (memLp_ifun hW i).toLp _

lemma inner_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eE (P := P) hle T i, eE hle T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eE
  rw [L2.inner_def]
  have h1 := (memLp_efun (P := P) hle i).coeFn_toLp
  have h2 := (memLp_efun (P := P) hle j).coeFn_toLp
  have hc : ∫ z, ⟪((memLp_efun (P := P) hle i).toLp _ : ℝ × Ω → ℝ) z,
      ((memLp_efun (P := P) hle j).toLp _ : ℝ × Ω → ℝ) z⟫_ℝ ∂(μT P T) =
      ∫ z, (ind i.u i.v z.1 * ind j.u j.v z.1) * (i.Y z.2 * j.Y z.2) ∂(μT P T) := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, efun, efun]
    ring
  rw [hc, μT, integral_prod_mul (fun r => ind i.u i.v r * ind j.u j.v r)
    (fun ω => i.Y ω * j.Y ω), int_time T i.hvT]

lemma inner_eI (hW : IncrHyp m W P) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eI hW T i, eI hW T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eI
  rw [L2.inner_def]
  have h1 := (memLp_ifun hW i).coeFn_toLp
  have h2 := (memLp_ifun hW j).coeFn_toLp
  have hc : ∫ ω, ⟪((memLp_ifun hW i).toLp _ : Ω → ℝ) ω, ((memLp_ifun hW j).toLp _ : Ω → ℝ) ω⟫_ℝ ∂P =
      ∫ ω, (i.Y ω * (W i.v ω - W i.u ω)) * (j.Y ω * (W j.v ω - W j.u ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, ifun, ifun]
  rw [hc, cov hW i.huv j.huv i.hY j.hY i.hC j.hC, mul_comm]

noncomputable def eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (μT P T) :=
  Finsupp.linearCombination ℝ (eE hle T)

noncomputable def TL (hW : IncrHyp m W P) (T : ℝ≥0) : (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (eI hW T)

lemma inner_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s t : Elem m T →₀ ℝ) :
    ⟪TL hW T s, TL hW T t⟫_ℝ = ⟪eL (P := P) hW.le T s, eL hW.le T t⟫_ℝ := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s1 s2 h1 h2 => simp only [map_add, inner_add_left, h1, h2]
  | single i a =>
    induction t using Finsupp.induction_linear with
    | zero => simp
    | add t1 t2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single j b =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_left,
        real_inner_smul_right, inner_eI, inner_eE]

lemma norm_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    ‖TL hW T s‖ = ‖eL (P := P) hW.le T s‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_TL]



end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma V_eq {u w : ℝ≥0} (huw : u ≤ w) : ((V u w : ℝ≥0) : ℝ) = (w : ℝ) - u := by
  rw [V, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast huw))]

theorem incr_B (M : Model p Ω) (hM : M.Standing) : IncrHyp M.F M.B M.P := by
  have := hM.prob
  exact
  { mono := fun _ _ h => M.F.mono h
    le := M.F.le
    adapt := fun t => B_measF M hM le_rfl
    indep := fun u v huv => indep_dB M hM huv
    mem2 := fun u v => memLp_xi (dB_meas M hM u v) (dB_law M hM u v)
    mean := fun u v _ => integral_gauss (dB_law M hM u v)
    var := fun u v huv => by
      have h := integral_sq_gauss (dB_law M hM u v)
      rw [V_eq huv] at h
      exact h }



end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




lemma coe_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (eL (P := P) hle T s : ℝ × Ω → ℝ) =ᵐ[μT P T] fun z => s.sum (fun i c => c * efun i z) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μT P T)] with z h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (eL (P := P) hle T s1) (eL hle T s2), h1, h2] with z h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [eL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eE (P := P) hle T i),
      (memLp_efun (P := P) hle i).coeFn_toLp] with z h h'
    rw [h, Pi.smul_apply, eE, h', smul_eq_mul]

end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/

lemma clamp_sub_le {D x y : ℝ} (hy : |y| ≤ D) : |max (-D) (min D x) - y| ≤ |x - y| := by
  have hy' := abs_le.1 hy
  rcases le_total x D with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-D) x with h2 | h2
    · exact le_of_eq (by rw [max_eq_right h2])
    · rw [max_eq_left h2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

lemma clamp_abs_le {D x : ℝ} (hD : 0 ≤ D) : |max (-D) (min D x)| ≤ D :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma cell_uniq {T : ℝ≥0} {n j k : ℕ} {u : ℝ}
    (hj : (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n)
    (hk : (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n) :
    j = k := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hT : (0 : ℝ) ≤ T.val := T.2
  have e1 : (j : ℝ) * T.val < ((k : ℝ) + 1) * T.val :=
    (div_lt_div_iff_of_pos_right h2).1 (lt_of_lt_of_le hj.1 hk.2)
  have e2 : (k : ℝ) * T.val < ((j : ℝ) + 1) * T.val :=
    (div_lt_div_iff_of_pos_right h2).1 (lt_of_lt_of_le hk.1 hj.2)
  have f1 : (j : ℝ) < (k : ℝ) + 1 := lt_of_mul_lt_mul_right e1 hT
  have f2 : (k : ℝ) < (j : ℝ) + 1 := lt_of_mul_lt_mul_right e2 hT
  have g1 : j < k + 1 := by exact_mod_cast f1
  have g2 : k < j + 1 := by exact_mod_cast f2
  omega

lemma stepValue_comp (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) (g : ℝ → ℝ) (hg : g 0 = 0) (u : ℝ)
    (ω : Ω) :
    itoStepValue T n (fun k ω => g (e k ω)) u ω = g (itoStepValue T n e u ω) := by
  unfold itoStepValue
  by_cases h : ∃ k ∈ Finset.range (2 ^ n), (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
      u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n
  · obtain ⟨k, hk, hc⟩ := h
    have key : ∀ v : ℕ → ℝ, ∑ j ∈ Finset.range (2 ^ n), (if (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
        u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n then v j else 0) = v k := by
      intro v
      rw [Finset.sum_eq_single_of_mem k hk
        (fun j _ hjk => if_neg (fun hcj => hjk (cell_uniq hcj hc))), if_pos hc]
    exact (key (fun j => g (e j ω))).trans (congrArg g (key (fun j => e j ω))).symm
  · have z : ∀ v : ℕ → ℝ, ∑ j ∈ Finset.range (2 ^ n), (if (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
        u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n then v j else 0) = 0 :=
      fun v => Finset.sum_eq_zero (fun j hj => if_neg (fun hc => h ⟨j, hj, hc⟩))
    exact (z (fun j => g (e j ω))).trans (hg.symm.trans (congrArg g (z (fun j => e j ω))).symm)

lemma stepValue_meas (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) (ω : Ω) :
    Measurable (fun u => itoStepValue T n e u ω) := by
  have : (fun u => itoStepValue T n e u ω) = fun u => ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * T.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n)).indicator
        (fun _ => e k ω) u := funext fun u => itoStepValue_eq_sum_indicator T n e u ω
  rw [this]
  exact Finset.measurable_sum _ fun k _ => measurable_const.indicator measurableSet_Ioc

lemma err_intervalIntegrable (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) {H : ℝ≥0 → Ω → ℝ} {D : ℝ}
    (hD : ∀ u ω, |H u ω| ≤ D) (hHm : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω)) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue T n e u ω - H u.toNNReal ω) ^ 2) volume 0 T.val := by
  have h1 := itoStepValue_sq_intervalIntegrable T n e ω
  have hc : IntervalIntegrable (fun _ : ℝ => 2 * D ^ 2) volume 0 T.val := intervalIntegrable_const
  refine ((h1.const_mul 2).add hc).mono_fun
    (((stepValue_meas T n e ω).sub (hHm ω)).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD u.toNNReal ω)
  have hH2 : H u.toNNReal ω ^ 2 ≤ D ^ 2 :=
    sq_le_sq.2 (by rw [abs_of_nonneg hD0]; exact hD _ _)
  have hx := sq_nonneg (itoStepValue T n e u ω + H u.toNNReal ω)
  have hs := sq_nonneg (itoStepValue T n e u ω)
  have hid : 2 * itoStepValue T n e u ω ^ 2 + 2 * H u.toNNReal ω ^ 2 -
      (itoStepValue T n e u ω - H u.toNNReal ω) ^ 2 =
      (itoStepValue T n e u ω + H u.toNNReal ω) ^ 2 := by ring
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
  linarith

/-- Bounded nonnegative functions tending to zero in measure have integrals tending to zero. -/
lemma integral_tendsto_zero_of_bdd {F : ℕ → Ω → ℝ} {K : ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) P) (hF0 : ∀ n ω, 0 ≤ F n ω) (hFK : ∀ n ω, F n ω ≤ K)
    (h : TendstoInMeasure P F atTop (fun _ => 0)) :
    Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K' := max K 1 with hK'
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hδ : 0 < ε / 2 := by linarith
  have hm := (tendstoInMeasure_iff_dist.1 h) (ε / 2) hδ
  have hev : ∀ᶠ n in atTop, P {ω | ε / 2 ≤ dist (F n ω) 0} < ENNReal.ofReal (ε / (2 * K')) :=
    (tendsto_order.1 hm).2 _ (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  set S := {ω | ε / 2 ≤ dist (F n ω) 0} with hS
  set S' := toMeasurable P S with hS'
  have hS'm : MeasurableSet S' := measurableSet_toMeasurable P S
  have hPS' : P S' < ENNReal.ofReal (ε / (2 * K')) := by
    rw [hS', measure_toMeasurable]; exact hN n hn
  have hreal : P.real S' < ε / (2 * K') := ENNReal.toReal_lt_of_lt_ofReal hPS'
  have hint : Integrable (F n) P :=
    memLp_one_iff_integrable.1 (MemLp.of_bound (hFm n) K' (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n ω)]
      exact (hFK n ω).trans (le_max_left _ _)))
  have hg : Integrable (fun ω => ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hS'm |>.const_mul K')
  have hle : ∫ ω, F n ω ∂P ≤ ∫ ω, (ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P := by
    refine integral_mono hint hg (fun ω => ?_)
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω, mul_one]
      have := (hFK n ω).trans (le_max_left K 1)
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hωS : ω ∉ S := fun h => hω (subset_toMeasurable P S h)
      simp only [hS, Set.mem_setOf_eq, not_le, Real.dist_eq, sub_zero] at hωS
      rw [abs_of_nonneg (hF0 n ω)] at hωS
      exact hωS.le
  have hval : ∫ ω, (ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P = ε / 2 + K' * P.real S' := by
    rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator hS'm |>.const_mul K'),
      integral_const, integral_const_mul, integral_indicator_const (1 : ℝ) hS'm]
    simp
  have hK'r : K' * P.real S' < ε / 2 := by
    have := mul_lt_mul_of_pos_left hreal hK'pos
    rw [show K' * (ε / (2 * K')) = ε / 2 by field_simp] at this
    exact this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (hF0 n))]
  linarith

/-! The clamped approximants as elementary combinations. -/

/-- Clamped coefficients. -/
noncomputable def clampSeq (D : ℝ) (a0 : ℕ → ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  max (-D) (min D (a0 n k ω))




lemma grid_le (T : ℝ≥0) (n k : ℕ) :
    (k : ℝ≥0) * T / (2 : ℝ≥0) ^ n ≤ ((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right le_self_add (by positivity)) (by positivity)

lemma grid_top (T : ℝ≥0) (n k : ℕ) (hk : k < 2 ^ n) :
    ((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n ≤ T := by
  have hk1 : (k : ℝ≥0) + 1 ≤ (2 : ℝ≥0) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk
  rw [div_le_iff₀ (by positivity), mul_comm T]
  exact mul_le_mul_of_nonneg_right hk1 (by positivity)

/-- The grid elementary process `Y 1_[k T/2^n, (k+1) T/2^n)`. -/
noncomputable def gElem (T : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n)) (Y : Ω → ℝ)
    (hY : Measurable[m (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] Y) (C : ℝ)
    (hC : ∀ ω, |Y ω| ≤ C) : Elem m T where
  u := ((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n
  v := (((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n
  huv := grid_le T n k
  hvT := grid_top T n k k.2
  Y := Y
  hY := hY
  C := C
  hC := hC

lemma sum_single_comb {ι : Type*} [Fintype ι] {T : ℝ≥0} (e : ι → Elem m T)
    (g : Elem m T → ℝ → ℝ) (hg0 : ∀ i, g i 0 = 0)
    (hgadd : ∀ i b1 b2, g i (b1 + b2) = g i b1 + g i b2) :
    (∑ k, Finsupp.single (e k) (1 : ℝ)).sum g = ∑ k, g (e k) 1 := by
  rw [← Finsupp.sum_finsetSum_index hg0 hgadd]
  exact Finset.sum_congr rfl fun k _ => Finsupp.sum_single_index (hg0 _)

/-- The left-closed grid step function agrees with `itoStepValue` off the finite grid. -/
lemma ind_grid_eq (T : ℝ≥0) (n k : ℕ) {u : ℝ}
    (hu1 : u ≠ (k : ℝ) * T.val / (2 : ℝ) ^ n) (hu2 : u ≠ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n)
    (y : ℝ) :
    ind ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) (((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) u * y =
      if (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n
        then y else 0 := by
  unfold ind
  simp only [Set.indicator_apply, Set.mem_Ico, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
  have e1 : ((k : ℝ) * (T : ℝ) / 2 ^ n ≤ u ∧ u < ((k : ℝ) + 1) * (T : ℝ) / 2 ^ n) ↔
      ((k : ℝ) * T.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hu1), h2.le⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, lt_of_le_of_ne h2 hu2⟩
  by_cases hc : (k : ℝ) * T.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n
  · rw [if_pos (e1.2 hc), if_pos hc, one_mul]
  · rw [if_neg (fun h => hc (e1.1 h)), if_neg hc, zero_mul]


end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

theorem pred_approx (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (a0 : ℕ → ℕ → Ω → ℝ)
    (ha0m : ∀ n k : ℕ, k < 2 ^ n → Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (a0 n k))
    (ha0H : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2) atTop (fun _ => (0 : ℝ))) :
    ∃ s : ℕ → (Elem m T →₀ ℝ), Tendsto (fun n => eLpNorm (fun z =>
        (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2 (μT P T)) atTop (𝓝 0) := by
  have hT0 : (0 : ℝ) ≤ T.val := T.2
  have hHm' : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω) :=
    fun ω => hHm.comp (measurable_id.prodMk measurable_const)
  have hcm : ∀ n k : ℕ, k < 2 ^ n →
      Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (clampSeq D a0 n k) :=
    fun n k hk => measurable_const.max (measurable_const.min (ha0m n k hk))
  have hcb : ∀ n k ω, |clampSeq D a0 n k ω| ≤ D := fun n k ω => clamp_abs_le hD0
  have hg0 : max (-D) (min D 0) = 0 := by
    rw [min_eq_right hD0, max_eq_right (neg_nonpos.2 hD0)]
  have hsvc : ∀ n u ω, itoStepValue T n (clampSeq D a0 n) u ω =
      max (-D) (min D (itoStepValue T n (a0 n) u ω)) :=
    fun n u ω => stepValue_comp T n (a0 n) (fun x => max (-D) (min D x)) hg0 u ω
  have herr : ∀ n u ω, (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 ≤
      (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 := fun n u ω => by
    rw [hsvc]; exact sq_le_sq.2 (clamp_sub_le (hD _ _))
  have hEc0 : ∀ n ω, 0 ≤ ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_nonneg hT0 (fun u _ => sq_nonneg _)
  have hEa0 : ∀ n ω, 0 ≤ ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_nonneg hT0 (fun u _ => sq_nonneg _)
  have hEcle : ∀ n ω, (∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ≤
      ∫ u in (0 : ℝ)..T.val, (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_mono_on hT0
      (err_intervalIntegrable T n _ hD hHm' ω) (err_intervalIntegrable T n _ hD hHm' ω)
      (fun u _ => herr n u ω)
  have hEc : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) atTop
      (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_zero_of_abs_le (K := 1) one_pos ha0H ha0H (fun n ω => ?_)
    rw [abs_of_nonneg (hEc0 n ω), abs_of_nonneg (hEa0 n ω)]
    linarith [hEcle n ω, hEa0 n ω]
  -- the elementary combinations
  let e : (n : ℕ) → Fin (2 ^ n) → Elem m T := fun n k =>
    gElem T n k (clampSeq D a0 n k) (hcm n k k.2) D (hcb n k)
  let s : ℕ → (Elem m T →₀ ℝ) := fun n => ∑ k, Finsupp.single (e n k) (1 : ℝ)
  have hsE : ∀ n (z : ℝ × Ω), (s n).sum (fun i c => c * efun i z) = ∑ k : Fin (2 ^ n),
      ind (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ((((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) z.1 *
        clampSeq D a0 n k z.2 := by
    intro n z
    show (∑ k, Finsupp.single (e n k) (1 : ℝ)).sum _ = _
    rw [sum_single_comb (e n) (fun i c => c * efun i z) (fun i => zero_mul _)
      (fun i b1 b2 => add_mul _ _ _)]
    simp only [one_mul, efun, e, gElem]
  have hoff : ∀ n (u : ℝ) (ω : Ω),
      u ∉ (fun j : ℕ => (j : ℝ) * T.val / (2 : ℝ) ^ n) '' Set.Iic (2 ^ n) →
      ∑ k : Fin (2 ^ n), ind (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n)
        ((((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) u * clampSeq D a0 n k ω =
      itoStepValue T n (clampSeq D a0 n) u ω := by
    intro n u ω hu
    unfold itoStepValue
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine ind_grid_eq T n k (fun h => hu ⟨k, Set.mem_Iic.2 (le_of_lt k.2), h.symm⟩)
      (fun h => hu ⟨(k : ℕ) + 1, Set.mem_Iic.2 (Nat.succ_le_of_lt k.2), by rw [h]; norm_num⟩) _
  have hGnull : ∀ n, volume ((fun j : ℕ => (j : ℝ) * T.val / (2 : ℝ) ^ n) '' Set.Iic (2 ^ n)) = 0 :=
    fun n => ((Set.finite_Iic _).image _).countable.measure_zero volume
  -- `L²(μT)` convergence
  have hψ2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T) :=
    MemLp.of_bound hHm.aestronglyMeasurable D (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hD _ _)
  have hgL : ∀ n, MemLp (fun z => (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2
      (μT P T) := fun n =>
    ((Lp.memLp (eL (P := P) hle T (s n))).ae_eq (coe_eL (P := P) hle T (s n))).sub hψ2
  have hinner : ∀ n ω, ∫ u, ((s n).sum (fun i c => c * efun i (u, ω)) - H (u, ω).1.toNNReal
      (u, ω).2) ^ 2 ∂(volume.restrict (Set.Ico (0 : ℝ) T)) = ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 := by
    intro n ω
    rw [intervalIntegral.integral_of_le hT0, ← integral_Ico_eq_integral_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hGnull n))] with u hu
    rw [hsE]
    dsimp only
    rw [hoff n u ω hu]
  have hfub : ∀ n, ∫ z, ((s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) ^ 2 ∂(μT P T) =
      ∫ ω, (∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ∂P := by
    intro n
    rw [show μT P T = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P from rfl,
      integral_prod_symm _ (hgL n).integrable_sq]
    exact integral_congr_ae (Eventually.of_forall fun ω => hinner n ω)
  have hEm : ∀ n, AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) P := by
    intro n
    have hi := (hgL n).integrable_sq.integral_prod_right
    exact hi.aestronglyMeasurable.congr (Eventually.of_forall fun ω => hinner n ω)
  have hEK : ∀ n ω, (∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ≤ T.val * (2 * D) ^ 2 := by
    intro n ω
    calc (∫ u in (0 : ℝ)..T.val,
          (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2)
        ≤ ∫ u in (0 : ℝ)..T.val, (2 * D) ^ 2 := by
          refine intervalIntegral.integral_mono_on hT0 (err_intervalIntegrable T n _ hD hHm' ω)
            intervalIntegrable_const (fun u _ => ?_)
          have h1 : |itoStepValue T n (clampSeq D a0 n) u ω| ≤ D := by
            rw [hsvc]; exact clamp_abs_le hD0
          have h2 := hD u.toNNReal ω
          have h3 := abs_sub (itoStepValue T n (clampSeq D a0 n) u ω) (H u.toNNReal ω)
          exact sq_le_sq.2 (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * D)]; linarith)
      _ = T.val * (2 * D) ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hI : Tendsto (fun n => ∫ z, ((s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) ^ 2
      ∂(μT P T)) atTop (𝓝 0) := by
    simp only [hfub]
    exact integral_tendsto_zero_of_bdd hEm hEc0 hEK hEc
  have hψ : Tendsto (fun n => eLpNorm (fun z => (s n).sum (fun i c => c * efun i z) -
      H z.1.toNNReal z.2) 2 (μT P T)) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm (fun z => (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2
        (μT P T) = ENNReal.ofReal ((∫ z, ((s n).sum (fun i c => c * efun i z) -
          H z.1.toNNReal z.2) ^ 2 ∂(μT P T)) ^ (2 : ℝ)⁻¹) := by
      intro n
      rw [(hgL n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    simp only [e]
    have h0 : ENNReal.ofReal ((0 : ℝ) ^ (2 : ℝ)⁻¹) = 0 := by
      rw [Real.zero_rpow (by norm_num)]; simp
    rw [← h0]
    exact ENNReal.tendsto_ofReal
      ((Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))).tendsto.comp hI)
  exact ⟨s, hψ⟩

/-- `pred_approx` as closure membership in `Lp ℝ 2 μT`. -/
theorem pred_mem (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hψ2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T))
    (a0 : ℕ → ℕ → Ω → ℝ)
    (ha0m : ∀ n k : ℕ, k < 2 ^ n → Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (a0 n k))
    (ha0H : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2) atTop (fun _ => (0 : ℝ))) :
    hψ2.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  obtain ⟨s, hψ⟩ := pred_approx (P := P) hle T hD0 hD hHm a0 ha0m ha0H
  have hψL : Tendsto (fun n => eL (P := P) hle T (s n)) atTop (𝓝 (hψ2.toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hψ.congr' (Eventually.of_forall fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [coe_eL (P := P) hle T (s n), hψ2.coeFn_toLp] with z e1 e2
    simp only [Pi.sub_apply, e1, e2]
  exact mem_closure_of_tendsto hψL (Eventually.of_forall fun n => ⟨s n, rfl⟩)

end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

/-- The left-point dyadic sampling of `H`. -/
noncomputable def lpt (T : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  H ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ω

lemma stepValue_lpt_tendsto (T : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (ω : Ω) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 T.val)
    (hlc : Tendsto (fun v : ℝ => H v.toNNReal ω) (𝓝[<] u) (𝓝 (H u.toNNReal ω))) :
    Tendsto (fun n => itoStepValue T n (lpt T H n) u ω) atTop (𝓝 (H u.toNNReal ω)) := by
  have hc : ∀ n : ℕ, ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * T.val / 2 ^ n < u ∧
      u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n ∧ itoStepValue T n (lpt T H n) u ω = lpt T H n k ω :=
    fun n => itoStepValue_eq_cell T n (lpt T H n) hu ω
  choose k _ hlo hhi hval using hc
  let w : ℕ → ℝ := fun n => (((k n : ℝ≥0) * T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)
  have hw : ∀ n, w n = (k n : ℝ) * T.val / 2 ^ n := fun n => by
    show (((k n : ℝ≥0) * T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) = _
    push_cast; rw [NNReal.val_eq_coe]
  have hval' : ∀ n, itoStepValue T n (lpt T H n) u ω = H (w n).toNNReal ω := fun n => by
    rw [hval n]; simp only [lpt, w, Real.toNNReal_coe]
  have hε : Tendsto (fun n : ℕ => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hlow : ∀ n, u - T.val / (2 : ℝ) ^ n ≤ w n := fun n => by
    rw [hw]
    have e : ((k n : ℝ) + 1) * T.val / 2 ^ n = (k n : ℝ) * T.val / 2 ^ n + T.val / 2 ^ n := by
      ring
    linarith [hhi n]
  have hwt : Tendsto w atTop (𝓝 u) := by
    have h1 : Tendsto (fun n : ℕ => u - T.val / (2 : ℝ) ^ n) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow (fun n => ?_)
    rw [hw]; exact (hlo n).le
  have hwl : Tendsto w atTop (𝓝[<] u) :=
    tendsto_nhdsWithin_iff.2 ⟨hwt, Eventually.of_forall fun n => by
      show w n < u
      rw [hw]; exact hlo n⟩
  rw [show (fun n => itoStepValue T n (lpt T H n) u ω) = fun n => H (w n).toNNReal ω from
    funext hval']
  exact hlc.comp hwl

theorem pred_left (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hHa : ∀ t, Measurable[m t] (H t))
    (hlc : ∀ ω, ∀ᵐ u ∂volume, u ∈ Set.Ioc 0 T.val →
      Tendsto (fun v : ℝ => H v.toNNReal ω) (𝓝[<] u) (𝓝 (H u.toNNReal ω)))
    (hψ2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T)) :
    hψ2.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  have hT0 : (0 : ℝ) ≤ T.val := T.2
  refine pred_mem (P := P) hle T hD0 hD hHm hψ2 (lpt T H) (fun n k _ => hHa _) ?_
  have hHm' : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω) :=
    fun ω => hHm.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ ω, Tendsto (fun n => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (lpt T H n) u ω - H u.toNNReal ω) ^ 2) atTop (𝓝 0) := by
    intro ω
    rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _ in (0 : ℝ)..T.val, (0 : ℝ)) by
      rw [intervalIntegral.integral_zero]]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * D) ^ 2) (Eventually.of_forall fun n => ?_)
      (Eventually.of_forall fun n => ?_) intervalIntegrable_const ?_
    · exact (intervalIntegrable_iff.1
        (err_intervalIntegrable T n (lpt T H n) hD hHm' ω)).aestronglyMeasurable
    · refine Eventually.of_forall fun u hu => ?_
      rw [Set.uIoc_of_le hT0] at hu
      obtain ⟨k, -, -, -, hval⟩ := itoStepValue_eq_cell T n (lpt T H n) hu ω
      rw [hval, Real.norm_eq_abs, abs_pow]
      have h1 := hD ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ω
      have h2 := hD u.toNNReal ω
      have h3 := abs_sub (lpt T H n k ω) (H u.toNNReal ω)
      have h4 : |lpt T H n k ω - H u.toNNReal ω| ≤ 2 * D := by
        simp only [lpt] at h3 ⊢; linarith
      exact pow_le_pow_left₀ (abs_nonneg _) h4 2
    · filter_upwards [hlc ω] with u hu hu'
      rw [Set.uIoc_of_le hT0] at hu'
      have := ((stepValue_lpt_tendsto T H ω hu' (hu hu')).sub_const (H u.toNNReal ω)).pow 2
      simpa using this
  have hjm : ∀ n, Measurable (fun z : ℝ × Ω =>
      (itoStepValue T n (lpt T H n) z.1 z.2 - H z.1.toNNReal z.2) ^ 2) := by
    intro n
    refine ((?_ : Measurable fun z : ℝ × Ω => itoStepValue T n (lpt T H n) z.1 z.2).sub
      hHm).pow_const 2
    unfold itoStepValue
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.ite ?_ (((hHa _).mono (hle _) le_rfl).comp measurable_snd) measurable_const
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) (Eventually.of_forall hpt)
  have hs : StronglyMeasurable (fun ω : Ω => ∫ u, (itoStepValue T n (lpt T H n) (u, ω).1 (u, ω).2 -
      H (u, ω).1.toNNReal (u, ω).2) ^ 2 ∂(volume.restrict (Set.Ioc (0 : ℝ) T.val))) :=
    (hjm n).stronglyMeasurable.integral_prod_left'
  refine hs.aestronglyMeasurable.congr (Eventually.of_forall fun ω => ?_)
  simp only [intervalIntegral.integral_of_le hT0]

end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

lemma efun_meas (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i : Elem m T) : Measurable (efun i) :=
  ((ind_meas i.u i.v).comp measurable_fst).mul ((i.hY.mono (hle i.u) le_rfl).comp measurable_snd)

lemma efun_abs_le {T : ℝ≥0} (i : Elem m T) (z : ℝ × Ω) : |efun i z| ≤ |i.C| := by
  rw [efun, abs_mul]
  calc |ind i.u i.v z.1| * |i.Y z.2| ≤ 1 * |i.Y z.2| :=
        mul_le_mul_of_nonneg_right (ind_abs_le _ _ _) (abs_nonneg _)
    _ ≤ |i.C| := by rw [one_mul]; exact (i.hC z.2).trans (le_abs_self _)

lemma abs_comb_le {T : ℝ≥0} (s : Elem m T →₀ ℝ) (z : ℝ × Ω) :
    |s.sum (fun i c => c * efun i z)| ≤ s.sum (fun i c => |c| * |i.C|) := by
  unfold Finsupp.sum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (efun_abs_le i z) (abs_nonneg _)

lemma comb_bound_nonneg {T : ℝ≥0} (s : Elem m T →₀ ℝ) :
    0 ≤ s.sum (fun i c => |c| * |i.C|) := by
  unfold Finsupp.sum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma efun_adapt (hmono : Monotone m) {T : ℝ≥0} (i : Elem m T) (t : ℝ≥0) :
    Measurable[m t] (fun ω => efun i ((t : ℝ), ω)) := by
  unfold efun
  by_cases hut : i.u ≤ t
  · show Measurable[m t] (fun ω => ind i.u i.v (t : ℝ) * i.Y ω)
    exact Measurable.const_mul (i.hY.mono (hmono hut) le_rfl) _
  · have h0 : ind i.u i.v (t : ℝ) = 0 := by
      simp only [ind, Set.indicator_apply, Set.mem_Ico]
      rw [if_neg]
      intro h
      exact hut (NNReal.coe_le_coe.1 h.1)
    simp only [h0, zero_mul]
    exact measurable_const

lemma ind_contAt {a b : ℝ≥0} {u : ℝ} (ha : u ≠ a) (hb : u ≠ b) : ContinuousAt (ind a b) u := by
  suffices h : ∀ᶠ r in 𝓝 u, ind a b r = ind a b u from
    continuousAt_const.congr (h.mono fun r hr => hr.symm)
  rcases lt_or_gt_of_ne ha with h | h
  · filter_upwards [Iio_mem_nhds h] with r hr
    simp only [ind, Set.indicator_apply, Set.mem_Ico]
    rw [if_neg (fun h' => absurd h'.1 (not_le.2 hr)), if_neg (fun h' => absurd h'.1 (not_le.2 h))]
  · rcases lt_or_gt_of_ne hb with h' | h'
    · filter_upwards [Ioo_mem_nhds h h'] with r hr
      simp only [ind, Set.indicator_apply, Set.mem_Ico]
      rw [if_pos ⟨hr.1.le, hr.2⟩, if_pos ⟨h.le, h'⟩]
    · filter_upwards [Ioi_mem_nhds h'] with r hr
      simp only [ind, Set.indicator_apply, Set.mem_Ico]
      rw [if_neg (fun h'' => absurd h''.2 (not_lt.2 (le_of_lt hr))),
        if_neg (fun h'' => absurd h''.2 (not_lt.2 h'.le))]

lemma comb_tendsto {T : ℝ≥0} (s : Elem m T →₀ ℝ) (ω : Ω) {u : ℝ} (hu0 : 0 < u)
    (hE : ∀ i ∈ s.support, u ≠ (i.u : ℝ) ∧ u ≠ (i.v : ℝ)) :
    Tendsto (fun v : ℝ => s.sum (fun i c => c * efun i ((v.toNNReal : ℝ), ω))) (𝓝 u)
      (𝓝 (s.sum (fun i c => c * efun i ((u.toNNReal : ℝ), ω)))) := by
  unfold Finsupp.sum
  refine tendsto_finset_sum _ fun i hi => ?_
  have hcu : ((u.toNNReal : ℝ)) = u := Real.coe_toNNReal _ hu0.le
  have h1 : ContinuousAt (ind i.u i.v) ((u.toNNReal : ℝ)) := by
    rw [hcu]; exact ind_contAt (hE i hi).1 (hE i hi).2
  have hc : ContinuousAt (fun v : ℝ => ind i.u i.v ((v.toNNReal : ℝ))) u :=
    h1.comp (f := fun v : ℝ => ((v.toNNReal : ℝ)))
      (NNReal.continuous_coe.comp continuous_real_toNNReal).continuousAt
  simp only [efun]
  exact (hc.tendsto.mul_const (i.Y ω)).const_mul (s i)

lemma ae_fst_Ico (T : ℝ≥0) : ∀ᵐ z ∂(μT P T), z.1 ∈ Set.Ico (0 : ℝ) T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ico)

lemma inner_toLp_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} {w : ℝ × Ω → ℝ}
    (hw : MemLp w 2 (μT P T)) (i : Elem m T) :
    ⟪hw.toLp w, eE (P := P) hle T i⟫_ℝ = ∫ z, w z * efun i z ∂(μT P T) := by
  unfold eE
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLp, (memLp_efun (P := P) hle i).coeFn_toLp] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', conj_trivial]



/-- The predictable subspace of `L²(μT)`. -/
noncomputable def Pred (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (μT P T)) :=
  (LinearMap.range (eL (P := P) hle T)).topologicalClosure

lemma mem_Pred_iff (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (x : Lp ℝ 2 (μT P T)) :
    x ∈ Pred (P := P) hle T ↔ x ∈ closure (Set.range (eL (P := P) hle T)) := by
  rw [Pred, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]


/-- An elementary combination times `φ`, as a process. -/
noncomputable def combφ {T : ℝ≥0} (s : Elem m T →₀ ℝ) (φ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  s.sum (fun i c => c * efun i ((t : ℝ), ω)) * φ t ω

theorem pred_mul (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0)
    {g : ℝ × Ω → ℝ} (hg : MemLp g 2 (μT P T))
    (hgP : hg.toLp g ∈ closure (Set.range (eL (P := P) hle T)))
    {φ : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |φ u ω| ≤ D)
    (hφm : Measurable (fun z : ℝ × Ω => φ z.1.toNNReal z.2))
    (hφa : ∀ t, Measurable[m t] (φ t))
    (hlc : ∀ ω, ∀ᵐ u ∂volume, u ∈ Set.Ioc 0 T.val →
      Tendsto (fun v : ℝ => φ v.toNNReal ω) (𝓝[<] u) (𝓝 (φ u.toNNReal ω)))
    (hgφ : MemLp (fun z => g z * φ z.1.toNNReal z.2) 2 (μT P T)) :
    hgφ.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  classical
  obtain ⟨x, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hgP
  choose s hs using hxr
  have hcoe : Measurable fun z : ℝ × Ω => ((z.1.toNNReal : ℝ)) :=
    (measurable_real_toNNReal.comp measurable_fst).coe_nnreal_real
  -- facts about each `combφ (s n) φ`
  have hB : ∀ n t ω, |combφ (s n) φ t ω| ≤ (s n).sum (fun i c => |c| * |i.C|) * D := by
    intro n t ω
    rw [combφ, abs_mul]
    exact mul_le_mul (abs_comb_le _ _) (hD t ω) (abs_nonneg _) (comb_bound_nonneg _)
  have hB0 : ∀ n, 0 ≤ (s n).sum (fun i c => |c| * |i.C|) * D :=
    fun n => mul_nonneg (comb_bound_nonneg _) hD0
  have hM : ∀ n, Measurable (fun z : ℝ × Ω => combφ (s n) φ z.1.toNNReal z.2) := by
    intro n
    simp only [combφ]
    unfold Finsupp.sum
    refine (Finset.measurable_sum _ fun i _ => ?_).mul hφm
    exact measurable_const.mul ((efun_meas hle i).comp (hcoe.prodMk measurable_snd))
  have hA : ∀ n t, Measurable[m t] (combφ (s n) φ t) := by
    intro n t
    unfold combφ Finsupp.sum
    exact (Finset.measurable_sum _ fun i _ => measurable_const.mul (efun_adapt hmono i t)).mul
      (hφa t)
  have hL : ∀ n ω, ∀ᵐ u ∂volume, u ∈ Set.Ioc 0 T.val →
      Tendsto (fun v : ℝ => combφ (s n) φ v.toNNReal ω) (𝓝[<] u)
        (𝓝 (combφ (s n) φ u.toNNReal ω)) := by
    intro n ω
    let E : Finset ℝ := (s n).support.biUnion (fun i => {(i.u : ℝ), (i.v : ℝ)})
    filter_upwards [hlc ω, measure_eq_zero_iff_ae_notMem.1
      ((E : Set ℝ).toFinite.measure_zero volume)] with u h1 h2 hu
    have hE : ∀ i ∈ (s n).support, u ≠ (i.u : ℝ) ∧ u ≠ (i.v : ℝ) := fun i hi =>
      ⟨fun h => h2 (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, hi, by simp [h]⟩)),
        fun h => h2 (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, hi, by simp [h]⟩))⟩
    simp only [combφ]
    exact ((comb_tendsto (s n) ω hu.1 hE).mono_left nhdsWithin_le_nhds).mul (h1 hu)
  have hL2 : ∀ n, MemLp (fun z : ℝ × Ω => combφ (s n) φ z.1.toNNReal z.2) 2 (μT P T) :=
    fun n => MemLp.of_bound (hM n).aestronglyMeasurable _
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB n _ _)
  have hmem : ∀ n, (hL2 n).toLp _ ∈ closure (Set.range (eL (P := P) hle T)) :=
    fun n => pred_left (P := P) hle T (hB0 n) (hB n) (hM n) (hA n) (hL n) (hL2 n)
  -- convergence
  have hx' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' x (hg.toLp g)).1 hx
  have hle' : ∀ n, eLpNorm ((fun z : ℝ × Ω => combφ (s n) φ z.1.toNNReal z.2) -
      fun z => g z * φ z.1.toNNReal z.2) 2 (μT P T) ≤
      ENNReal.ofReal D * eLpNorm (⇑(x n) - ⇑(hg.toLp g)) 2 (μT P T) := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
    filter_upwards [ae_fst_Ico (P := P) T, coe_eL (P := P) hle T (s n), hg.coeFn_toLp] with z hz h1 h2
    have hcz : ((z.1.toNNReal : ℝ)) = z.1 := Real.coe_toNNReal _ hz.1
    rw [← hs n] at *
    simp only [Pi.sub_apply, combφ, hcz, Prod.mk.eta, h1, h2, Real.norm_eq_abs]
    rw [← sub_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hD _ _) (abs_nonneg _)
  have hconv : Tendsto (fun n => (hL2 n).toLp _) atTop (𝓝 (hgφ.toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hL2 _ hgφ]
    have h0 : Tendsto (fun n => ENNReal.ofReal D * eLpNorm (⇑(x n) - ⇑(hg.toLp g)) 2 (μT P T))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hx' (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun n => by positivity) hle'
  exact isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall hmem)

end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}










/-- If `TL x_n → θ` and `a ∈ Pred` represents `θ`, then `eL x_n → a`. -/
theorem eL_tendsto (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T)))
    {x : ℕ → (Elem m T →₀ ℝ)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ)) :
    Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 a) := by
  have hc : CauchySeq fun n => eL (P := P) hW.le T (x n) := by
    have hcu : CauchySeq fun n => TL hW T (x n) := hx.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, ← norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hc
  have hψP : ψ ∈ closure (Set.range (eL (P := P) hW.le T)) :=
    mem_closure_of_tendsto hψ (Eventually.of_forall fun n => ⟨x n, rfl⟩)
  have horth : ∀ y, ⟪a - ψ, eL (P := P) hW.le T y⟫_ℝ = 0 := by
    intro y
    have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
      hx.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
        (𝓝 ⟪ψ, eL (P := P) hW.le T y⟫_ℝ) := hψ.inner tendsto_const_nhds
    simp only [inner_TL] at h1
    rw [inner_sub_left, ← ha y, tendsto_nhds_unique h1 h2, sub_self]
  have hcl : closure (Set.range (eL (P := P) hW.le T)) ⊆ {w | ⟪a - ψ, w⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact horth y)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hmem : a - ψ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
    have := (Pred (P := P) hW.le T).sub_mem ((mem_Pred_iff hW.le T a).2 haP)
      ((mem_Pred_iff hW.le T ψ).2 hψP)
    exact (mem_Pred_iff hW.le T _).1 this
  have h0 : a - ψ = 0 := inner_self_eq_zero.1 (hcl hmem)
  rw [sub_eq_zero.1 h0]
  exact hψ

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





lemma memLp_snd_ind {T : ℝ≥0} {w : Ω → ℝ} (hw : MemLp w 2 P) (u v : ℝ≥0) :
    MemLp (fun z : ℝ × Ω => w z.2 * ind u v z.1) 2 (μT P T) := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Ω => w z.2 * ind u v z.1) (μT P T) := by
    unfold μT
    exact hw.aestronglyMeasurable.comp_snd.mul ((ind_meas u v).comp measurable_fst).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  have hi : Integrable (fun r : ℝ => ind u v r ^ 2) (volume.restrict (Set.Ico (0 : ℝ) T)) := by
    refine (integrable_const (1 : ℝ)).mono' ((ind_meas u v).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (ind_abs_le _ _ _)
  have h2 := hi.mul_prod (hw.integrable_sq)
  unfold μT
  exact h2.congr (Eventually.of_forall fun z => by simp only; ring)


omit [IsProbabilityMeasure P] in
lemma inner_toLp_toLp {μ : Measure (ℝ × Ω)} {F G : ℝ × Ω → ℝ} (hF : MemLp F 2 μ)
    (hG : MemLp G 2 μ) : ⟪hF.toLp F, hG.toLp G⟫_ℝ = ∫ z, F z * G z ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', conj_trivial]

/-- **C3**: a process `w(ω) 1_{[0,s')}(r)` with `w ⊥ L^∞(m s')` is orthogonal to `Pred`. -/
lemma perp_tail (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) {T : ℝ≥0} (s' : ℝ≥0) {w : Ω → ℝ}
    (hw : MemLp w 2 P)
    (hwY : ∀ Y : Ω → ℝ, Measurable[m s'] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) → ∫ ω, w ω * Y ω ∂P = 0)
    {ψ : ℝ × Ω → ℝ} (hψ : MemLp ψ 2 (μT P T))
    (hψP : hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hle T))) :
    ∫ z, w z.2 * ind 0 s' z.1 * ψ z ∂(μT P T) = 0 := by
  have hF := memLp_snd_ind (T := T) hw 0 s'
  have h0 : ∀ i : Elem m T, ∫ z, w z.2 * ind 0 s' z.1 * efun i z ∂(μT P T) = 0 := by
    intro i
    have e : ∀ z : ℝ × Ω, w z.2 * ind 0 s' z.1 * efun i z =
        (ind 0 s' z.1 * ind i.u i.v z.1) * (w z.2 * i.Y z.2) := by
      intro z; simp only [efun]; ring
    simp_rw [e]
    unfold μT
    rw [integral_prod_mul (fun r => ind 0 s' r * ind i.u i.v r) (fun ω => w ω * i.Y ω)]
    by_cases hu : i.u < s'
    · rw [hwY i.Y (i.hY.mono (hmono hu.le) le_rfl) i.C i.hC, mul_zero]
    · have hz : (fun r => ind 0 s' r * ind i.u i.v r) = fun _ => (0 : ℝ) := by
        funext r
        rw [ind_mul, Set.indicator_apply, if_neg]
        rintro ⟨h1, h2⟩
        have hu' : (s' : ℝ) ≤ i.u := by exact_mod_cast not_lt.1 hu
        have a1 : (i.u : ℝ) ≤ r := (le_max_right _ _).trans h1
        have a2 : r < s' := (lt_min_iff.1 h2).1
        linarith
      rw [hz, integral_zero, zero_mul]
  have h1 : ∀ x, ⟪hF.toLp _, eL (P := P) hle T x⟫_ℝ = 0 := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => rw [map_zero, inner_zero_right]
    | add s1 s2 h1 h2 => rw [map_add, inner_add_right, h1, h2, add_zero]
    | single i c =>
      simp only [eL, Finsupp.linearCombination_single]
      rw [inner_smul_right, inner_toLp_eE, h0, mul_zero]
  have hcl : closure (Set.range (eL (P := P) hle T)) ⊆ {x | ⟪hF.toLp _, x⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact h1 x)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have := hcl hψP
  simp only [Set.mem_setOf_eq] at this
  rw [inner_toLp_toLp] at this
  exact this



end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- `θ` is the stochastic integral of the predictable integrand `b`. -/
def Rep (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Set.range (TL hW T)) ∧ b ∈ closure (Set.range (eL (P := P) hW.le T)) ∧
    ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪b, eL (P := P) hW.le T x⟫_ℝ

lemma rep_dist (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) (x : Elem m T →₀ ℝ) :
    ‖TL hW T x - θ‖ = ‖eL (P := P) hW.le T x - b‖ := by
  obtain ⟨hθ, hb, hi⟩ := h
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hθ
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by simp_rw [hy]; exact hx
  have hE := eL_tendsto hW T hi hb hx'
  have h1 : Tendsto (fun n => ‖TL hW T x - TL hW T (y n)‖) atTop (𝓝 ‖TL hW T x - θ‖) :=
    (tendsto_const_nhds.sub hx').norm
  have h2 : Tendsto (fun n => ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖) atTop
      (𝓝 ‖eL (P := P) hW.le T x - b‖) := (tendsto_const_nhds.sub hE).norm
  have he : ∀ n, ‖TL hW T x - TL hW T (y n)‖ =
      ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖ := by
    intro n; rw [← map_sub, ← map_sub, norm_TL]
  simp_rw [he] at h1
  exact tendsto_nhds_unique h1 h2
























end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/


















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}



end Gen






end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






variable {Ic : ℝ≥0 → Ω → ℝ}
















end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω}


end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV







end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge









end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}





end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]


end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of RUmod (scratch/probe/slice8c/cuts/r_tce3.lean.src/RUmod.lean): 11/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Elementary time-space functions `1_[u,v) Y`, Elem-free. -/
def SE (m : ℝ≥0 → MeasurableSpace Ω) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 (μT P T)) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun z : ℝ × Ω => ind u v z.1 * Y z.2) 2 (μT P T), g = h.toLp _}

/-- Elementary stochastic integrals `Y (W_v - W_u)`, Elem-free. -/
def SI (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 P) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _}

/-- `Rep`, Elem-free. -/
def RepU (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0)
    (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) ∧
    b ∈ closure (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) ∧
    ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y → (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
      ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
        ∫ z, (b : ℝ × Ω → ℝ) z * (ind u v z.1 * Y z.2) ∂(μT P T)



lemma range_eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eE (P := P) hle T) = SE m P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_efun hle i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eI (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (eI hW T) = SI m W P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_ifun hW i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eL (P := P) hle T) = (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) := by
  rw [← LinearMap.coe_range]
  unfold eL
  rw [Finsupp.range_linearCombination, range_eE]

lemma range_TL (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (TL hW T) = (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) := by
  rw [← LinearMap.coe_range]
  unfold TL
  rw [Finsupp.range_linearCombination, range_eI]

lemma closure_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    closure (Set.range (eL (P := P) hle T)) =
      closure (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) := by
  rw [range_eL]

lemma int_eI (hW : IncrHyp m W P) {T : ℝ≥0} (θ : Lp ℝ 2 P) (i : Elem m T) :
    ∫ ω, (θ : Ω → ℝ) ω * (i.Y ω * (W i.v ω - W i.u ω)) ∂P = ⟪θ, eI hW T i⟫_ℝ := by
  unfold eI
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_ifun hW i).coeFn_toLp] with ω hω
  rw [hω, ifun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma int_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (b : Lp ℝ 2 (μT P T)) (i : Elem m T) :
    ∫ z, (b : ℝ × Ω → ℝ) z * (ind i.u i.v z.1 * i.Y z.2) ∂(μT P T) = ⟪b, eE (P := P) hle T i⟫_ℝ := by
  unfold eE
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_efun (P := P) hle i).coeFn_toLp] with z hz
  rw [hz, efun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma rep_iff (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) :
    StochCalcO3.Rep hW T θ b ↔ RepU m W P T θ b := by
  unfold StochCalcO3.Rep RepU
  rw [range_TL, range_eL]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩)
  · intro u v huv hvT Y hY hC
    obtain ⟨C, hC⟩ := hC
    let i : Elem m T := ⟨u, v, huv, hvT, Y, hY, C, hC⟩
    have h1 := h (Finsupp.single i 1)
    simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at h1
    rw [int_eI hW θ i, int_eE hW.le b i]
    exact h1
  · intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add s1 s2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single i a =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_right]
      rw [← int_eI hW θ i, ← int_eE hW.le b i, h i.u i.v i.huv i.hvT i.Y i.hY ⟨i.C, i.hC⟩]

end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcZ2 StochCalcZ3 StochCalcO3
open StochCalcZK
open StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcQ2U

end StochCalcP6

-- ===== slice of P8c066573M16b (scratch/probe/slice8c/cuts/r_tce3.lean.src/P8c066573M16b.lean): 31/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



































end StochCalcBr

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcD1b

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




end StochCalcIndep

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcHs

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}


















end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]












end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



















end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein








end StochCalcStein
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6




/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]




variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)



end StochCalcP6S

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]











end StochCalcHedgeDeg

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcD2

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6




end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)


end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcD3
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






















end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
































end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/








/-! The clamped approximants as elementary combinations. -/











end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}



end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}




end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

















end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



lemma rep_lim (hW : IncrHyp m W P) (T : ℝ≥0) {x : ℕ → (Elem m T →₀ ℝ)} {θ : Lp ℝ 2 P}
    {b : Lp ℝ 2 (μT P T)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ))
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) : Rep hW T θ b := by
  refine ⟨mem_closure_of_tendsto hx (Eventually.of_forall fun n => ⟨x n, rfl⟩),
    mem_closure_of_tendsto hb (Eventually.of_forall fun n => ⟨x n, rfl⟩), fun y => ?_⟩
  have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
    hx.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
      (𝓝 ⟪b, eL (P := P) hW.le T y⟫_ℝ) := hb.inner tendsto_const_nhds
  simp only [inner_TL] at h1
  exact tendsto_nhds_unique h1 h2


lemma rep_conv (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {x : ℕ → (Elem m T →₀ ℝ)}
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) :
    Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
  simp_rw [rep_dist hW T h]
  exact hb



lemma rep_add (hW : IncrHyp m W P) (T : ℝ≥0) {θ₁ θ₂ : Lp ℝ 2 P} {b₁ b₂ : Lp ℝ 2 (μT P T)}
    (h₁ : Rep hW T θ₁ b₁) (h₂ : Rep hW T θ₂ b₂) : Rep hW T (θ₁ + θ₂) (b₁ + b₂) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h₁.2.1
  choose y hy using hxr
  obtain ⟨xs', hxr', hx''⟩ := mem_closure_iff_seq_limit.1 h₂.2.1
  choose y' hy' using hxr'
  have e1 : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b₁) := by
    simp_rw [hy]; exact hx
  have e2 : Tendsto (fun n => eL (P := P) hW.le T (y' n)) atTop (𝓝 b₂) := by
    simp_rw [hy']; exact hx''
  refine rep_lim hW T (x := fun n => y n + y' n) ?_ ?_
  · simp_rw [map_add]; exact (rep_conv hW T h₁ e1).add (rep_conv hW T h₂ e2)
  · simp_rw [map_add]; exact e1.add e2


















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/

lemma rep_neg (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) : Rep hW T (-θ) (-b) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.2.1
  choose y hy using hxr
  have e1 : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  refine rep_lim hW T (x := fun n => -y n) ?_ ?_
  · simp_rw [map_neg]; exact (rep_conv hW T h e1).neg
  · simp_rw [map_neg]; exact e1.neg

lemma rep_sub (hW : IncrHyp m W P) (T : ℝ≥0) {θ₁ θ₂ : Lp ℝ 2 P} {b₁ b₂ : Lp ℝ 2 (μT P T)}
    (h₁ : Rep hW T θ₁ b₁) (h₂ : Rep hW T θ₂ b₂) : Rep hW T (θ₁ - θ₂) (b₁ - b₂) := by
  simpa [sub_eq_add_neg] using rep_add hW T h₁ (rep_neg hW T h₂)
















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}

/-- A function measurable for the a.e. closure of `G` (`G` containing the measurable null sets)
has a `G`-measurable a.e. version. -/
theorem exists_version_of_aeClosure {G : MeasurableSpace Ω'} {m0 : MeasurableSpace Ω'}
    {P : Measure[m0] Ω'} (hG : G ≤ m0)
    (hG0 : ∀ N : Set Ω', MeasurableSet[m0] N → P N = 0 → MeasurableSet[G] N) {Y : Ω' → ℝ}
    (hY : Measurable[aeClosure P G] Y) : ∃ Y' : Ω' → ℝ, Measurable[G] Y' ∧ Y' =ᵐ[P] Y := by
  have hnull : @NullMeasurable Ω' ℝ G _ Y (P.trim hG) := by
    intro S hS
    obtain ⟨B, hB, hAB⟩ := hY hS
    have h0 : P {x | ¬ ((Y ⁻¹' S) x = B x)} = 0 := ae_iff.1 hAB
    obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
    have hNG := hG0 N hNm hN0
    have hAB' : Y ⁻¹' S =ᵐ[P.trim hG] B := by
      refine ae_iff.2 ?_
      exact measure_mono_null hsub (by rw [trim_measurableSet_eq hG hNG]; exact hN0)
    exact (hB.nullMeasurableSet (μ := P.trim hG)).congr hAB'.symm
  have hae := hnull.aemeasurable
  exact ⟨hae.mk Y, hae.measurable_mk, (ae_eq_of_ae_eq_trim hae.ae_eq_mk).symm⟩

lemma meas_vec {m : MeasurableSpace Ω'} {f g : Ω' → ℝ} (hf : Measurable[m] f)
    (hg : Measurable[m] g) :
    Measurable[m] (fun ω => (WithLp.toLp 2 ![f ω, g ω] : EuclideanSpace ℝ (Fin 2))) := by
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  fin_cases i
  · simpa using hf
  · simpa using hg

end Gen

lemma null_mem_F (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) (N : Set Ω) (hN : MeasurableSet N)
    (hN0 : M.P N = 0) : MeasurableSet[M.F t] N := by
  have h1 : MeasurableSet[MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet N ∧ M.P N = 0}] N :=
    MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩
  have h2 : MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ M.P N = 0} ≤ M.F t := by
    rw [hM.filtF t]; exact le_sup_right
  exact h2 N h1

lemma pair_measF (M : Model p Ω) (hM : M.Standing) {s t : ℝ≥0} (hs : s ≤ t) :
    Measurable[M.F t] (fun ω => (M.B s ω, M.Bt s ω)) := by
  have h2 : MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance ≤ M.F t := by
    rw [hM.filtF t]
    exact le_sup_of_le_left (le_iSup₂ (f := fun s' (_ : s' ≤ t) =>
      MeasurableSpace.comap (fun ω => (M.B s' ω, M.Bt s' ω)) inferInstance) s hs)
  exact Measurable.of_comap_le h2

lemma W_measF (M : Model p Ω) (hM : M.Standing) {s t : ℝ≥0} (hs : s ≤ t) :
    Measurable[M.F t] (W M s) := by
  have hN := null_mem_F M hM t (Nbad M) (Nbad_meas M) (Nbad_null M hM)
  have hB : Measurable[M.F t] (M.B s) := measurable_fst.comp (pair_measF M hM hs)
  have hBt : Measurable[M.F t] (M.Bt s) := measurable_snd.comp (pair_measF M hM hs)
  have h0 : Measurable[M.F t] (gB M s) := Measurable.ite hN measurable_const hB
  have h1 : Measurable[M.F t] (gBt M s) := Measurable.ite hN measurable_const hBt
  exact meas_vec h0 h1

lemma cBP_le_aeF (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    completedBrownianPast M.P (W M) (fun _ => 0) t ≤ aeClosure M.P (M.F t) := by
  have hGW : (⨆ r : Set.Iic t, MeasurableSpace.comap (W M r.val) inferInstance) ≤ M.F t :=
    iSup_le fun r => (W_measF M hM r.2).comap_le
  intro A hA
  obtain ⟨B, hB, hAB⟩ := completedBrownianPast_const_le M.P (W M) 0 t A hA
  exact ⟨B, hGW B hB, hAB⟩

/-- **Z4m-a.** Every completed-Brownian-past measurable variable has an `M.F t`-measurable
a.e. version. -/
theorem hmod_cBP (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) (Y : Ω → ℝ)
    (hY : Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] Y) :
    ∃ Y' : Ω → ℝ, Measurable[M.F t] Y' ∧ Y' =ᵐ[M.P] Y :=
  exists_version_of_aeClosure (M.F.le t) (null_mem_F M hM t) (hY.mono (cBP_le_aeF M hM t) le_rfl)

end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Conjunct 3 of `EthierKurtz.brownian_ito_integral_locality_and_continuity` (platform theorem
1c98c8e0) for the model's 2-d Brownian motion `W M`, coordinate 0. -/
def ContHyp (M : Model p Ω) : Prop :=
  ∀ H : ℝ≥0 → Ω → ℝ,
    (∀ s, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s] (H s)) →
    (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
    ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
    ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
      (∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Jc t)) ∧
      (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
      HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
        (fun s ω => W M s ω 0) H Jc

/-- `η` frozen at the horizon. -/
noncomputable def etaT (M : Model p Ω) (s : ℝ≥0) (ω : Ω) : ℝ := M.η (min s p.T) ω


lemma etaT_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) : Continuous fun s => etaT M s ω :=
  (η_cont M hM ω).comp (continuous_id.min continuous_const)

lemma etaT_cBP (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s] (etaT M s) :=
  (((η_meas M hM (min s p.T)).measurable.mono (F_le_cBP M hM _) le_rfl)).mono
    (completedBrownianPast_mono _ _ _ (min_le_left _ _)) le_rfl

lemma etaT_meas (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) : Measurable (etaT M s) :=
  (η_meas M hM (min s p.T)).measurable.mono (M.F.le _) le_rfl











end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








/-- Riemann-sum measurability of `ω ↦ ∫_0^t H`. -/
lemma int_meas {G : MeasurableSpace Ω} (H : ℝ≥0 → Ω → ℝ) (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (hm : ∀ s, s ≤ t → Measurable[G] (H s)) :
    Measurable[G] (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω) := by
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (ω : Ω) =>
    (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ))
    (fun n => ?_) (tendsto_pi_nhds.mpr (fun ω => riemann_tendsto hHc t ω))
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ (fun k hk =>
    hm _ (dyTime_le t (Finset.mem_range.mp hk).le))


/-- `Zc = exp(-Ic - ½∫_0^s η'²)`. -/
noncomputable def Zc (M : Model p Ω) (Ic : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(Ic s ω) - (1 / 2) * ∫ u in (0 : ℝ)..s.val, etaT M u.toNNReal ω ^ 2)


end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A measurable function a.e. equal to an `M.F t`-measurable one is `M.F t`-measurable. -/
lemma measF_of_ae_eq (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) {Y Y' : Ω → ℝ}
    (hY : Measurable Y) (hY' : Measurable[M.F t] Y') (he : Y =ᵐ[M.P] Y') :
    Measurable[M.F t] Y := by
  set N := toMeasurable M.P {ω | Y ω ≠ Y' ω}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : M.P N = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp he
  have hsub : {ω | Y ω ≠ Y' ω} ⊆ N := subset_toMeasurable _ _
  intro A hA
  have e : Y ⁻¹' A = (Y' ⁻¹' A ∩ Nᶜ) ∪ (Y ⁻¹' A ∩ N) := by
    ext ω
    by_cases h : ω ∈ N
    · simp [h]
    · have hYY : Y ω = Y' ω := by
        by_contra h'
        exact h (hsub h')
      simp [h, hYY]
  rw [e]
  refine ((hY' hA).inter (null_mem_F M hM t N hNm hN0).compl).union ?_
  exact null_mem_F M hM t _ ((hY hA).inter hNm) (measure_mono_null Set.inter_subset_right hN0)



lemma A_cBP (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s]
      (fun ω => ∫ u in (0 : ℝ)..s.val, etaT M u.toNNReal ω ^ 2) :=
  int_meas (fun u ω => etaT M u ω ^ 2) (fun ω => (etaT_cont M hM ω).pow 2) s
    (fun u hu => ((etaT_cBP M hM u).mono (completedBrownianPast_mono _ _ _ hu) le_rfl).pow_const 2)

lemma A_meas (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    Measurable (fun ω => ∫ u in (0 : ℝ)..s.val, etaT M u.toNNReal ω ^ 2) :=
  int_meas (fun u ω => etaT M u ω ^ 2) (fun ω => (etaT_cont M hM ω).pow 2) s
    (fun u _ => (etaT_meas M hM u).pow_const 2)

variable {Ic : ℝ≥0 → Ω → ℝ}


lemma Zc_cBP (M : Model p Ω) (hM : M.Standing)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t)) (s : ℝ≥0) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s] (Zc M Ic s) := by
  unfold Zc
  exact Real.measurable_exp.comp (((hIa s).neg).sub (measurable_const.mul (A_cBP M hM s)))

lemma Zc_meas (M : Model p Ω) (hM : M.Standing) (hIm : ∀ t, Measurable (Ic t)) (s : ℝ≥0) :
    Measurable (Zc M Ic s) := by
  unfold Zc
  exact Real.measurable_exp.comp (((hIm s).neg).sub (measurable_const.mul (A_meas M hM s)))

lemma Zc_measF (M : Model p Ω) (hM : M.Standing)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (s : ℝ≥0) : Measurable[M.F s] (Zc M Ic s) := by
  obtain ⟨Y', hY', he⟩ := hmod_cBP M hM s _ (Zc_cBP M hM hIa s)
  exact measF_of_ae_eq M hM s (Zc_meas M hM hIm s) hY' he.symm


lemma Zc_eq (M : Model p Ω) (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {t : ℝ≥0}
    (ht : t ≤ p.T) : Zc M Ic t =ᵐ[M.P] M.Z t := by
  filter_upwards [hIe t ht] with ω hω
  have hint : (∫ u in (0 : ℝ)..t.val, etaT M u.toNNReal ω ^ 2) =
      ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω ^ 2 := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have hu' : u ≤ (t : ℝ) := by
      rcases Set.mem_uIcc.1 hu with h | h
      · exact h.2
      · exact h.2.trans (NNReal.coe_nonneg t)
    have h1 : u.toNNReal ≤ p.T := (Real.toNNReal_le_iff_le_coe.2 hu').trans ht
    simp only [etaT, min_eq_left h1]
  show Real.exp (-(Ic t ω) - (1 / 2) * ∫ u in (0 : ℝ)..t.val, etaT M u.toNNReal ω ^ 2) =
    Real.exp (-(M.I t ω) - (1 / 2) * ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω ^ 2)
  rw [hω, hint]

lemma Zc_mart (M : Model p Ω) (h5 : M.Assumption5)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {t : ℝ≥0} (ht : t ≤ p.T) :
    condExp (M.F t) M.P (Zc M Ic p.T) =ᵐ[M.P] Zc M Ic t :=
  (condExp_congr_ae (Zc_eq M hIe le_rfl)).trans
    ((h5.1.2.2 t p.T ht le_rfl).trans (Zc_eq M hIe ht).symm)

lemma Zc_memLp (M : Model p Ω) (h5 : M.Assumption5)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) : MemLp (Zc M Ic p.T) 2 M.P :=
  (h5.2 p.T le_rfl).ae_eq (Zc_eq M hIe le_rfl).symm








end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











/-- **ζ-tail** (O7.3 remainder, Rep part): `ζ (θ - E[θ|m t]) = I(ζ a 1_[t,T))` for bounded
`m t`-measurable `ζ`. -/
theorem rep_zeta_tail (hW : IncrHyp m W P) (T : ℝ≥0) {t : ℝ≥0} (htT : t ≤ T)
    {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)} (h : Rep hW T θ a) {θt : Lp ℝ 2 P}
    (hθt : (θt : Ω → ℝ) =ᵐ[P] condExp (m t) P θ) {ζ : Ω → ℝ}
    (hζ : Measurable[m t] ζ) {Cz : ℝ} (hCz : ∀ ω, |ζ ω| ≤ Cz)
    {θ' : Lp ℝ 2 P} (hθ' : θ' =ᵐ[P] fun ω => ζ ω * (θ ω - θt ω))
    {b' : Lp ℝ 2 (μT P T)} (hb' : b' =ᵐ[μT P T] fun z => ζ z.2 * (a z * (1 - ind 0 t z.1))) :
    Rep hW T θ' b' := by
  exact (StochCalcP6.StochCalcRU.rep_iff hW T θ' b').2 (by unfold StochCalcP6.StochCalcRU.RepU; exact HedgePSNV.conditional_tail_integrand_representation hW.mono hW.le hW.adapt hW.indep hW.mem2 hW.mean hW.var T (StochCalcP6.StochCalcO3.μT P T) rfl htT ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).1 ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).2.1 ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).2.2 hθt hζ hCz hθ' hb')











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `Zc` frozen at the horizon. -/
noncomputable def ZT (M : Model p Ω) (Ic : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Zc M Ic (min s p.T) ω

lemma ZT_of_le (M : Model p Ω) (Ic : ℝ≥0 → Ω → ℝ) {s : ℝ≥0} (hs : s ≤ p.T) (ω : Ω) :
    ZT M Ic s ω = Zc M Ic s ω := by
  simp [ZT, min_eq_left hs]


end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω}


end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV







end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge









end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}





end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]


end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of RUz (scratch/probe/slice8c/cuts/r_tce3.lean.src/RUz.lean): 1/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}














end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcZ2 StochCalcZ3 StochCalcO3
open StochCalcZK
open StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




/-- Back-conversion used when `zK` is wrapped over the `zKU` child. -/
theorem zK_back (M : Model p Ω) [IsProbabilityMeasure M.P] {Ic : ℝ≥0 → Ω → ℝ}
    {mK : ℝ≥0 → MeasurableSpace Ω} (hKB : IncrHyp mK M.B M.P) {t : ℝ≥0} {ζ : Ω → ℝ}
    (hU :
      ∃ hc2 : MemLp (fun z : ℝ × Ω => ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2)) 2
          (μT M.P p.T),
      ∃ θ2 : Lp ℝ 2 M.P, ((θ2 : Ω → ℝ) =ᵐ[M.P] fun ω => ζ ω * (Zc M Ic p.T ω - Zc M Ic t ω)) ∧
      ∃ a2 : Lp ℝ 2 (μT M.P p.T),
        ((a2 : ℝ × Ω → ℝ) =ᵐ[μT M.P p.T] fun z => ζ z.2 *
          (-(Zc M Ic z.1.toNNReal z.2 * etaT M z.1.toNNReal z.2) * (1 - ind 0 t z.1))) ∧
        RepU mK M.B M.P p.T θ2 a2 ∧ hc2.toLp _ ∈ closure (Submodule.span ℝ (SE mK M.P p.T) : Set (Lp ℝ 2 (μT M.P p.T))) ∧
        ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
          hψ.toLp ψ ∈ closure (Submodule.span ℝ (SE mK M.P p.T) : Set (Lp ℝ 2 (μT M.P p.T))) →
          ∫ z, ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2) * ψ z ∂(μT M.P p.T) =
            ∫ z, (θ2 : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T)) :
    ∃ hc2 : MemLp (fun z : ℝ × Ω => ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2)) 2
        (μT M.P p.T),
    ∃ θ2 : Lp ℝ 2 M.P, ((θ2 : Ω → ℝ) =ᵐ[M.P] fun ω => ζ ω * (Zc M Ic p.T ω - Zc M Ic t ω)) ∧
    ∃ a2 : Lp ℝ 2 (μT M.P p.T),
      ((a2 : ℝ × Ω → ℝ) =ᵐ[μT M.P p.T] fun z => ζ z.2 *
        (-(Zc M Ic z.1.toNNReal z.2 * etaT M z.1.toNNReal z.2) * (1 - ind 0 t z.1))) ∧
      StochCalcO3.Rep hKB p.T θ2 a2 ∧ hc2.toLp _ ∈ closure (Set.range (eL (P := M.P) hKB.le p.T)) ∧
      ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
        hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) hKB.le p.T)) →
        ∫ z, ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2) * ψ z ∂(μT M.P p.T) =
          ∫ z, (θ2 : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) := by
  obtain ⟨hc2, θ2, h1, a2, h2, hr, hm, hp⟩ := hU
  refine ⟨hc2, θ2, h1, a2, h2, (rep_iff hKB p.T θ2 a2).2 hr, ?_, fun ψ hψ hψm => hp ψ hψ ?_⟩
  · rw [closure_eL]; exact hm
  · rw [← closure_eL hKB.le]; exact hψm

end StochCalcQ2U

end StochCalcP6

-- ===== slice of P8c066573M16d (scratch/probe/slice8c/cuts/r_tce3.lean.src/P8c066573M16d.lean): 23/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



































end StochCalcBr

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcD1b

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




end StochCalcIndep

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcHs

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}


















end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]












end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



















end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein








end StochCalcStein
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6




/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]




variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)



end StochCalcP6S

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]











end StochCalcHedgeDeg

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcD2

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6




end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)


end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcD3
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






















end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
































end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/








/-! The clamped approximants as elementary combinations. -/











end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}



end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}




end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

















end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


























end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/


















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}



end Gen






end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






variable {Ic : ℝ≥0 → Ω → ℝ}
















end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



/-- **zK (O7.3 model instance in `mK`).** -/
theorem zK (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    (hC : ContHyp M) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + Kj t ω)
    {mK : ℝ≥0 → MeasurableSpace Ω} (hKB : IncrHyp mK M.B M.P)
    (hZK : ∀ s, s ≤ p.T → Measurable[mK s] (Zc M Ic s))
    (hηK : ∀ s, Measurable[mK s] (etaT M s))
    (hKF : ∀ s, mK s ≤ M.F s)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ p.T → Measurable[M.F u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK p.T) M.P Y =ᵐ[M.P] condExp (mK u) M.P Y)
    {t : ℝ≥0} (htT : t ≤ p.T) {ζ : Ω → ℝ} (hζ : Measurable[mK t] ζ) {Cz : ℝ}
    (hCz : ∀ ω, |ζ ω| ≤ Cz) :
    ∃ hc2 : MemLp (fun z : ℝ × Ω => ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2)) 2
        (μT M.P p.T),
    ∃ θ2 : Lp ℝ 2 M.P, ((θ2 : Ω → ℝ) =ᵐ[M.P] fun ω => ζ ω * (Zc M Ic p.T ω - Zc M Ic t ω)) ∧
    ∃ a2 : Lp ℝ 2 (μT M.P p.T),
      ((a2 : ℝ × Ω → ℝ) =ᵐ[μT M.P p.T] fun z => ζ z.2 *
        (-(Zc M Ic z.1.toNNReal z.2 * etaT M z.1.toNNReal z.2) * (1 - ind 0 t z.1))) ∧
      Rep hKB p.T θ2 a2 ∧ hc2.toLp _ ∈ closure (Set.range (eL (P := M.P) hKB.le p.T)) ∧
      ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
        hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) hKB.le p.T)) →
        ∫ z, ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2) * ψ z ∂(μT M.P p.T) =
          ∫ z, (θ2 : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) := by
  exact StochCalcP6.StochCalcQ2U.zK_back M hKB (HedgePSNV.tilted_density_increment_representation M hM h5 (StochCalcBr.W M) (fun _ _ => rfl) hC hIc hIa hIm hI0 hIe (StochCalcP6.StochCalcZ3.Zc M Ic) (fun _ _ => rfl) hKj hKz _ rfl hKB.mono hKB.le hKB.adapt hKB.indep hKB.mem2 hKB.mean hKB.var hZK hηK hKF H1 htT hζ hCz)
































































































end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

theorem ce_sup_indep (hAF : A ≤ F') (hF : F' ≤ mΩ) (hD : D ≤ mΩ) (hind : Indep F' D P)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[F'] Y) (hYi : Integrable Y P) :
    condExp (A ⊔ D) P Y =ᵐ[P] condExp A P Y := by
  have hA : A ≤ mΩ := hAF.trans hF
  have hAD : A ⊔ D ≤ mΩ := sup_le hA hD
  set g := condExp A P Y with hgdef
  have hgi : Integrable g P := integrable_condExp
  have hgA : StronglyMeasurable[A] g := stronglyMeasurable_condExp
  have hprod : ∀ a d, MeasurableSet[A] a → MeasurableSet[D] d → ∀ f : Ω → ℝ,
      StronglyMeasurable[F'] f → Integrable f P →
      ∫ ω in a ∩ d, f ω ∂P = (∫ ω in a, f ω ∂P) * P.real d := by
    intro a d ha hd f hf hfi
    have e1 : ∫ ω in a ∩ d, f ω ∂P =
        ∫ ω, a.indicator f ω * d.indicator (fun _ => (1 : ℝ)) ω ∂P := by
      rw [← integral_indicator ((hA _ ha).inter (hD _ hd))]
      congr 1
      ext ω
      by_cases h1 : ω ∈ a <;> by_cases h2 : ω ∈ d <;> simp [Set.indicator, h1, h2]
    have hm1 : Measurable[F'] (a.indicator f) := (hf.indicator (hAF _ ha)).measurable
    have hm2 : Measurable[D] (d.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hd
    have hind' : IndepFun (a.indicator f) (d.indicator fun _ => (1 : ℝ)) P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hind hm2.comap_le) hm1.comap_le
    have hmul := hind'.integral_mul_eq_mul_integral (hm1.mono hF le_rfl).aestronglyMeasurable
      (hm2.mono hD le_rfl).aestronglyMeasurable
    simp only [Pi.mul_apply] at hmul
    rw [e1, hmul, integral_indicator (hA _ ha),
      integral_indicator_const _ (hD _ hd)]
    simp
  have hrect : ∀ a d, MeasurableSet[A] a → MeasurableSet[D] d →
      ∫ ω in a ∩ d, g ω ∂P = ∫ ω in a ∩ d, Y ω ∂P := by
    intro a d ha hd
    rw [hprod a d ha hd g (hgA.mono hAF) hgi, hprod a d ha hd Y hY hYi,
      setIntegral_condExp hA hYi ha]
  let C : Set (Set Ω) := {s | ∃ a d, MeasurableSet[A] a ∧ MeasurableSet[D] d ∧ s = a ∩ d}
  have hgen : A ⊔ D = MeasurableSpace.generateFrom C := by
    refine le_antisymm (sup_le (fun a ha => MeasurableSpace.measurableSet_generateFrom
      ⟨a, Set.univ, ha, MeasurableSet.univ, (Set.inter_univ a).symm⟩)
      (fun d hd => MeasurableSpace.measurableSet_generateFrom
      ⟨Set.univ, d, MeasurableSet.univ, hd, (Set.univ_inter d).symm⟩))
      (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨a, d, ha, hd, rfl⟩
    have h1 : MeasurableSet[A ⊔ D] a := (le_sup_left : A ≤ A ⊔ D) a ha
    have h2 : MeasurableSet[A ⊔ D] d := (le_sup_right : D ≤ A ⊔ D) d hd
    exact h1.inter h2
  have hpi : IsPiSystem C := by
    rintro _ ⟨a, d, ha, hd, rfl⟩ _ ⟨a', d', ha', hd', rfl⟩ _
    exact ⟨a ∩ a', d ∩ d', ha.inter ha', hd.inter hd', Set.inter_inter_inter_comm a d a' d'⟩
  have htot : ∫ ω, g ω ∂P = ∫ ω, Y ω ∂P := integral_condExp hA
  have hall : ∀ s, MeasurableSet[A ⊔ D] s → ∫ ω in s, g ω ∂P = ∫ ω in s, Y ω ∂P := by
    refine MeasurableSpace.induction_on_inter (C := fun s _ => ∫ ω in s, g ω ∂P = ∫ ω in s, Y ω ∂P)
      hgen hpi (by simp) ?_ ?_ ?_
    · rintro t ⟨a, d, ha, hd, rfl⟩
      exact hrect a d ha hd
    · intro t htm ht
      rw [setIntegral_compl (hAD _ htm) hgi, setIntegral_compl (hAD _ htm) hYi, ht, htot]
    · intro f hdisj hfm hf
      rw [integral_iUnion (fun i => hAD _ (hfm i)) hdisj hgi.integrableOn,
        integral_iUnion (fun i => hAD _ (hfm i)) hdisj hYi.integrableOn]
      exact tsum_congr hf
  exact (ae_eq_condExp_of_forall_setIntegral_eq hAD hYi (fun s _ _ => hgi.integrableOn)
    (fun s hs _ => hall s hs) (hgA.mono (le_sup_left : A ≤ A ⊔ D)).aestronglyMeasurable).symm

theorem ce_between (hAF : A ≤ F') (hF : F' ≤ mΩ) (hD : D ≤ mΩ)
    (hind : Indep F' D P) (hAK : A ≤ K) (hKAD : K ≤ A ⊔ D)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[F'] Y) (hYi : Integrable Y P) :
    condExp K P Y =ᵐ[P] condExp A P Y := by
  have hADle : A ⊔ D ≤ mΩ := sup_le (hAF.trans hF) hD
  have hKle : K ≤ mΩ := hKAD.trans hADle
  have h1 := ce_sup_indep hAF hF hD hind hY hYi
  have h2 : condExp K P (condExp (A ⊔ D) P Y) =ᵐ[P] condExp K P Y :=
    condExp_condExp_of_le hKAD hADle
  have h3 : condExp K P (condExp (A ⊔ D) P Y) =ᵐ[P] condExp K P (condExp A P Y) :=
    condExp_congr_ae h1
  have h4 : condExp K P (condExp A P Y) = condExp A P Y :=
    condExp_of_stronglyMeasurable hKle (stronglyMeasurable_condExp.mono hAK) integrable_condExp
  rw [h4] at h3
  exact h2.symm.trans h3

omit [IsProbabilityMeasure P] in
theorem meas_of_ae_eq_nulls
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[A] N)
    {Y Y' : Ω → ℝ} (hY : Measurable Y) (hY' : Measurable[A] Y') (he : Y =ᵐ[P] Y') :
    Measurable[A] Y := by
  set N := toMeasurable P {ω | Y ω ≠ Y' ω}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp he
  have hsub : {ω | Y ω ≠ Y' ω} ⊆ N := subset_toMeasurable _ _
  intro S hS
  have e : Y ⁻¹' S = (Y' ⁻¹' S ∩ Nᶜ) ∪ (Y ⁻¹' S ∩ N) := by
    ext ω
    by_cases h : ω ∈ N
    · simp [h]
    · have hYY : Y ω = Y' ω := by
        by_contra h'
        exact h (hsub h')
      simp [h, hYY]
  rw [e]
  refine ((hY' hS).inter (hnull N hNm hN0).compl).union ?_
  exact hnull _ ((hY hS).inter hNm) (measure_mono_null Set.inter_subset_right hN0)

end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The filtration `K^t`. -/
noncomputable def Kf (M : Model p Ω) (t s : ℝ≥0) : MeasurableSpace Ω :=
  if s < t then M.F s else M.F t ⊔ M.G s

lemma Kf_lt (M : Model p Ω) {t s : ℝ≥0} (h : s < t) : Kf M t s = M.F s := if_pos h

lemma Kf_ge (M : Model p Ω) {t s : ℝ≥0} (h : t ≤ s) : Kf M t s = M.F t ⊔ M.G s :=
  if_neg (not_lt.2 h)

lemma Kf_le_F (M : Model p Ω) (hM : M.Standing) (t s : ℝ≥0) : Kf M t s ≤ M.F s := by
  rcases lt_or_ge s t with h | h
  · rw [Kf_lt M h]
  · rw [Kf_ge M h]; exact sup_le (M.F.mono h) (G_le_F M hM s)

lemma Kf_mono (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Monotone (Kf M t) := by
  intro s s' hss'
  rcases lt_or_ge s' t with h' | h'
  · rw [Kf_lt M (lt_of_le_of_lt hss' h'), Kf_lt M h']; exact M.F.mono hss'
  · rw [Kf_ge M h']
    rcases lt_or_ge s t with h | h
    · rw [Kf_lt M h]; exact le_sup_of_le_left (M.F.mono h.le)
    · rw [Kf_ge M h]; exact sup_le_sup le_rfl (M.G.mono hss')

lemma F_le_Kf (M : Model p Ω) {t s : ℝ≥0} (h : t ≤ s) : M.F t ≤ Kf M t s := by
  rw [Kf_ge M h]; exact le_sup_left

lemma G_le_Kf (M : Model p Ω) (hM : M.Standing) (t s : ℝ≥0) : M.G s ≤ Kf M t s := by
  rcases lt_or_ge s t with h | h
  · rw [Kf_lt M h]; exact G_le_F M hM s
  · rw [Kf_ge M h]; exact le_sup_right


theorem incr_K (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : IncrHyp (Kf M t) M.B M.P :=
  { incr_B M hM with
    mono := Kf_mono M hM t
    le := fun s => (Kf_le_F M hM t s).trans (M.F.le s)
    adapt := fun s => (B_measG M hM le_rfl).mono (G_le_Kf M hM t s) le_rfl
    indep := fun u v huv =>
      indep_of_indep_of_le_left ((incr_B M hM).indep u v huv) (Kf_le_F M hM t u) }

/-- The future increments of `B` after `u`. -/
noncomputable def Dfut (M : Model p Ω) (u : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (r : ℝ≥0) => W M (u + r) ω 0 - W M u ω 0) inferInstance

lemma η_measG (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    Measurable[M.G s] (M.η s) :=
  ((hM.μ_adapted s).div (hM.σ_adapted s)).measurable

lemma etaT_measG (M : Model p Ω) (hM : M.Standing) {s u : ℝ≥0} (hsu : s ≤ u) :
    Measurable[M.G u] (etaT M s) :=
  (η_measG M hM (min s p.T)).mono (M.G.mono ((min_le_left _ _).trans hsu)) le_rfl

lemma etaT_measK (M : Model p Ω) (hM : M.Standing) (t s : ℝ≥0) :
    Measurable[Kf M t s] (etaT M s) :=
  (etaT_measG M hM le_rfl).mono (G_le_Kf M hM t s) le_rfl

lemma Zc_measG (M : Model p Ω) (hM : M.Standing) {Ic : ℝ≥0 → Ω → ℝ}
    (hIm : ∀ t, Measurable (Ic t)) (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t)
    {s : ℝ≥0} (hs : s ≤ p.T) : Measurable[M.G s] (Zc M Ic s) := by
  have hnull : ∀ N : Set Ω, MeasurableSet N → M.P N = 0 → MeasurableSet[M.G s] N := by
    intro N hN hN0
    rw [hM.filtG s]
    exact le_sup_right (a := ⨆ r : ℝ≥0, ⨆ (_ : r ≤ s), MeasurableSpace.comap (M.B r) inferInstance)
      _ (MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩)
  have hIG : Measurable[M.G s] (Ic s) :=
    meas_of_ae_eq_nulls (P := M.P) hnull (hIm s) (hM.I_adapted s).measurable (hIe s hs)
  have hAG : Measurable[M.G s] (fun ω => ∫ u in (0 : ℝ)..s.val, etaT M u.toNNReal ω ^ 2) :=
    int_meas (fun u ω => etaT M u ω ^ 2) (fun ω => (etaT_cont M hM ω).pow 2) s
      (fun u hu => (etaT_measG M hM hu).pow_const 2)
  unfold Zc
  exact Real.measurable_exp.comp ((hIG.neg).sub (measurable_const.mul hAG))

lemma Zc_measK (M : Model p Ω) (hM : M.Standing) {Ic : ℝ≥0 → Ω → ℝ}
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t)
    (t : ℝ≥0) {s : ℝ≥0} (hs : s ≤ p.T) : Measurable[Kf M t s] (Zc M Ic s) := by
  rcases lt_or_ge s t with h | h
  · rw [Kf_lt M h]; exact Zc_measF M hM hIa hIm s
  · exact (Zc_measG M hM hIm hIe hs).mono (G_le_Kf M hM t s) le_rfl

/-- **H1 for `K^t`.** -/
theorem H1_K (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] {t : ℝ≥0}
    (htT : t ≤ p.T) (u : ℝ≥0) (Y : Ω → ℝ) (huT : u ≤ p.T) (hY : Measurable[M.F u] Y)
    (hYb : ∃ C, ∀ ω, |Y ω| ≤ C) :
    condExp (Kf M t p.T) M.P Y =ᵐ[M.P] condExp (Kf M t u) M.P Y := by
  obtain ⟨C, hC⟩ := hYb
  have hYm : Measurable Y := hY.mono (M.F.le u) le_rfl
  have hYi : Integrable Y M.P :=
    Integrable.of_bound hYm.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  have hKle : ∀ s, Kf M t s ≤ mΩ := (incr_K M hM t).le
  rcases lt_or_ge u t with h | h
  · -- Y is measurable for both
    have hYK : Measurable[Kf M t u] Y := by rw [Kf_lt M h]; exact hY
    have hYT : Measurable[Kf M t p.T] Y := hYK.mono (Kf_mono M hM t huT) le_rfl
    rw [condExp_of_stronglyMeasurable (hKle _) hYT.stronglyMeasurable hYi,
      condExp_of_stronglyMeasurable (hKle _) hYK.stronglyMeasurable hYi]
  · have hAF : M.F t ⊔ M.G u ≤ M.F u := by rw [← Kf_ge M h]; exact Kf_le_F M hM t u
    have hDle : Dfut M u ≤ mΩ := by
      refine Measurable.comap_le ?_
      refine measurable_pi_lambda _ fun r => ?_
      simp only [W_zero]
      exact (gB_measurable M hM (u + r)).sub (gB_measurable M hM u)
    have hAK : M.F t ⊔ M.G u ≤ Kf M t p.T := by
      rw [Kf_ge M htT]; exact sup_le_sup le_rfl (M.G.mono huT)
    have hnull : ∀ N : Set Ω, MeasurableSet N → M.P N = 0 →
        MeasurableSet[(M.F t ⊔ M.G u) ⊔ Dfut M u] N :=
      fun N hN hN0 => ((le_sup_left : M.F t ≤ M.F t ⊔ M.G u).trans le_sup_left :
        M.F t ≤ (M.F t ⊔ M.G u) ⊔ Dfut M u) _ (null_mem_F M hM t N hN hN0)
    have hKAD : Kf M t p.T ≤ (M.F t ⊔ M.G u) ⊔ Dfut M u := by
      rw [Kf_ge M htT]
      refine sup_le (le_sup_of_le_left le_sup_left) ?_
      rw [hM.filtG p.T]
      refine sup_le (iSup₂_le fun r _ => ?_) (MeasurableSpace.generateFrom_le fun N hN =>
        hnull N hN.1 hN.2)
      refine Measurable.comap_le ?_
      rcases le_or_gt r u with hru | hru
      · exact (B_measG M hM hru).mono (le_sup_of_le_left le_sup_right) le_rfl
      · have hinc : Measurable[(M.F t ⊔ M.G u) ⊔ Dfut M u] (fun ω => gB M r ω - gB M u ω) := by
          have heq : (fun ω => gB M r ω - gB M u ω) =
              (fun f : ℝ≥0 → ℝ => f (r - u)) ∘
                (fun ω (r' : ℝ≥0) => W M (u + r') ω 0 - W M u ω 0) := by
            funext ω
            simp only [Function.comp, W_zero, add_tsub_cancel_of_le hru.le]
          rw [heq]
          exact ((measurable_pi_apply (r - u)).comp (comap_measurable
            (fun ω (r' : ℝ≥0) => W M (u + r') ω 0 - W M u ω 0))).mono
            (le_sup_right : Dfut M u ≤ _) le_rfl
        have hBu : Measurable[(M.F t ⊔ M.G u) ⊔ Dfut M u] (M.B u) :=
          (B_measG M hM le_rfl).mono (le_sup_of_le_left le_sup_right) le_rfl
        refine meas_of_ae_eq_nulls (P := M.P) hnull (B_measurable M hM r) (hBu.add hinc) ?_
        filter_upwards [dB_ae M hM u r] with ω hω
        simp only [StochCalcD3.dB] at hω
        simp only [Pi.add_apply]
        linarith
    rw [Kf_ge M h]
    exact ce_between hAF (M.F.le u) hDle (indep_B_incr M hM u) hAK hKAD hY.stronglyMeasurable hYi

end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem int_mul_ce {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {g X : Ω → ℝ}
    (hg : StronglyMeasurable[m] g) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) (hX : MemLp X 2 P) :
    ∫ ω, g ω * condExp m P X ω ∂P = ∫ ω, g ω * X ω ∂P := by
  have hg2 : MemLp g 2 P := MemLp.of_bound (hg.mono hm).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  calc ∫ ω, g ω * condExp m P X ω ∂P = ∫ ω, condExp m P (fun ω => g ω * X ω) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg (hg2.integrable_mul hX)
          (hX.integrable one_le_two)).symm
    _ = ∫ ω, g ω * X ω ∂P := integral_condExp hm

variable {m : ℝ≥0 → MeasurableSpace Ω}

/-- F-projection of `1_A (θ - f_t)`: `1_A (c - f_t) 1_[t,T)`. -/
theorem proj_tailA (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0) {t : ℝ≥0}
    {A : Set Ω} (hA : MeasurableSet[m t] A) {θ : Lp ℝ 2 P} {c : ℝ × Ω → ℝ}
    (hc : MemLp c 2 (μT P T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hle T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {f : Ω → ℝ} (hf2 : MemLp f 2 P) (hfce : f =ᵐ[P] condExp (m t) P θ) :
    ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hle T)) →
      ∫ z, A.indicator (fun _ => (1 : ℝ)) z.2 * (c z - f z.2) * (1 - ind 0 t z.1) * ψ z
          ∂(μT P T) =
        ∫ z, A.indicator (fun _ => (1 : ℝ)) z.2 * ((θ : Ω → ℝ) z.2 - f z.2) * ψ z ∂(μT P T) := by
  intro ψ hψ hψP
  set ζ1 : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hζ1
  have hζ1m : Measurable[m t] ζ1 := measurable_const.indicator hA
  have hζ1d : Measurable ζ1 := hζ1m.mono (hle t) le_rfl
  have hζ1b : ∀ ω, |ζ1 ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [hζ1, h]
  have hindb : ∀ r, |1 - ind 0 t r| ≤ 1 := fun r => by
    simp only [ind, Set.indicator_apply]; split_ifs <;> simp
  set φ : ℝ≥0 → Ω → ℝ := fun u ω => ζ1 ω * (1 - ind 0 t (u : ℝ)) with hφ
  have hφb : ∀ u ω, |φ u ω| ≤ 1 := fun u ω => by
    simp only [hφ, abs_mul]
    calc |ζ1 ω| * |1 - ind 0 t (u : ℝ)| ≤ 1 * 1 :=
          mul_le_mul (hζ1b ω) (hindb _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hφm : Measurable (fun z : ℝ × Ω => φ z.1.toNNReal z.2) :=
    (hζ1d.comp measurable_snd).mul (measurable_const.sub
      ((ind_meas 0 t).comp (measurable_coe_nnreal_real.comp measurable_fst.real_toNNReal)))
  have hφa : ∀ s, Measurable[m s] (φ s) := by
    intro s
    by_cases hts : t ≤ s
    · exact (hζ1m.mono (hmono hts) le_rfl).mul measurable_const
    · have h1 : ind 0 t (s : ℝ) = 1 := by
        simp only [ind, Set.indicator_apply]
        rw [if_pos ⟨by exact_mod_cast s.2, by exact_mod_cast (not_le.1 hts)⟩]
      have : φ s = fun _ => 0 := funext fun ω => by simp only [hφ, h1, sub_self, mul_zero]
      rw [this]; exact measurable_const
  have hlc : ∀ ω, ∀ᵐ u ∂volume, u ∈ Set.Ioc 0 T.val →
      Tendsto (fun v : ℝ => φ v.toNNReal ω) (𝓝[<] u) (𝓝 (φ u.toNNReal ω)) := by
    intro ω
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (t : ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with u hut hu
    refine tendsto_const_nhds.congr' ?_
    rcases lt_or_gt_of_ne hut with h | h
    · filter_upwards [Ioo_mem_nhdsLT hu.1] with v hv
      have e1 : ind 0 t ((v.toNNReal : ℝ≥0) : ℝ) = 1 := by
        rw [Real.coe_toNNReal _ hv.1.le]
        simp only [ind, Set.indicator_apply]
        rw [if_pos ⟨hv.1.le, hv.2.trans h⟩]
      have e2 : ind 0 t ((u.toNNReal : ℝ≥0) : ℝ) = 1 := by
        rw [Real.coe_toNNReal _ hu.1.le]
        simp only [ind, Set.indicator_apply]
        rw [if_pos ⟨hu.1.le, h⟩]
      simp only [hφ, e1, e2]
    · filter_upwards [Ioo_mem_nhdsLT h] with v hv
      have ht0 : (0 : ℝ) ≤ t := t.2
      have e1 : ind 0 t ((v.toNNReal : ℝ≥0) : ℝ) = 0 := by
        rw [Real.coe_toNNReal _ (ht0.trans hv.1.le)]
        simp only [ind, Set.indicator_apply]
        rw [if_neg (fun hh => absurd hh.2 (not_lt.2 hv.1.le))]
      have e2 : ind 0 t ((u.toNNReal : ℝ≥0) : ℝ) = 0 := by
        rw [Real.coe_toNNReal _ (ht0.trans h.le)]
        simp only [ind, Set.indicator_apply]
        rw [if_neg (fun hh => absurd hh.2 (not_lt.2 h.le))]
      simp only [hφ, e1, e2]
  have hψ1 : MemLp (fun z => ψ z * φ z.1.toNNReal z.2) 2 (μT P T) :=
    hψ.of_le (hψ.aestronglyMeasurable.mul hφm.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hφb _ _))
  have hψ1P := pred_mul hle hmono T hψ hψP zero_le_one hφb hφm hφa hlc hψ1
  have e1 := hproj _ hψ1 hψ1P
  have hfs : MemLp (fun z : ℝ × Ω => f z.2) 2 (μT P T) := by
    unfold μT; exact hf2.comp_snd _
  have hθs : MemLp (fun z : ℝ × Ω => (θ : Ω → ℝ) z.2) 2 (μT P T) := by
    unfold μT; exact (Lp.memLp θ).comp_snd _
  have hφe : ∀ᵐ z ∂(μT P T), φ z.1.toNNReal z.2 = ζ1 z.2 * (1 - ind 0 t z.1) := by
    filter_upwards [ae_fst_Ico (P := P) T] with z hz
    simp only [hφ, Real.coe_toNNReal _ hz.1]
  have hw : MemLp (fun ω => ζ1 ω * ((θ : Ω → ℝ) ω - f ω)) 2 P :=
    ((Lp.memLp θ).sub hf2).of_le_mul (c := 1)
      ((hζ1d.aestronglyMeasurable).mul ((Lp.memLp θ).aestronglyMeasurable.sub
        hf2.aestronglyMeasurable))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, Pi.sub_apply]
        exact mul_le_mul_of_nonneg_right (hζ1b ω) (abs_nonneg _))
  have hwY : ∀ Y : Ω → ℝ, Measurable[m t] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) →
      ∫ ω, ζ1 ω * ((θ : Ω → ℝ) ω - f ω) * Y ω ∂P = 0 := by
    intro Y hY C hC
    have hg : StronglyMeasurable[m t] (fun ω => ζ1 ω * Y ω) := (hζ1m.mul hY).stronglyMeasurable
    have hgb : ∀ ω, |ζ1 ω * Y ω| ≤ 1 * C := fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hζ1b ω) (hC ω) (abs_nonneg _) zero_le_one
    have hg2 : MemLp (fun ω => ζ1 ω * Y ω) 2 P := MemLp.of_bound
      ((hg.mono (hle t)).aestronglyMeasurable) (1 * C)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
    have k1 := int_mul_ce (P := P) (hle t) hg hgb (Lp.memLp θ)
    have k2 : ∫ ω, ζ1 ω * Y ω * f ω ∂P = ∫ ω, ζ1 ω * Y ω * condExp (m t) P θ ω ∂P :=
      integral_congr_ae (hfce.mono fun ω h => by beta_reduce; rw [h])
    have i1 : Integrable (fun ω => ζ1 ω * Y ω * (θ : Ω → ℝ) ω) P := hg2.integrable_mul (Lp.memLp θ)
    have i2 : Integrable (fun ω => ζ1 ω * Y ω * f ω) P := hg2.integrable_mul hf2
    calc ∫ ω, ζ1 ω * ((θ : Ω → ℝ) ω - f ω) * Y ω ∂P
        = ∫ ω, (ζ1 ω * Y ω * (θ : Ω → ℝ) ω - ζ1 ω * Y ω * f ω) ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = 0 := by rw [integral_sub i1 i2, k2, k1, sub_self]
  have e2 := perp_tail hle hmono t hw hwY hψ hψP
  beta_reduce at e2
  have hws := memLp_snd_ind (T := T) hw 0 t
  have i1 : Integrable (fun z => c z * (ψ z * φ z.1.toNNReal z.2)) (μT P T) :=
    hc.integrable_mul hψ1
  have i2 : Integrable (fun z => f z.2 * (ψ z * φ z.1.toNNReal z.2)) (μT P T) :=
    hfs.integrable_mul hψ1
  have i3 : Integrable (fun z => (θ : Ω → ℝ) z.2 * (ψ z * φ z.1.toNNReal z.2)) (μT P T) :=
    hθs.integrable_mul hψ1
  have i4 : Integrable (fun z => ζ1 z.2 * ((θ : Ω → ℝ) z.2 - f z.2) * ind 0 t z.1 * ψ z)
      (μT P T) := hws.integrable_mul hψ
  have hL : ∫ z, ζ1 z.2 * (c z - f z.2) * (1 - ind 0 t z.1) * ψ z ∂(μT P T) =
      ∫ z, c z * (ψ z * φ z.1.toNNReal z.2) ∂(μT P T) -
        ∫ z, f z.2 * (ψ z * φ z.1.toNNReal z.2) ∂(μT P T) := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hφe] with z hz
    simp only [hz]; ring
  have hR : ∫ z, ζ1 z.2 * ((θ : Ω → ℝ) z.2 - f z.2) * ψ z ∂(μT P T) =
      (∫ z, (θ : Ω → ℝ) z.2 * (ψ z * φ z.1.toNNReal z.2) ∂(μT P T) -
        ∫ z, f z.2 * (ψ z * φ z.1.toNNReal z.2) ∂(μT P T)) +
      ∫ z, ζ1 z.2 * ((θ : Ω → ℝ) z.2 - f z.2) * ind 0 t z.1 * ψ z ∂(μT P T) := by
    have i32 : Integrable (fun z => (θ : Ω → ℝ) z.2 * (ψ z * φ z.1.toNNReal z.2) -
        f z.2 * (ψ z * φ z.1.toNNReal z.2)) (μT P T) := i3.sub i2
    rw [← integral_sub i3 i2, ← integral_add i32 i4]
    refine integral_congr_ae ?_
    filter_upwards [hφe] with z hz
    simp only [Pi.add_apply, Pi.sub_apply, hz]; ring
  rw [hL, hR, e2, e1, add_zero]

end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV







end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge









end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}





end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Bayes formula** for `Q = (Z²/c)·P` when `E_P[f | mH] = ψ Z` and `Z` is `mH`-measurable:
`E_Q[f/Z | m] = ψ` for every `m ≤ mH` for which `ψ` is `m`-measurable. -/
theorem bayes_ce (hm : m ≤ mH) (hH : mH ≤ mΩ)
    {D Z f ψ : Ω → ℝ} {c : ℝ} (hc : 0 < c) (hD : ∀ ω, D ω = Z ω ^ 2 / c)
    (hZpos : ∀ ω, 0 < Z ω) (hZm : StronglyMeasurable[mH] Z) (hZ2 : MemLp Z 2 P)
    (hf2 : MemLp f 2 P) (hψm : StronglyMeasurable[m] ψ)
    (hψ : condExp mH P f =ᵐ[P] fun ω => ψ ω * Z ω) [IsFiniteMeasure (Qd P D)] :
    condExp m (Qd P D) (fun ω => f ω / Z ω) =ᵐ[Qd P D] ψ := by
  have hZmeas : Measurable Z := (hZm.mono hH).measurable
  have hDm : Measurable D := by
    have : D = fun ω => Z ω ^ 2 / c := funext hD
    rw [this]; exact (hZmeas.pow_const 2).div_const c
  have hDpos : ∀ ω, 0 < D ω := fun ω => by rw [hD]; exact div_pos (pow_pos (hZpos ω) 2) hc
  have hmΩ : m ≤ mΩ := hm.trans hH
  have hZf : Integrable (fun ω => Z ω * f ω) P := hZ2.integrable_mul hf2
  have hce2 : MemLp (condExp mH P f) 2 P := MemLp.condExp (m := mH) one_le_two hf2
  have hZce : Integrable (fun ω => Z ω * condExp mH P f ω) P := hZ2.integrable_mul hce2
  -- integrability of f/Z under Q
  have hint1 : Integrable (fun ω => f ω / Z ω) (Qd P D) := by
    rw [integrable_Qd_iff hDm hDpos]
    refine (hZf.div_const c).congr (Eventually.of_forall fun ω => ?_)
    have hz : Z ω ≠ 0 := (hZpos ω).ne'
    simp only [hD]
    field_simp
  -- integrability of ψ under Q
  have hint2 : Integrable ψ (Qd P D) := by
    rw [integrable_Qd_iff hDm hDpos]
    refine (hZce.div_const c).congr ?_
    filter_upwards [hψ] with ω hω
    simp only [hD, hω]
    ring
  -- the key pairing: ∫_s Z f = ∫_s Z E[f|mH] for s ∈ mH
  have hpair : ∀ s, MeasurableSet[mH] s →
      ∫ ω in s, Z ω * condExp mH P f ω ∂P = ∫ ω in s, Z ω * f ω ∂P := by
    intro s hs
    have hpull : condExp mH P (Z * f) =ᵐ[P] Z * condExp mH P f :=
      condExp_mul_of_stronglyMeasurable_left hZm hZf (hf2.integrable one_le_two)
    rw [← setIntegral_condExp hH hZf hs]
    refine (setIntegral_congr_ae (hH s hs) ?_).symm
    filter_upwards [hpull] with ω hω _
    exact hω
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmΩ hint1
    (fun s _ _ => hint2.integrableOn) (fun s hs _ => ?_) hψm.aestronglyMeasurable).symm
  have hsΩ : MeasurableSet s := hmΩ s hs
  rw [setIntegral_Qd hDm hDpos _ hsΩ, setIntegral_Qd hDm hDpos _ hsΩ]
  have e1 : ∫ ω in s, D ω * ψ ω ∂P = ∫ ω in s, Z ω * condExp mH P f ω / c ∂P := by
    refine setIntegral_congr_ae hsΩ ?_
    filter_upwards [hψ] with ω hω _
    simp only [hD, hω]
    ring
  have e2 : ∫ ω in s, D ω * (f ω / Z ω) ∂P = ∫ ω in s, Z ω * f ω / c ∂P := by
    refine setIntegral_congr_fun hsΩ fun ω _ => ?_
    have hz : Z ω ≠ 0 := (hZpos ω).ne'
    simp only [hD]
    field_simp
  rw [e1, e2, integral_div, integral_div, hpair s (hm s hs)]

end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma Z_measK (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    {Ic : ℝ≥0 → Ω → ℝ} (hIm : ∀ t, Measurable (Ic t))
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) (t : ℝ≥0) :
    Measurable[Kf M t p.T] (M.Z p.T) := by
  have hnull : ∀ N : Set Ω, MeasurableSet N → M.P N = 0 → MeasurableSet[M.G p.T] N := by
    intro N hN hN0
    rw [hM.filtG p.T]
    exact le_sup_right (a := ⨆ r : ℝ≥0, ⨆ (_ : r ≤ p.T), MeasurableSpace.comap (M.B r) inferInstance)
      _ (MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩)
  have hZm : Measurable (M.Z p.T) := ((h5.1.1 p.T le_rfl).mono (M.F.le p.T)).measurable
  have hG : Measurable[M.G p.T] (M.Z p.T) :=
    meas_of_ae_eq_nulls (P := M.P) hnull hZm (Zc_measG M hM hIm hIe le_rfl)
      (Zc_eq M hIe le_rfl).symm
  exact hG.mono (G_le_Kf M hM t p.T) le_rfl


end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of P8c066573M17 (scratch/probe/slice8c/cuts/r_tce3.lean.src/P8c066573M17.lean): 0/73 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! O7E6 (8c066573 relay 35, O7.6): conclusion of the completeness argument.  Under
`Q2 = (Z_T²/c)·P`, let `g = f/Z_T`.  If `g ⊥_Q2 L∞(G_T)` (`hG`, from `Q2ce` at `t = 0`) and
`g ⊥_Q2 y·ΔB~_cell` for bounded `F_{t_j} ⊔ G_T`-measurable `y` (`hE`, the conclusion of
`StochCalcE5M.E5`), then `E_P[f Z_T ζ e^{i Σ μ_k ΔB~_k}] = 0` for bounded `G_T`-measurable `ζ`
(`StochCalcR1.core` under `Q2`: exponentials of `B~`-grid sums are `L²(Q2)`-limits of constants
plus `F_{t_l} ⊔ G_T`-weighted `B~`-grid sums), hence `f Z_T` is orthogonal to every
`cos/sin ⟪Δ_j, t⟫` (`StochCalcR5.inner_Δ`, `cos (a + b)` split with `a` the `B`-part) and
`StochCalcR2.ae_eq_zero_of_trig` gives `f Z_T = 0`, so `f = 0`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcE6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV Finset
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcE2 StochCalcG4 StochCalcR5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcE6M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! O7HG (8c066573 relay 36): the `hG` input of `StochCalcE6M.E6` from `Q2ce` at `t = 0`.
`F_0` (augmented natural filtration of `(B, B~)` at time `0`) is `P`-trivial since `B_0 = B~_0 = 0`
a.s., so `E_P[f | F_0] = ∫ f = 0`; `Q2ce` at `t = 0` gives `E_Q2[f/Z_T | F_0 ⊔ G_T] = 0`, hence
`∫ f/Z_T · ζ dQ2 = 0` for bounded `G_T`-measurable `ζ`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcHGM

open MeasureTheory ProbabilityTheory Filter HedgePSNV Set
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcZ3
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcHGM

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

/-! O70 support (copied from the accepted cc6d45ce library: StochCalcS2 clR + hasIto_add, StochCalcS3 hasIto_tail,
StochCalcS3M ext_hasIto, StochCalcFe). -/

namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]














end StochCalcS2
namespace StochCalcS3

open EthierKurtz ItoLib StochCalcTC StochCalcS2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcS3
namespace StochCalcS3M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcS3M
namespace StochCalcFe

open Real

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




end line










end StochCalcFe

/-! O7.0 (8c066573 relay 36): `X_t ≠ 0` a.s. in the NON-degenerate model (no `hdeg`, no `QVStatement`):
Ito formula for `f_ε(x) = ½ log(x² + ε)` on `X` frozen at `T` and continued with its drift and
Brownian increments, localized on `σ ≤ Rσ`, `μ ≤ Rμ`; then `μT`-a.e. via Tonelli, and the `hac`
input of `Q2ce`: `a' Xσ + c Xμ = 0 ⇒ a' = -η c`. -/

namespace StochCalcX0

open MeasureTheory ProbabilityTheory Filter Set
open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3 StochCalcS3M StochCalcFe
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




























end StochCalcX0

end StochCalcP6

-- ===== slice of P8c066573M18 (scratch/probe/slice8c/cuts/r_tce3.lean.src/P8c066573M18.lean): 4/23 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! GQ (8c066573 relay 37): the O7.4 chain for a GENERAL `θ = θB + θ⊥` (relay 37 found that
`Q1model`/`Q2ce` assume `θ` is a pure `B`-integral, but the completeness argument applies them to `f`,
which also has a `B~`-part).  `KshiftG`/`Q1coreG`: `Rep θB a` for the `B`-part only, `hproj` for the
full `θ`, and `E[θ - θB | K_T] = 0`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


theorem Q1coreG {mF mK : ℝ≥0 → MeasurableSpace Ω} (hF : IncrHyp mF W P) (hK : IncrHyp mK W P)
    (hKF : ∀ s, mK s ≤ mF s) (T : ℝ≥0)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    {θ θB : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)} (h : Rep hF T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hF.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[mK u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (hac : ∀ᵐ z ∂(μT P T), a z = -(η z.1.toNNReal z.2) * c z)
    {Θ : Lp ℝ 2 P} (hΘ : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θ)
    (hΘB : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θB) (t : ℝ≥0)
    (hΘt : ∀ Y : Ω → ℝ, Measurable[mK t] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) →
      ∫ ω, (Θ : Ω → ℝ) ω * Y ω ∂P = 0) :
    Θ = 0 := by
  exact HedgePSNV.subfiltration_projection_zero hF.mono hF.le hF.adapt hF.indep hF.mem2 hF.mean hF.var hK.mono hK.le hK.adapt hK.indep hK.mem2 hK.mean hK.var hKF T (StochCalcP6.StochCalcO3.μT P T) rfl H1 ((StochCalcP6.StochCalcRU.rep_iff hF T θB a).1 h).1 ((StochCalcP6.StochCalcRU.rep_iff hF T θB a).1 h).2.1 ((StochCalcP6.StochCalcRU.rep_iff hF T θB a).1 h).2.2 hc (fun ψ hψ hm => hproj ψ hψ (by rw [StochCalcP6.StochCalcRU.closure_eL]; exact hm)) hηa hηc hac hΘ hΘB t hΘt



































end StochCalcO3


namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem Q1RG (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    (hC : ContHyp M) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + Kj t ω)
    {θ θB : Lp ℝ 2 M.P} {a : Lp ℝ 2 (μT M.P p.T)} (h : Rep (incr_B M hM) p.T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT M.P p.T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) (incr_B M hM).le p.T)) →
      ∫ z, c z * ψ z ∂(μT M.P p.T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T))
    (hac : ∀ᵐ z ∂(μT M.P p.T), a z = -(etaT M z.1.toNNReal z.2) * c z)
    {t : ℝ≥0} (htT : t ≤ p.T)
    (hperp : condExp (Kf M t p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
      condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω)) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂M.P, (|condExp (M.F t) M.P θ ω| ≤ R ∧ 1 ≤ R * Zc M Ic t ω) →
      condExp (Kf M t p.T) M.P θ ω =
        condExp (M.F t) M.P θ ω * Zc M Ic p.T ω / Zc M Ic t ω := by
  have hF := incr_B M hM
  set f : Ω → ℝ := condExp (M.F t) M.P θ with hfdef
  have hfm : StronglyMeasurable[M.F t] f := stronglyMeasurable_condExp
  have hf2 : MemLp f 2 M.P := (Lp.memLp θ).condExp (by norm_num)
  have hZt : Measurable[M.F t] (Zc M Ic t) := Zc_measF M hM hIa hIm t
  have hZpos : ∀ s ω, 0 < Zc M Ic s ω := fun s ω => Real.exp_pos _
  set A : Set Ω := {ω | |f ω| ≤ R} ∩ {ω | 1 ≤ R * Zc M Ic t ω} with hAdef
  have hA : MeasurableSet[M.F t] A :=
    (measurableSet_le (continuous_abs.measurable.comp hfm.measurable) measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.mul hZt))
  set ζ1 : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hζ1
  have hζ1m : Measurable[M.F t] ζ1 := measurable_const.indicator hA
  have hζ1d : Measurable ζ1 := hζ1m.mono (M.F.le t) le_rfl
  have hζ1b : ∀ ω, |ζ1 ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A <;> simp [hζ1, h]
  set ζ : Ω → ℝ := A.indicator (fun ω => f ω / Zc M Ic t ω) with hζ
  have hζm : Measurable[M.F t] ζ := (hfm.measurable.div hZt).indicator hA
  have hCz : ∀ ω, |ζ ω| ≤ R * R := by
    intro ω
    by_cases hω : ω ∈ A
    · have h1 : |f ω| ≤ R := hω.1
      have h2 : 1 ≤ R * Zc M Ic t ω := hω.2
      rw [hζ, Set.indicator_of_mem hω, abs_div, abs_of_pos (hZpos t ω),
        div_le_iff₀ (hZpos t ω)]
      nlinarith [mul_le_mul_of_nonneg_left h2 hR.le]
    · rw [hζ, Set.indicator_of_notMem hω, abs_zero]; positivity
  have hζZ : ∀ ω, ζ ω * Zc M Ic t ω = ζ1 ω * f ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hζ, hζ1, Set.indicator_of_mem hω]
      rw [one_mul, div_mul_cancel₀ _ (hZpos t ω).ne']
    · simp [hζ, hζ1, Set.indicator_of_notMem hω]
  -- O7.3 instance in `F` with multiplier `ζ`
  have hZK : ∀ s, s ≤ p.T → Measurable[M.F s] (Zc M Ic s) := fun s _ => Zc_measF M hM hIa hIm s
  have hηK : ∀ s, Measurable[M.F s] (etaT M s) := fun s =>
    (η_meas M hM (min s p.T)).measurable.mono (M.F.mono (min_le_left _ _)) le_rfl
  have H1F : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ p.T → Measurable[M.F u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (M.F p.T) M.P Y =ᵐ[M.P] condExp (M.F u) M.P Y := by
    rintro u Y huT hY ⟨C, hC⟩
    have hYi : Integrable Y M.P :=
      Integrable.of_bound (hY.mono (M.F.le u) le_rfl).aestronglyMeasurable C
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
    rw [condExp_of_stronglyMeasurable (M.F.le p.T)
        (hY.mono (M.F.mono huT) le_rfl).stronglyMeasurable hYi,
      condExp_of_stronglyMeasurable (M.F.le u) hY.stronglyMeasurable hYi]
  obtain ⟨hc2, θ2, hθ2, a2, ha2, hrep2, -, hproj2⟩ :=
    zK M hM h5 hC hIc hIa hIm hI0 hIe hKj hKz hF hZK hηK (fun s => le_rfl) H1F htT hζm hCz
  -- the tail `1_A (θ - f_t)`
  have hθ1m : MemLp (fun ω => ζ1 ω * ((θ : Ω → ℝ) ω - f ω)) 2 M.P :=
    ((Lp.memLp θ).sub hf2).of_le_mul (c := 1)
      (hζ1d.aestronglyMeasurable.mul
        ((Lp.memLp θ).aestronglyMeasurable.sub hf2.aestronglyMeasurable))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, Pi.sub_apply]
        exact mul_le_mul_of_nonneg_right (hζ1b ω) (abs_nonneg _))
  have hindb : ∀ r, |1 - ind 0 t r| ≤ 1 := fun r => by
    simp only [ind, Set.indicator_apply]; split_ifs <;> simp
  have hindm : Measurable fun z : ℝ × Ω => 1 - ind 0 t z.1 :=
    measurable_const.sub ((ind_meas 0 t).comp measurable_fst)
  have hb1m : MemLp (fun z : ℝ × Ω => ζ1 z.2 * (a z * (1 - ind 0 t z.1))) 2 (μT M.P p.T) :=
    (Lp.memLp a).of_le_mul (c := 1)
      ((hζ1d.comp measurable_snd).aestronglyMeasurable.mul
        ((Lp.memLp a).aestronglyMeasurable.mul hindm.aestronglyMeasurable))
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        calc |ζ1 z.2| * (|a z| * |1 - ind 0 t z.1|) ≤ 1 * (|a z| * 1) :=
              mul_le_mul (hζ1b _) (mul_le_mul_of_nonneg_left (hindb _) (abs_nonneg _))
                (by positivity) zero_le_one
          _ = 1 * |a z| := by ring)
  set fB : Ω → ℝ := condExp (M.F t) M.P θB with hfBdef
  have hfB2 : MemLp fB 2 M.P := (Lp.memLp θB).condExp (by norm_num)
  have hθ1Bm : MemLp (fun ω => ζ1 ω * ((θB : Ω → ℝ) ω - fB ω)) 2 M.P :=
    ((Lp.memLp θB).sub hfB2).of_le_mul (c := 1)
      (hζ1d.aestronglyMeasurable.mul
        ((Lp.memLp θB).aestronglyMeasurable.sub hfB2.aestronglyMeasurable))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, Pi.sub_apply]
        exact mul_le_mul_of_nonneg_right (hζ1b ω) (abs_nonneg _))
  have hrep1 := rep_zeta_tail hF p.T htT h (θt := hfB2.toLp fB) hfB2.coeFn_toLp hζ1m
    (fun ω => hζ1b ω) (θ' := hθ1Bm.toLp _)
    (by filter_upwards [hθ1Bm.coeFn_toLp, hfB2.coeFn_toLp] with ω h1 h2; rw [h1, h2])
    (b' := hb1m.toLp _) hb1m.coeFn_toLp
  have hrep' := rep_sub hF p.T hrep1 hrep2
  -- the projection `c'`
  have hfs : MemLp (fun z : ℝ × Ω => f z.2) 2 (μT M.P p.T) := by
    unfold μT; exact hf2.comp_snd _
  have hc1 : MemLp (fun z : ℝ × Ω => ζ1 z.2 * (c z - f z.2) * (1 - ind 0 t z.1)) 2
      (μT M.P p.T) :=
    (hc.sub hfs).of_le_mul (c := 1)
      (((hζ1d.comp measurable_snd).aestronglyMeasurable.mul
        (hc.aestronglyMeasurable.sub hfs.aestronglyMeasurable)).mul hindm.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, Pi.sub_apply]
        calc |ζ1 z.2| * |c z - f z.2| * |1 - ind 0 t z.1| ≤ 1 * |c z - f z.2| * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_right (hζ1b _) (abs_nonneg _)) (hindb _)
                (abs_nonneg _) (by positivity)
          _ = 1 * |c z - f z.2| := by ring)
  have hc' : MemLp (fun z : ℝ × Ω => ζ1 z.2 * (c z - f z.2) * (1 - ind 0 t z.1) -
      ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2)) 2 (μT M.P p.T) :=
    hc1.sub hc2
  have hprojc : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) hF.le p.T)) →
      ∫ z, (ζ1 z.2 * (c z - f z.2) * (1 - ind 0 t z.1) -
          ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2)) * ψ z ∂(μT M.P p.T) =
        ∫ z, ((hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) := by
    intro ψ hψ hψP
    have k1 := proj_tailA hF.le hF.mono p.T hA hc hproj hf2 (ae_eq_refl _) ψ hψ hψP
    rw [← hζ1] at k1
    have k2 := hproj2 ψ hψ hψP
    have hθ1s : MemLp (fun z : ℝ × Ω => (hθ1m.toLp _ : Ω → ℝ) z.2) 2 (μT M.P p.T) := by
      unfold μT; exact (Lp.memLp _).comp_snd _
    have hθ2s : MemLp (fun z : ℝ × Ω => (θ2 : Ω → ℝ) z.2) 2 (μT M.P p.T) := by
      unfold μT; exact (Lp.memLp _).comp_snd _
    have hsub : ∀ᵐ z ∂(μT M.P p.T), ((hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) z.2 =
        (hθ1m.toLp _ : Ω → ℝ) z.2 - (θ2 : Ω → ℝ) z.2 := by
      unfold μT
      exact Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_sub _ _)
    have h1e : ∀ᵐ z ∂(μT M.P p.T), (hθ1m.toLp _ : Ω → ℝ) z.2 =
        ζ1 z.2 * ((θ : Ω → ℝ) z.2 - f z.2) := by
      unfold μT
      exact Measure.quasiMeasurePreserving_snd.ae hθ1m.coeFn_toLp
    have k3 : ∫ z, (hθ1m.toLp _ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) =
        ∫ z, ζ1 z.2 * ((θ : Ω → ℝ) z.2 - f z.2) * ψ z ∂(μT M.P p.T) :=
      integral_congr_ae (h1e.mono fun z hz => by simp only [hz])
    have j3 : Integrable (fun z => (hθ1m.toLp _ : Ω → ℝ) z.2 * ψ z) (μT M.P p.T) :=
      hθ1s.integrable_mul hψ
    have j4 : Integrable (fun z => (θ2 : Ω → ℝ) z.2 * ψ z) (μT M.P p.T) :=
      hθ2s.integrable_mul hψ
    have k4 : ∫ z, ((hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) =
        ∫ z, (hθ1m.toLp _ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) -
          ∫ z, (θ2 : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) := by
      rw [← integral_sub j3 j4]
      exact integral_congr_ae (hsub.mono fun z hz => by simp only [hz, sub_mul])
    have j1 : Integrable (fun z => ζ1 z.2 * (c z - f z.2) * (1 - ind 0 t z.1) * ψ z)
        (μT M.P p.T) := hc1.integrable_mul hψ
    have j2 : Integrable (fun z => ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2) *
        ψ z) (μT M.P p.T) := hc2.integrable_mul hψ
    rw [k4, k3, ← k1, ← k2, ← integral_sub j1 j2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only; ring
  have hac' : ∀ᵐ z ∂(μT M.P p.T), ((hb1m.toLp _ - a2 : Lp ℝ 2 (μT M.P p.T)) :
      ℝ × Ω → ℝ) z = -(etaT M z.1.toNNReal z.2) * (ζ1 z.2 * (c z - f z.2) * (1 - ind 0 t z.1) -
        ζ z.2 * (ZT M Ic (max z.1.toNNReal t) z.2 - ZT M Ic t z.2)) := by
    filter_upwards [Lp.coeFn_sub (hb1m.toLp _) a2, hb1m.coeFn_toLp, ha2, hac,
      ae_fst_Ico (P := M.P) p.T] with z e1 e2 e3 e4 e5
    rw [e1, Pi.sub_apply, e2, e3]
    beta_reduce
    rw [e4]
    have hz0 : (0 : ℝ) ≤ z.1 := e5.1
    rcases lt_or_ge z.1 t with hlt | hge
    · have hi : ind 0 t z.1 = 1 := by
        simp only [ind, Set.indicator_apply]; rw [if_pos ⟨hz0, hlt⟩]
      have hmx : max z.1.toNNReal t = t := max_eq_right (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hz0]; exact hlt.le)
      rw [hi, hmx]; ring
    · have hi : ind 0 t z.1 = 0 := by
        simp only [ind, Set.indicator_apply]
        rw [if_neg (fun hh => absurd hh.2 (not_lt.2 hge))]
      have hmx : max z.1.toNNReal t = z.1.toNNReal := max_eq_left (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hz0]; exact hge)
      have hsT : z.1.toNNReal ≤ p.T := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hz0]; exact e5.2.le
      rw [hi, hmx, ZT_of_le M Ic hsT, ZT_of_le M Ic htT]
      linear_combination (etaT M z.1.toNNReal z.2) * hζZ z.2
  -- Θ := E[θ' | K^t_T] is orthogonal to L∞(K^t_t) = L∞(F_t)
  set g1 : Ω → ℝ := fun ω => ζ1 ω * ((θ : Ω → ℝ) ω - f ω) with hg1
  set g2 : Ω → ℝ := fun ω => ζ ω * (Zc M Ic p.T ω - Zc M Ic t ω) with hg2
  have hθ'e : ((hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) =ᵐ[M.P] g1 - g2 := by
    filter_upwards [Lp.coeFn_sub (hθ1m.toLp _) θ2, hθ1m.coeFn_toLp, hθ2] with ω e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3]; rfl
  have hKle : Kf M t p.T ≤ mΩ := (Kf_le_F M hM t p.T).trans (M.F.le p.T)
  have hFK : M.F t ≤ Kf M t p.T := F_le_Kf M htT
  have hZT2 : MemLp (Zc M Ic p.T) 2 M.P := Zc_memLp M h5 hIe
  have hZt2 : MemLp (Zc M Ic t) 2 M.P :=
    (h5.2 t htT).ae_eq (Zc_eq M hIe htT).symm
  have hZd : Measurable (Zc M Ic t) := hZt.mono (M.F.le t) le_rfl
  have hζd : Measurable ζ := hζm.mono (M.F.le t) le_rfl
  have hg2m : MemLp g2 2 M.P :=
    (hZT2.sub hZt2).of_le_mul (c := R * R)
      (hζd.aestronglyMeasurable.mul (hZT2.aestronglyMeasurable.sub hZt2.aestronglyMeasurable))
      (Eventually.of_forall fun ω => by
        rw [hg2, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, Pi.sub_apply]
        exact mul_le_mul_of_nonneg_right (hCz ω) (abs_nonneg _))
  have hΘ2 : MemLp (condExp (Kf M t p.T) M.P (hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P)) 2 M.P :=
    (Lp.memLp _).condExp (by norm_num)
  have hΘt : ∀ Y : Ω → ℝ, Measurable[Kf M t t] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) →
      ∫ ω, (hΘ2.toLp _ : Ω → ℝ) ω * Y ω ∂M.P = 0 := by
    intro Y hY C hC
    rw [Kf_ge M le_rfl, sup_eq_left.2 (G_le_F M hM t)] at hY
    have hYK : StronglyMeasurable[Kf M t p.T] Y :=
      (hY.mono hFK le_rfl).stronglyMeasurable
    have hG1 : StronglyMeasurable[M.F t] (fun ω => Y ω * ζ1 ω) := (hY.mul hζ1m).stronglyMeasurable
    have hG1b : ∀ ω, |Y ω * ζ1 ω| ≤ C * 1 := fun ω => by
      rw [abs_mul, mul_one]
      calc |Y ω| * |ζ1 ω| ≤ |Y ω| * 1 := mul_le_mul_of_nonneg_left (hζ1b ω) (abs_nonneg _)
        _ ≤ C := by rw [mul_one]; exact hC ω
    have hG2 : StronglyMeasurable[M.F t] (fun ω => Y ω * ζ ω) := (hY.mul hζm).stronglyMeasurable
    have hG2b : ∀ ω, |Y ω * ζ ω| ≤ C * (R * R) := fun ω => by
      rw [abs_mul]
      calc |Y ω| * |ζ ω| ≤ |Y ω| * (R * R) := mul_le_mul_of_nonneg_left (hCz ω) (abs_nonneg _)
        _ ≤ C * (R * R) := mul_le_mul_of_nonneg_right (hC ω) (by positivity)
    have hG1m : MemLp (fun ω => Y ω * ζ1 ω) 2 M.P := MemLp.of_bound
      (hG1.mono (M.F.le t)).aestronglyMeasurable (C * 1)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hG1b ω)
    have hG2m : MemLp (fun ω => Y ω * ζ ω) 2 M.P := MemLp.of_bound
      (hG2.mono (M.F.le t)).aestronglyMeasurable (C * (R * R))
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hG2b ω)
    have k1 := int_mul_ce (P := M.P) (M.F.le t) hG1 hG1b (Lp.memLp θ)
    have k2 := int_mul_ce (P := M.P) (M.F.le t) hG2 hG2b hZT2
    have k2' : ∫ ω, Y ω * ζ ω * condExp (M.F t) M.P (Zc M Ic p.T) ω ∂M.P =
        ∫ ω, Y ω * ζ ω * Zc M Ic t ω ∂M.P :=
      integral_congr_ae ((Zc_mart M h5 hIe htT).mono fun ω h => by beta_reduce; rw [h])
    have i1 : Integrable (fun ω => Y ω * ζ1 ω * (θ : Ω → ℝ) ω) M.P :=
      hG1m.integrable_mul (Lp.memLp θ)
    have i2 : Integrable (fun ω => Y ω * ζ1 ω * f ω) M.P := hG1m.integrable_mul hf2
    have i3 : Integrable (fun ω => Y ω * ζ ω * Zc M Ic p.T ω) M.P := hG2m.integrable_mul hZT2
    have i4 : Integrable (fun ω => Y ω * ζ ω * Zc M Ic t ω) M.P := hG2m.integrable_mul hZt2
    have i12 : Integrable (fun ω => Y ω * ζ1 ω * (θ : Ω → ℝ) ω - Y ω * ζ1 ω * f ω) M.P :=
      i1.sub i2
    have i34 : Integrable (fun ω => Y ω * ζ ω * Zc M Ic p.T ω - Y ω * ζ ω * Zc M Ic t ω) M.P :=
      i3.sub i4
    calc ∫ ω, (hΘ2.toLp _ : Ω → ℝ) ω * Y ω ∂M.P
        = ∫ ω, Y ω * condExp (Kf M t p.T) M.P (hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) ω ∂M.P :=
          integral_congr_ae (hΘ2.coeFn_toLp.mono fun ω h => by beta_reduce; rw [h]; ring)
      _ = ∫ ω, Y ω * ((hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) ω ∂M.P :=
          int_mul_ce hKle hYK hC (Lp.memLp _)
      _ = ∫ ω, ((Y ω * ζ1 ω * (θ : Ω → ℝ) ω - Y ω * ζ1 ω * f ω) -
            (Y ω * ζ ω * Zc M Ic p.T ω - Y ω * ζ ω * Zc M Ic t ω)) ∂M.P := by
          refine integral_congr_ae ?_
          filter_upwards [hθ'e] with ω e1
          rw [e1, Pi.sub_apply, hg1, hg2]; ring
      _ = 0 := by
          rw [integral_sub i12 i34, integral_sub i1 i2, integral_sub i3 i4,
            ← k1, ← k2, k2']
          ring
  have hΘB : (hΘ2.toLp _ : Ω → ℝ) =ᵐ[M.P]
      condExp (Kf M t p.T) M.P (hθ1Bm.toLp _ - θ2 : Lp ℝ 2 M.P) := by
    have hKle' : Kf M t p.T ≤ mΩ := (Kf_le_F M hM t p.T).trans (M.F.le p.T)
    have hFK' : M.F t ≤ Kf M t p.T := (Kf_ge M htT).symm ▸ le_sup_left
    set D : Ω → ℝ := fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω with hDdef
    have hDi : Integrable D M.P := ((Lp.memLp θ).sub (Lp.memLp θB)).integrable one_le_two
    set ED : Ω → ℝ := condExp (M.F t) M.P D with hEDdef
    have hEDi : Integrable ED M.P := integrable_condExp
    have hce0 : condExp (M.F t) M.P D =ᵐ[M.P] fun ω => f ω - fB ω :=
      condExp_sub ((Lp.memLp θ).integrable one_le_two) ((Lp.memLp θB).integrable one_le_two) _
    have hdiff : ((hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) =ᵐ[M.P]
        fun ω => ((hθ1Bm.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) ω + ζ1 ω * (D ω - ED ω) := by
      filter_upwards [Lp.coeFn_sub (hθ1m.toLp _) θ2, Lp.coeFn_sub (hθ1Bm.toLp _) θ2,
        hθ1m.coeFn_toLp, hθ1Bm.coeFn_toLp, hce0] with ω e1 e2 e3 e4 e5
      rw [e1, e2, Pi.sub_apply, Pi.sub_apply, e3, e4]
      have e5' : ED ω = f ω - fB ω := e5
      rw [e5']; simp only [hDdef]; ring
    have hgi : Integrable (fun ω => ζ1 ω * (D ω - ED ω)) M.P :=
      ((hDi.sub hEDi).bdd_mul (c := 1) hζ1d.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hζ1b ω))
    have hBi : Integrable ((hθ1Bm.toLp _ - θ2 : Lp ℝ 2 M.P) : Ω → ℝ) M.P :=
      (Lp.memLp _).integrable one_le_two
    have hζ1K : StronglyMeasurable[Kf M t p.T] ζ1 := (hζ1m.mono hFK' le_rfl).stronglyMeasurable
    have hz0 : condExp (Kf M t p.T) M.P (fun ω => ζ1 ω * (D ω - ED ω)) =ᵐ[M.P] 0 := by
      have k1 : condExp (Kf M t p.T) M.P (fun ω => ζ1 ω * (D ω - ED ω)) =ᵐ[M.P]
          ζ1 * condExp (Kf M t p.T) M.P (fun ω => D ω - ED ω) :=
        condExp_mul_of_stronglyMeasurable_left hζ1K hgi (hDi.sub hEDi)
      have k2 : condExp (Kf M t p.T) M.P (fun ω => D ω - ED ω) =ᵐ[M.P]
          condExp (Kf M t p.T) M.P D - condExp (Kf M t p.T) M.P ED := condExp_sub hDi hEDi _
      have k3 : condExp (Kf M t p.T) M.P ED = ED :=
        condExp_of_stronglyMeasurable hKle' (stronglyMeasurable_condExp.mono hFK') hEDi
      filter_upwards [k1, k2, hperp] with ω e1 e2 e3
      rw [e1, Pi.mul_apply, e2, Pi.sub_apply, k3, Pi.zero_apply]
      have e3' : condExp (Kf M t p.T) M.P D ω = ED ω := e3
      rw [e3', sub_self, mul_zero]
    refine hΘ2.coeFn_toLp.trans ?_
    refine (condExp_congr_ae hdiff).trans ?_
    refine (condExp_add hBi hgi _).trans ?_
    filter_upwards [hz0] with ω e
    rw [Pi.add_apply, e, Pi.zero_apply, add_zero]
  have hΘ0 := Q1coreG hF (incr_K M hM t) (Kf_le_F M hM t) p.T (H1_K M hM htT) hrep' hc' hprojc
    (etaT_measK M hM t) (etaT_cont M hM) hac' hΘ2.coeFn_toLp hΘB t hΘt
  have hz : condExp (Kf M t p.T) M.P (hθ1m.toLp _ - θ2 : Lp ℝ 2 M.P) =ᵐ[M.P] 0 := by
    have := hΘ2.coeFn_toLp
    rw [hΘ0] at this
    exact this.symm.trans (Lp.coeFn_zero _ _ _)
  -- compute E[θ' | K_T]
  have hi1 : Integrable g1 M.P := hθ1m.integrable one_le_two
  have hi2 : Integrable g2 M.P := hg2m.integrable one_le_two
  have hce1 := (condExp_congr_ae (m := Kf M t p.T) hθ'e).trans (condExp_sub hi1 hi2 _)
  have hζ1K : StronglyMeasurable[Kf M t p.T] ζ1 := (hζ1m.mono hFK le_rfl).stronglyMeasurable
  have hdi : Integrable (⇑θ - f) M.P := ((Lp.memLp θ).sub hf2).integrable one_le_two
  have hce3 : condExp (Kf M t p.T) M.P g1 =ᵐ[M.P] ζ1 * condExp (Kf M t p.T) M.P (⇑θ - f) :=
    condExp_mul_of_stronglyMeasurable_left hζ1K hi1 hdi
  have hfi : Integrable f M.P := hf2.integrable one_le_two
  have hce4 : condExp (Kf M t p.T) M.P (⇑θ - f) =ᵐ[M.P]
      condExp (Kf M t p.T) M.P θ - f := by
    refine (condExp_sub ((Lp.memLp θ).integrable one_le_two) hfi _).trans ?_
    rw [condExp_of_stronglyMeasurable hKle (hfm.mono hFK) hfi]
  have hg2K : StronglyMeasurable[Kf M t p.T] g2 :=
    ((hζm.mono hFK le_rfl).mul ((Zc_measK M hM hIa hIm hIe t le_rfl).sub
      (hZt.mono hFK le_rfl))).stronglyMeasurable
  have hce5 : condExp (Kf M t p.T) M.P g2 = g2 := condExp_of_stronglyMeasurable hKle hg2K hi2
  filter_upwards [hz, hce1, hce3, hce4] with ω e0 e1 e3 e4 hω
  have hωA : ω ∈ A := hω
  have hZ := (hZpos t ω).ne'
  rw [e0, Pi.sub_apply, hce5, e3, Pi.mul_apply, e4, Pi.sub_apply] at e1
  have hζ1ω : ζ1 ω = 1 := by simp only [hζ1, Set.indicator_of_mem hωA]
  have hζω : ζ ω = f ω / Zc M Ic t ω := by simp only [hζ, Set.indicator_of_mem hωA]
  have key : f ω / Zc M Ic t ω * Zc M Ic t ω = f ω := div_mul_cancel₀ _ hZ
  rw [eq_div_iff hZ]
  simp only [hg2, hζ1ω, hζω, Pi.zero_apply] at e1
  linear_combination (-(Zc M Ic t ω)) * e1 + (Zc M Ic p.T ω - Zc M Ic t ω) * key

theorem Q1modelG (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    (hC : ContHyp M) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + Kj t ω)
    {θ θB : Lp ℝ 2 M.P} {a : Lp ℝ 2 (μT M.P p.T)} (h : Rep (incr_B M hM) p.T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT M.P p.T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) (incr_B M hM).le p.T)) →
      ∫ z, c z * ψ z ∂(μT M.P p.T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T))
    (hac : ∀ᵐ z ∂(μT M.P p.T), a z = -(etaT M z.1.toNNReal z.2) * c z)
    {t : ℝ≥0} (htT : t ≤ p.T)
    (hperp : condExp (Kf M t p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
      condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω)) :
    condExp (Kf M t p.T) M.P θ =ᵐ[M.P]
      fun ω => condExp (M.F t) M.P θ ω * Zc M Ic p.T ω / Zc M Ic t ω := by
  have hall : ∀ᵐ ω ∂M.P, ∀ n : ℕ, (|condExp (M.F t) M.P θ ω| ≤ ((n : ℝ) + 1) ∧
      1 ≤ ((n : ℝ) + 1) * Zc M Ic t ω) →
      condExp (Kf M t p.T) M.P θ ω =
        condExp (M.F t) M.P θ ω * Zc M Ic p.T ω / Zc M Ic t ω :=
    ae_all_iff.2 fun n => Q1RG M hM h5 hC hIc hIa hIm hI0 hIe hKj hKz h hc hproj hac htT hperp
      (R := (n : ℝ) + 1) (by positivity)
  filter_upwards [hall] with ω hω
  obtain ⟨n, hn⟩ := exists_nat_gt (max |condExp (M.F t) M.P θ ω| (1 / Zc M Ic t ω))
  have hZ : 0 < Zc M Ic t ω := Real.exp_pos _
  refine hω n ⟨?_, ?_⟩
  · linarith [le_max_left |condExp (M.F t) M.P θ ω| (1 / Zc M Ic t ω)]
  · have h1 : 1 / Zc M Ic t ω < (n : ℝ) + 1 := by
      linarith [le_max_right |condExp (M.F t) M.P θ ω| (1 / Zc M Ic t ω)]
    rw [div_lt_iff₀ hZ] at h1
    linarith

end StochCalcQ1M

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem Q2ceG (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    (hC : ContHyp M) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + Kj t ω)
    {θ θB : Lp ℝ 2 M.P} {a : Lp ℝ 2 (μT M.P p.T)} (h : Rep (incr_B M hM) p.T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT M.P p.T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) (incr_B M hM).le p.T)) →
      ∫ z, c z * ψ z ∂(μT M.P p.T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T))
    (hac : ∀ᵐ z ∂(μT M.P p.T), a z = -(etaT M z.1.toNNReal z.2) * c z)
    {t : ℝ≥0} (htT : t ≤ p.T)
    (hperp : condExp (Kf M t p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
      condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω)) {cc : ℝ} (hcc : 0 < cc)
    [IsFiniteMeasure (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)] :
    condExp (M.F t ⊔ M.G p.T) (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)
        (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Qd M.P fun ω => M.Z p.T ω ^ 2 / cc]
      (fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω) ∧
    condExp (M.F t) (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)
        (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Qd M.P fun ω => M.Z p.T ω ^ 2 / cc]
      (fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω) := by
  have hQ1 := StochCalcQ1M.Q1modelG M hM h5 hC hIc hIa hIm hI0 hIe hKj hKz h hc hproj hac htT hperp
  have hKe : Kf M t p.T = M.F t ⊔ M.G p.T := Kf_ge M htT
  have hH : Kf M t p.T ≤ mΩ := (Kf_le_F M hM t p.T).trans (M.F.le p.T)
  have hFK : M.F t ≤ Kf M t p.T := by rw [hKe]; exact le_sup_left
  have hZpos : ∀ ω, 0 < M.Z p.T ω := fun ω => Real.exp_pos _
  have hZm : StronglyMeasurable[Kf M t p.T] (M.Z p.T) :=
    (Z_measK M hM h5 hIm hIe t).stronglyMeasurable
  have hψF : Measurable[M.F t] (fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω) :=
    stronglyMeasurable_condExp.measurable.div (Zc_measF M hM hIa hIm t)
  have hψ : condExp (Kf M t p.T) M.P (θ : Ω → ℝ) =ᵐ[M.P]
      fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω * M.Z p.T ω := by
    filter_upwards [hQ1, Zc_eq M hIe le_rfl] with ω h1 h2
    rw [h1, h2]; ring
  have hZ2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have hf2 : MemLp (θ : Ω → ℝ) 2 M.P := Lp.memLp θ
  have e1 := bayes_ce (m := Kf M t p.T) (mH := Kf M t p.T) le_rfl hH hcc (fun _ => rfl) hZpos hZm
    hZ2 hf2 (hψF.mono hFK le_rfl).stronglyMeasurable hψ
  have e2 := bayes_ce (m := M.F t) (mH := Kf M t p.T) hFK hH hcc (fun _ => rfl) hZpos hZm
    hZ2 hf2 hψF.stronglyMeasurable hψ
  rw [hKe] at e1
  exact ⟨e1, e2⟩

end StochCalcQ2M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! G3/G5 (8c066573 relay 38).  G5: `O6_modelP` = `O6_model` also exporting that `a'` is
predictable (in the closure of the elementaries).  G3: for `θ` in the closure of the elementary
`B~`-integrals, `E[θ | F_t ⊔ G_T] = E[θ | F_t]` (the `B~` increments after `u` are independent of
`F_u ⊔ G_T`). -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcO6M

namespace StochCalcG3

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m1 m2 mG n : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcG3

namespace StochCalcG3M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcKF StochCalcSteinM
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcG3M


namespace StochCalcG4

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]





variable {mF : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcG4


namespace StochCalcG4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcG3M StochCalcG4 StochCalcR1M StochCalcR4 StochCalcR7 StochCalcD2
  StochCalcD3 StochCalcTiltM
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcG4M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! HC (8c066573 relay 38): **M6 hcomp** (completeness) from O3_model, O6_modelP, O70, G4, G3, Z2, Z3,
Q2ceG, E5, hG_glue, E6.  `ContHyp M` (conj 3 of platform theorem 1c98c8e0) is kept as a hypothesis. -/

namespace StochCalcHC

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcO3 StochCalcO3M StochCalcO6M StochCalcG3M StochCalcG4 StochCalcG4M StochCalcKF
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcHC

end StochCalcP6

-- ===== slice of RUb (scratch/probe/slice8c/cuts/r_tce3.lean.src/RUb.lean): 1/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}














end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2 StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `Q2ceG` with Elem-free hypotheses (cut statement for the K4 package). -/
theorem Q2ceGU (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    (hC : ContHyp M) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + Kj t ω)
    {θ θB : Lp ℝ 2 M.P} {a : Lp ℝ 2 (μT M.P p.T)} (h : RepU M.F M.B M.P p.T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT M.P p.T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
      hψ.toLp ψ ∈ closure (Submodule.span ℝ (SE M.F M.P p.T) : Set (Lp ℝ 2 (μT M.P p.T))) →
      ∫ z, c z * ψ z ∂(μT M.P p.T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T))
    (hac : ∀ᵐ z ∂(μT M.P p.T), a z = -(etaT M z.1.toNNReal z.2) * c z)
    {t : ℝ≥0} (htT : t ≤ p.T)
    (hperp : condExp (M.F t ⊔ M.G p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
      condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω)) {cc : ℝ} (hcc : 0 < cc)
    [IsFiniteMeasure (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)] :
    condExp (M.F t ⊔ M.G p.T) (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)
        (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Qd M.P fun ω => M.Z p.T ω ^ 2 / cc]
      (fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω) ∧
    condExp (M.F t) (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)
        (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Qd M.P fun ω => M.Z p.T ω ^ 2 / cc]
      (fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω) := by
  have hB := incr_B M hM
  refine StochCalcQ2M.Q2ceG M hM h5 hC hIc hIa hIm hI0 hIe hKj hKz ((rep_iff hB p.T θB a).2 h) hc
    (fun ψ hψ hm => hproj ψ hψ (by rwa [closure_eL] at hm)) hac htT ?_ hcc
  rw [Kf_ge M htT]
  exact hperp




end StochCalcQ2U

end StochCalcP6

-- ===== slice of __current__ (scratch/probe/slice8c/cuts/r_tce3.lean.src/__current__.lean): 0/98 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! K2d (relay 3): the finite-grid lower bound under `P^M`, tests `D0 = Z_T - 1`, `D1 = Z_T S`. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK2

/-! K2e (relay 3): the grid weights `Y = a·ĉ_t / max(Z^M_t, ε)` and the bracket bound. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcK2

/-! K2f (relay 3): `ε ↓ 0` in the grid bound; `Z^M_t > 0` `P^M`-a.s. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcK2

/-! K2g (relay 3): `G(u) = E_P[Z_u/Z^M_u δ_u²]`, `G` monotone and bounded. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcK2

/-! K2h (relay 3): Riemann sums and the assembled lower bound K2. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2

/-! K3H (8c066573 relay 11): abstract Hilbert-space glue for the upper bound K3 of HedgePSNV.theorem_1_ii.
E = L²(F_T, P), one = 1, z = Z_T, h = H, A = admissible gains {χ_T}, N = span{Z_T γ ξ_k} (B̃-part of the
dual space).  Completeness `hcomp` (f ⊥ 1, A, N ⇒ f = 0) is the martingale-representation input. -/

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace StochCalcK3H

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]





section Fn

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]



end Fn

end StochCalcK3H

/-! K3M0 (8c066573 relay 11): model-level glue.  `HedgePSNV.theorem_1_ii_upper_bound`'s conclusion from the
obligations M1-M6 of scratch/decomp/8c066573.K3plan.md, stated on `P` (F_T-measurable functions), via
`StochCalcK3H.fn_upper` on `P.trim (F_T ≤ m)`.  Append after K3H.lean (needs Definitions.Def_HedgePSNV_Hedging). -/

namespace StochCalcK3M0

open MeasureTheory ProbabilityTheory HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcK3M0
/-! K3M1 (8c066573 relay 12): the easy obligations of `StochCalcK3M0.K3_of_obl`:
`A_X` contains `0` and is closed under `+` and scalar multiples (linearity of the Ito relation and
of `IsMartingaleOn`), `Z_T`/`H` measurability and `L²`, `E Z_T = 1`, `1 < E Z_T²`, `V0 = E[H Z_T]`,
`E[Z_T χ_T] = 0`.  `K3_of_N` is then K3 from the `N`-class obligations, `hcomp` (M6) and `hbd` (M5).
Append after K3H + K3M0_tail (on top of the K2 dev chain probe/8c066573_K2h.lean). -/

namespace StochCalcK3M1

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]













variable {p : Params}









end StochCalcK3M1
/-! K3M2 (8c066573 relay 12): the class `N` of `Z_T`-weighted `B~`-grid sums
`n = Z_T * Σ_{k<n} Y_k ξ(t_k, t_{k+1})` (uniform grid `t_k = k T / n` of K2, `Y_k` bounded
`F_{t_k}`-measurable) and its obligations in `StochCalcK3M1.K3_of_N`: `L²`, `F_T`-measurability,
`0`, closure under `+` (common refinement `n * n'`) and scalar multiples, orthogonality to the
gains `χ_T` (under `P^M`), to `1` and to `Z_T`.  `K3_of_M56` = K3 from M5 (`hbd`) and M6 (`hcomp`)
for this class.  Append after K3M1_tail. -/

namespace StochCalcK3M2

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


















end StochCalcK3M2
/-! K3M5 (8c066573 relay 13): obligation M5 of `StochCalcK3M2.K3_of_M56`.  For
`f = Z_T * Σ_k Y_k ξ_k` in the grid class `NC`, `(E_P[H f])² ≤ Ψ E_P[f²]` with
`Ψ = ∫_0^T fK` (= the target `∫ E_P[(Z_u/Z^M_u) δ_u²] du`).  Proof: Stein under `P^M` turns
`E_P[H f]` into `Σ (T/n) E^M[a c^M_{t_k} Y_k]`; the tower property turns `E_P[f²]` into
`Σ (T/n) E^M[Z^M_{t_k} Y_k²]`; a weighted AM-GM bound for every `λ > 0` gives Cauchy-Schwarz;
the left Riemann sum of the monotone `fK` is below its integral.  `K3_of_M6` = K3 from M6
(`hcomp`) only.  Append after K3M2_tail. -/

namespace StochCalcK3M5

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2 StochCalcK3M2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcK3M5

/-! K3G (8c066573 relay 39): K3 (upper bound of (21)) from `K3_of_M6` + `hcomp`, with the
continuity hypothesis `ContHyp M` (conjunct 3 of platform theorem 1c98c8e0) kept explicit. -/

namespace StochCalcK3G

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK3G

end StochCalcP6


open MeasureTheory ProbabilityTheory EthierKurtz in
open scoped NNReal in
open Classical in
theorem solution {p : HedgePSNV.Params} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5) (W : ℝ≥0 → Ω → SDEState 2)
    (hW : ∀ t ω, W t ω = WithLp.toLp 2
      ![if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.B t ω,
        if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.Bt t ω])
    (hC : ∀ H : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable[completedBrownianPast M.P W (fun _ => 0) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
        (∀ t, Measurable[completedBrownianPast M.P W (fun _ => 0) t] (Jc t)) ∧
        (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
        HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
          (fun s ω => W s ω 0) H Jc)
    {Ic : ℝ≥0 → Ω → ℝ} (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P W (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) (Z : ℝ≥0 → Ω → ℝ)
    (hZ : ∀ s ω, Z s ω =
      Real.exp (-(Ic s ω) - (1 / 2) * ∫ u in (0 : ℝ)..s.val, M.η (min u.toNNReal p.T) ω ^ 2))
    {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) (fun s ω => -(Z s ω * M.η (min s p.T) ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Z t ω = 1 + Kj t ω)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) p.T)).prod M.P)
    {θ θB : Lp ℝ 2 M.P} {a : Lp ℝ 2 μ}
    (hθB : θB ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 M.P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
      ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
      ∃ h : MemLp (fun ω => Y ω * (M.B v ω - M.B u ω)) 2 M.P, g = h.toLp _} : Set (Lp ℝ 2 M.P)))
    (ha : a ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
      ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
      ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
        g = h.toLp _} : Set (Lp ℝ 2 μ)))
    (hθBa : ∀ u v : ℝ≥0, u ≤ v → v ≤ p.T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
      (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
      ∫ ω, (θB : Ω → ℝ) ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
        ∫ z, (a : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 μ)
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 μ,
      hψ.toLp ψ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
        ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
        ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
          g = h.toLp _} : Set (Lp ℝ 2 μ)) →
      ∫ z, c z * ψ z ∂μ = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂μ)
    (hac : ∀ᵐ z ∂μ, a z = -(M.η (min z.1.toNNReal p.T) z.2) * c z)
    {t : ℝ≥0} (htT : t ≤ p.T)
    (hperp : condExp (M.F t ⊔ M.G p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
      condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω)) {cc : ℝ} (hcc : 0 < cc)
    (Q : Measure Ω) (hQ : Q = M.P.withDensity fun ω => ENNReal.ofReal (M.Z p.T ω ^ 2 / cc))
    [IsFiniteMeasure Q] :
    condExp (M.F t ⊔ M.G p.T) Q (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Q]
      (fun ω => condExp (M.F t) M.P θ ω / Z t ω) ∧
    condExp (M.F t) Q (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Q]
      (fun ω => condExp (M.F t) M.P θ ω / Z t ω) := by
  obtain rfl : W = StochCalcBr.W M := funext fun t => funext fun ω => hW t ω
  obtain rfl : Z = StochCalcP6.StochCalcZ3.Zc M Ic := funext fun s => funext fun ω => hZ s ω
  subst hμ hQ
  exact StochCalcP6.StochCalcQ2U.Q2ceGU M hM h5 hC hIc hIa hIm hI0 hIe hKj hKz ⟨hθB, ha, hθBa⟩ hc hproj
    hac htT hperp hcc
