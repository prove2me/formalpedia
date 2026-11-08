-- Prove2me | solution 1 for HedgePSNV.girsanov_density_terminal_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:42:05.992436+00:00
-- url     : https://prove2.me/submissions/8428260d-cf84-4011-a319-af4ecc5ee4a4

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Theorems.Thm_HedgePSNV_bounded_integrand_ito_representation
import Theorems.Thm_HedgePSNV_ito_integral_dyadic_locality
import Theorems.Thm_HedgePSNV_stopped_integrand_representation

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false





-- ===== slice of Solutions.Sol_pv_1558a108 (probe/slice8c/cuts/r_z7.lean.src/Solutions.Sol_pv_1558a108.lean): 22/153 top-level decls kept =====

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






theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]


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

/-- Locality of the Ito integral: integrands agreeing on the dyadic grid of `[0, s]` on an event
give integrals agreeing a.e. on that event at time `s`. -/
theorem hasBrownianItoIntegral_eq_on {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H H' J J' : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s))
    (hH'c : ∀ ω, Continuous fun s => H' s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H' J') (s : ℝ≥0) (E : Set Ω)
    (hE : ∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N → H (dyTime s N i) ω = H' (dyTime s N i) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω := by
  exact HedgePSNV.ito_integral_dyadic_locality hW x₀ j hHm hHc hH'm hH'c hJ hJ' s E hE










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


-- ===== slice of P8c066573M16 (probe/slice8c/cuts/r_z7.lean.src/P8c066573M16.lean): 117/865 top-level decls kept =====

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

/-- Hitting time of `{R ≤ |x|}` on `[0,T]`, equal to `T` if the set is not hit. -/
noncomputable def hitR (X : ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf ({v | v ≤ T ∧ R ≤ |X v ω|} ∪ {T})

lemma hitR_le (X : ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω) : hitR X R T ω ≤ T :=
  csInf_le (OrderBot.bddBelow _) (Or.inr rfl)

lemma hitR_le_of {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {T : ℝ≥0} {ω : Ω} {v : ℝ≥0} (hvT : v ≤ T)
    (hv : R ≤ |X v ω|) : hitR X R T ω ≤ v :=
  csInf_le (OrderBot.bddBelow _) (Or.inl ⟨hvT, hv⟩)

lemma hitR_mem {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun v => X v ω) (R : ℝ) (T : ℝ≥0)
    (ω : Ω) : hitR X R T ω ∈ ({v | v ≤ T ∧ R ≤ |X v ω|} ∪ {T}) := by
  refine IsClosed.csInf_mem ?_ ⟨T, Or.inr rfl⟩ (OrderBot.bddBelow _)
  refine IsClosed.union ?_ isClosed_singleton
  exact isClosed_le continuous_id continuous_const |>.inter
    (isClosed_le continuous_const (hc ω).abs)

/-- Before the hitting time the process is strictly inside. -/
lemma abs_lt_of_lt_hitR {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {T : ℝ≥0} {ω : Ω} {w : ℝ≥0}
    (hw : w < hitR X R T ω) : |X w ω| < R := by
  by_contra h
  exact absurd (hitR_le_of ((hw.le.trans (hitR_le X R T ω))) (not_lt.1 h)) (not_le.2 hw)

lemma hitR_le_iff {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun v => X v ω) (R : ℝ) (T : ℝ≥0)
    (ω : Ω) {u : ℝ≥0} (hu : u < T) :
    hitR X R T ω ≤ u ↔ ∃ v, v ≤ u ∧ R ≤ |X v ω| := by
  constructor
  · intro h
    rcases hitR_mem hc R T ω with hm | hm
    · exact ⟨_, h, hm.2⟩
    · rw [Set.mem_singleton_iff] at hm
      exact absurd (hm ▸ h) (not_le.2 hu)
  · rintro ⟨v, hvu, hv⟩
    exact (hitR_le_of (hvu.trans hu.le) hv).trans hvu

/-- The set "the closed set `{R ≤ |x|}` is hit by time `u`" via countably many times
`min q⁺ u`, `q ∈ ℚ`. -/
lemma hit_set_eq {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun v => X v ω) (R : ℝ) (u : ℝ≥0) :
    {ω | ∃ v, v ≤ u ∧ R ≤ |X v ω|} =
      ⋂ k : ℕ, ⋃ q : ℚ, {ω | R - 1 / ((k : ℝ) + 1) < |X (min (Real.toNNReal q) u) ω|} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · rintro ⟨v, hvu, hv⟩ k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hcv := ((hc ω).abs).continuousAt (x := v)
    rw [Metric.continuousAt_iff] at hcv
    obtain ⟨δ, hδ, hδv⟩ := hcv _ hε
    have key : ∀ w : ℝ≥0, dist w v < δ → R - 1 / ((k : ℝ) + 1) < |X w ω| := by
      intro w hw
      have := hδv hw
      rw [Real.dist_eq] at this
      have h2 := (abs_lt.1 this).1
      linarith
    rcases eq_or_lt_of_le hvu with hvu' | hvu'
    · obtain ⟨n, hn⟩ := exists_nat_ge (u : ℝ)
      refine ⟨n, key _ ?_⟩
      have : min (Real.toNNReal ((n : ℚ) : ℝ)) u = v := by
        rw [hvu', min_eq_right]
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
        exact_mod_cast hn
      rw [this, dist_self]; exact hδ
    · have hlt : (v : ℝ) < min (u : ℝ) ((v : ℝ) + δ) :=
        lt_min (by exact_mod_cast hvu') (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hq0 : (0 : ℝ) ≤ q := v.coe_nonneg.trans hq1.le
      have hqu : Real.toNNReal q ≤ u := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact (hq2.trans_le (min_le_left _ _)).le
      refine ⟨q, key _ ?_⟩
      rw [min_eq_left hqu, NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
      constructor
      · linarith
      · linarith [hq2.trans_le (min_le_right _ _)]
  · intro h
    choose q hq using h
    set w : ℕ → ℝ≥0 := fun k => min (Real.toNNReal (q k)) u with hw
    have hmem : ∀ k, w k ∈ Set.Icc (0 : ℝ≥0) u := fun k => ⟨zero_le, min_le_right _ _⟩
    obtain ⟨v, hv, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    refine ⟨v, hv.2, ?_⟩
    have h1 : Tendsto (fun k => |X (w (φ k)) ω| + 1 / ((φ k : ℝ) + 1)) atTop
        (𝓝 (|X v ω| + 0)) :=
      (((hc ω).abs.tendsto v).comp hlim).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    rw [add_zero] at h1
    refine ge_of_tendsto h1 (Eventually.of_forall fun k => ?_)
    have := hq (φ k)
    simp only [hw] at this ⊢
    linarith

/-- **O2a**: the capped hitting time is a stopping time. -/
theorem hitR_isStopping (F : Filtration ℝ≥0 mΩ) {X : ℝ≥0 → Ω → ℝ}
    (hXa : ∀ u, StronglyMeasurable[F u] (X u)) (hc : ∀ ω, Continuous fun v => X v ω)
    (R : ℝ) (T : ℝ≥0) (u : ℝ≥0) : MeasurableSet[F u] {ω | hitR X R T ω ≤ u} := by
  rcases lt_or_ge u T with hu | hu
  · have e : {ω | hitR X R T ω ≤ u} = {ω | ∃ v, v ≤ u ∧ R ≤ |X v ω|} := by
      ext ω; exact hitR_le_iff hc R T ω hu
    rw [e, hit_set_eq hc R u]
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => ?_
    have hm : Measurable[F u] (X (min (Real.toNNReal q) u)) :=
      ((hXa _).mono (F.mono (min_le_right _ _))).measurable
    exact (continuous_abs.measurable.comp hm) measurableSet_Ioi
  · have e : {ω | hitR X R T ω ≤ u} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (hitR_le X R T ω).trans hu
    rw [e]; exact MeasurableSet.univ


/-- If the path stays strictly inside on `[0,T]`, the hitting time is `T`. -/
lemma hitR_eq_T {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {T : ℝ≥0} {ω : Ω}
    (h : ∀ v, v ≤ T → |X v ω| < R) : hitR X R T ω = T := by
  have e : ({v | v ≤ T ∧ R ≤ |X v ω|} ∪ {T} : Set ℝ≥0) = {T} := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, or_iff_right_iff_imp]
    rintro ⟨hv, hR⟩
    exact absurd (h v hv) (not_lt.2 hR)
  unfold hitR; rw [e, csInf_singleton]

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



lemma coe_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (TL hW T s : Ω → ℝ) =ᵐ[P] fun ω => s.sum (fun i c => c * ifun W i ω) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with ω h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (TL hW T s1) (TL hW T s2), h1, h2] with ω h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [TL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eI hW T i), (memLp_ifun hW i).coeFn_toLp] with ω h h'
    rw [h, Pi.smul_apply, eI, h', smul_eq_mul]

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








lemma ae_fst_Ico (T : ℝ≥0) : ∀ᵐ z ∂(μT P T), z.1 ∈ Set.Ico (0 : ℝ) T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ico)




/-- The predictable subspace of `L²(μT)`. -/
noncomputable def Pred (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (μT P T)) :=
  (LinearMap.range (eL (P := P) hle T)).topologicalClosure

lemma mem_Pred_iff (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (x : Lp ℝ 2 (μT P T)) :
    x ∈ Pred (P := P) hle T ↔ x ∈ closure (Set.range (eL (P := P) hle T)) := by
  rw [Pred, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]




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

/-- Restriction of an elementary process to `[0,s)`. -/
noncomputable def resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) : Elem m T where
  u := i.u
  v := max i.u (min i.v s)
  huv := le_max_left _ _
  hvT := max_le (i.huv.trans i.hvT) ((min_le_left _ _).trans i.hvT)
  Y := i.Y
  hY := i.hY
  C := i.C
  hC := i.hC

lemma ind_resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) (r : ℝ) :
    ind (resI s i).u (resI s i).v r = ind i.u i.v r * ind 0 s r := by
  have hu : (0 : ℝ) ≤ i.u := i.u.2
  simp only [resI, ind, Set.indicator_apply, Set.mem_Ico, NNReal.coe_max, NNReal.coe_min,
    NNReal.coe_zero, lt_max_iff, lt_min_iff]
  by_cases h1 : (i.u : ℝ) ≤ r
  · have h1' : ¬ r < (i.u : ℝ) := not_lt.2 h1
    have h0 : (0 : ℝ) ≤ r := hu.trans h1
    by_cases h2 : r < (i.v : ℝ)
    · by_cases h3 : r < (s : ℝ)
      · simp [h1, h1', h2, h3, h0]
      · simp [h1, h1', h2, h3]
    · simp [h1, h1', h2]
  · simp [h1]

lemma efun_resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) (z : ℝ × Ω) :
    efun (resI s i) z = efun i z * ind 0 s z.1 := by
  simp only [efun, ind_resI]
  show ind i.u i.v z.1 * ind 0 s z.1 * i.Y z.2 = _
  ring

/-- Restriction of a combination. -/
noncomputable def resF {T : ℝ≥0} (s : ℝ≥0) (x : Elem m T →₀ ℝ) : Elem m T →₀ ℝ :=
  Finsupp.mapDomain (resI s) x

lemma comb_resF {T : ℝ≥0} (s : ℝ≥0) (x : Elem m T →₀ ℝ) (z : ℝ × Ω) :
    (resF s x).sum (fun i c => c * efun i z) = x.sum (fun i c => c * efun i z) * ind 0 s z.1 := by
  unfold resF
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [efun_resI, Finsupp.sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma int_ifun_res (hW : IncrHyp m W P) {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) {g : Ω → ℝ}
    (hg : Measurable[m s] g) :
    ∫ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) ∂P = 0 := by
  by_cases hvs : i.v ≤ s
  · have hv : (resI s i).v = i.v := by
      show max i.u (min i.v s) = i.v
      rw [min_eq_left hvs, max_eq_right i.huv]
    have h0 : ∀ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) = 0 := by
      intro ω
      simp only [ifun, hv]
      show g ω * (i.Y ω * (W i.v ω - W i.u ω) - i.Y ω * (W i.v ω - W i.u ω)) = 0
      ring
    simp_rw [h0, integral_zero]
  · push Not at hvs
    have hv : (resI s i).v = max i.u s := by
      show max i.u (min i.v s) = max i.u s
      rw [min_eq_right hvs.le]
    have key : ∀ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) =
        (g ω * i.Y ω) * (W i.v ω - W (max i.u s) ω) := by
      intro ω
      simp only [ifun, hv]
      show g ω * (i.Y ω * (W i.v ω - W i.u ω) - i.Y ω * (W (max i.u s) ω - W i.u ω)) = _
      ring
    simp_rw [key]
    refine int_mul_dW hW (max_le i.huv hvs.le) ?_
    exact (hg.mono (hW.mono (le_max_right _ _)) le_rfl).mul
      (i.hY.mono (hW.mono (le_max_left _ _)) le_rfl)

lemma int_TL_res (hW : IncrHyp m W P) (T : ℝ≥0) (s : ℝ≥0) (x : Elem m T →₀ ℝ) {g : Ω → ℝ}
    (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) :
    ∫ ω, g ω * (TL hW T x ω - TL hW T (resF s x) ω) ∂P = 0 := by
  have e : (fun ω => g ω * (TL hW T x ω - TL hW T (resF s x) ω)) =ᵐ[P]
      fun ω => ∑ i ∈ x.support, x i * (g ω * (ifun W i ω - ifun W (resI s i) ω)) := by
    filter_upwards [coe_TL hW T x, coe_TL hW T (resF s x)] with ω h1 h2
    rw [h1, h2]
    unfold resF
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [Finsupp.sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae e, integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, int_ifun_res hW s i hg, mul_zero]
  · intro i _
    refine Integrable.const_mul ?_ _
    exact hg2.integrable_mul ((memLp_ifun hW i).sub (memLp_ifun hW (resI s i)))

/-- The restricted integrand `a 1_{[0,s)}` as an `L²` element. -/
lemma memLp_res {T : ℝ≥0} {a : ℝ × Ω → ℝ} (ha : MemLp a 2 (μT P T)) (s : ℝ≥0) :
    MemLp (fun z => a z * ind 0 s z.1) 2 (μT P T) := by
  refine ha.of_le (ha.aestronglyMeasurable.mul
    ((ind_meas 0 s).comp measurable_fst).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)

lemma norm_res_sub_le (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (a : Lp ℝ 2 (μT P T)) (s : ℝ≥0)
    (x : Elem m T →₀ ℝ) :
    ‖eL (P := P) hle T (resF s x) - (memLp_res (Lp.memLp a) s).toLp _‖ ≤
      ‖eL (P := P) hle T x - a‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (eL (P := P) hle T (resF s x)) ((memLp_res (Lp.memLp a) s).toLp _),
    Lp.coeFn_sub (eL (P := P) hle T x) a, coe_eL (P := P) hle T (resF s x), coe_eL (P := P) hle T x,
    (memLp_res (Lp.memLp a) s).coeFn_toLp] with z h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, comb_resF, ← sub_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)

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

omit [IsProbabilityMeasure P] in
lemma sq_norm_toLp {μ : Measure (ℝ × Ω)} {F : ℝ × Ω → ℝ} (hF : MemLp F 2 μ) :
    ‖hF.toLp F‖ ^ 2 = ∫ z, F z ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with z h
  rw [h, RCLike.inner_apply', conj_trivial, sq]


/-- **S1**: pairing of `θ = I(a)` with an `m s`-measurable `g` sees only `a 1_{[0,s)}`. -/
theorem S1 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P}
    (hθ : θ ∈ closure (Set.range (TL hW T)))
    {a : Lp ℝ 2 (μT P T)} (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (s : ℝ≥0)
    {g : Ω → ℝ} (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) :
    ⟪θ, hg2.toLp g⟫_ℝ ≤ ‖(memLp_res (Lp.memLp a) s).toLp _‖ * ‖hg2.toLp g‖ := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hθ
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by
    simp_rw [hy]; exact hx
  have hEa := eL_tendsto hW T ha haP hx'
  have hres : Tendsto (fun n => eL (P := P) hW.le T (resF s (y n))) atTop
      (𝓝 ((memLp_res (Lp.memLp a) s).toLp _)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_res_sub_le hW.le a s (y n)) ?_
    exact tendsto_iff_norm_sub_tendsto_zero.1 hEa
  have heq : ∀ n, ⟪TL hW T (y n), hg2.toLp g⟫_ℝ = ⟪TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ := by
    intro n
    have h0 : ⟪TL hW T (y n) - TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ = 0 := by
      rw [L2.inner_def]
      refine (integral_congr_ae ?_).trans (int_TL_res hW T s (y n) hg hg2)
      filter_upwards [Lp.coeFn_sub (TL hW T (y n)) (TL hW T (resF s (y n))), hg2.coeFn_toLp]
        with ω h1 h2
      rw [h1, h2, Pi.sub_apply, RCLike.inner_apply', conj_trivial, mul_comm]
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have hlim1 : Tendsto (fun n => ⟪TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ) atTop
      (𝓝 ⟪θ, hg2.toLp g⟫_ℝ) := by
    simp_rw [← heq]; exact hx'.inner tendsto_const_nhds
  have hlim2 : Tendsto (fun n => ‖eL (P := P) hW.le T (resF s (y n))‖ * ‖hg2.toLp g‖) atTop
      (𝓝 (‖(memLp_res (Lp.memLp a) s).toLp _‖ * ‖hg2.toLp g‖)) :=
    hres.norm.mul_const _
  refine le_of_tendsto_of_tendsto' hlim1 hlim2 fun n => ?_
  rw [← norm_TL hW T]
  exact real_inner_le_norm _ _


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
-- ===== slice of RUmod (probe/slice8c/cuts/r_z7.lean.src/RUmod.lean): 10/17 top-level decls kept =====

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

-- ===== slice of P8c066573M16c (probe/slice8c/cuts/r_z7.lean.src/P8c066573M16c.lean): 122/865 top-level decls kept =====

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

lemma rep_exists (hW : IncrHyp m W P) (T : ℝ≥0) {b : Lp ℝ 2 (μT P T)}
    (hb : b ∈ closure (Set.range (eL (P := P) hW.le T))) : ∃ θ, Rep hW T θ b := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hb
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  have hc : CauchySeq fun n => TL hW T (y n) := by
    have hcu : CauchySeq fun n => eL (P := P) hW.le T (y n) := hx'.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨θ, hθ⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨θ, rep_lim hW T hθ hx'⟩

lemma rep_conv (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {x : ℕ → (Elem m T →₀ ℝ)}
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) :
    Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
  simp_rw [rep_dist hW T h]
  exact hb

lemma rep_unique (hW : IncrHyp m W P) (T : ℝ≥0) {θ θ' : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) (h' : Rep hW T θ' b) : θ = θ' := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.2.1
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  exact tendsto_nhds_unique (rep_conv hW T h hx') (rep_conv hW T h' hx')

lemma rep_norm (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) : ‖θ‖ = ‖b‖ := by
  have := rep_dist hW T h 0
  simpa using this

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

/-- If the integrand vanishes before `s`, the integral is orthogonal to `L²(m s)`. -/
lemma rep_perp (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {s : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), z.1 < (s : ℝ) → b z = 0)
    {g : Ω → ℝ} (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) : ⟪θ, hg2.toLp g⟫_ℝ = 0 := by
  have h0 : (memLp_res (Lp.memLp b) s).toLp _ = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [(memLp_res (Lp.memLp b) s).coeFn_toLp, hv] with z h1 h2
    rw [h1]
    by_cases hz : z.1 < (s : ℝ)
    · simp [h2 hz]
    · simp [ind, Set.indicator_apply, hz]
  have h1 := S1 hW T h.1 h.2.2 h.2.1 s hg hg2
  have h2 := S1 hW T h.1 h.2.2 h.2.1 s (g := -g) (hg.neg : Measurable[m s] (-g)) hg2.neg
  rw [h0, norm_zero, zero_mul] at h1 h2
  rw [MemLp.toLp_neg hg2, inner_neg_right] at h2
  linarith

/-- The indicator of `A` as a real function. -/
noncomputable def oneA (A : Set Ω) (ω : Ω) : ℝ := A.indicator (fun _ => (1 : ℝ)) ω

lemma abs_oneA_le (A : Set Ω) (ω : Ω) : |oneA A ω| ≤ 1 := by
  classical
  unfold oneA; rw [Set.indicator_apply]; split_ifs <;> simp

lemma oneA_univ (ω : Ω) : oneA (Set.univ : Set Ω) ω = 1 := by simp [oneA]

lemma oneA_meas {t : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[m t] A) : Measurable[m t] (oneA A) := by
  unfold oneA; exact measurable_const.indicator hA

lemma univ_meas (t : ℝ≥0) : MeasurableSet[m t] (Set.univ : Set Ω) := @MeasurableSet.univ Ω (m t)

lemma ind_max (u v t : ℝ≥0) (r : ℝ) :
    ind (max u t) (max v t) r = ind u v r * (1 - ind 0 t r) := by
  have hu : (0 : ℝ) ≤ u := u.2
  simp only [ind, Set.indicator_apply, Set.mem_Ico, NNReal.coe_max, NNReal.coe_zero, max_le_iff,
    lt_max_iff]
  by_cases h1 : (u : ℝ) ≤ r
  · by_cases h3 : (t : ℝ) ≤ r
    · have h3' : ¬ r < (t : ℝ) := not_lt.2 h3
      by_cases h2 : r < (v : ℝ)
      · simp [h1, h2, h3, h3']
      · simp [h1, h2, h3, h3']
    · have h3' : r < (t : ℝ) := lt_of_not_ge h3
      have h0 : (0 : ℝ) ≤ r := hu.trans h1
      by_cases h2 : r < (v : ℝ)
      · simp [h1, h2, h3, h3', h0]
      · simp [h1, h2, h3]
  · simp [h1]

lemma abs_one_sub_ind_le (t : ℝ≥0) (r : ℝ) : |1 - ind 0 t r| ≤ 1 := by
  unfold ind; rw [Set.indicator_apply]; split_ifs <;> simp

/-- Tail-and-indicator modification of an elementary process: `1_A Y 1_[max u t, max v t)`. -/
noncomputable def tailI (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (i : Elem m T) : Elem m T where
  u := max i.u t
  v := max i.v t
  huv := max_le_max i.huv le_rfl
  hvT := max_le i.hvT htT
  Y := fun ω => oneA A ω * i.Y ω
  hY := ((oneA_meas hA).mono (hmono (le_max_right _ _)) le_rfl).mul
    (i.hY.mono (hmono (le_max_left _ _)) le_rfl)
  C := i.C
  hC := fun ω => by
    rw [abs_mul]
    calc |oneA A ω| * |i.Y ω| ≤ 1 * |i.Y ω| :=
          mul_le_mul_of_nonneg_right (abs_oneA_le A ω) (abs_nonneg _)
      _ ≤ i.C := by rw [one_mul]; exact i.hC ω

lemma efun_tailI (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (i : Elem m T) (z : ℝ × Ω) :
    efun (tailI hmono htT hA i) z = oneA A z.2 * (efun i z * (1 - ind 0 t z.1)) := by
  show ind (max i.u t) (max i.v t) z.1 * (oneA A z.2 * i.Y z.2) = _
  rw [ind_max]
  simp only [efun]
  ring

lemma ifun_tailI (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (i : Elem m T) (ω : Ω) :
    ifun W (tailI hmono htT hA i) ω = oneA A ω * ifun W (tailI hmono htT (univ_meas t) i) ω := by
  show oneA A ω * i.Y ω * (W (max i.v t) ω - W (max i.u t) ω) =
    oneA A ω * (oneA Set.univ ω * i.Y ω * (W (max i.v t) ω - W (max i.u t) ω))
  rw [oneA_univ]; ring

noncomputable def tailF (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (x : Elem m T →₀ ℝ) : Elem m T →₀ ℝ :=
  Finsupp.mapDomain (tailI hmono htT hA) x

lemma comb_tailF (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (x : Elem m T →₀ ℝ) (z : ℝ × Ω) :
    (tailF hmono htT hA x).sum (fun i c => c * efun i z) =
      oneA A z.2 * (x.sum (fun i c => c * efun i z) * (1 - ind 0 t z.1)) := by
  unfold tailF
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [efun_tailI, Finsupp.sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma icomb_tailF (hmono : Monotone m) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) (x : Elem m T →₀ ℝ) (ω : Ω) :
    (tailF hmono htT hA x).sum (fun i c => c * ifun W i ω) =
      oneA A ω * (tailF hmono htT (univ_meas t) x).sum (fun i c => c * ifun W i ω) := by
  unfold tailF
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [ifun_tailI hmono htT hA, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma tail_eL_le (hW : IncrHyp m W P) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) {b b' : Lp ℝ 2 (μT P T)}
    (hv : ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → b z = 0)
    (hb' : b' =ᵐ[μT P T] fun z => oneA A z.2 * b z) (x : Elem m T →₀ ℝ) :
    ‖eL (P := P) hW.le T (tailF hW.mono htT hA x) - b'‖ ≤ ‖eL (P := P) hW.le T x - b‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (eL (P := P) hW.le T (tailF hW.mono htT hA x)) b',
    Lp.coeFn_sub (eL (P := P) hW.le T x) b, coe_eL (P := P) hW.le T (tailF hW.mono htT hA x),
    coe_eL (P := P) hW.le T x, hb', hv] with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, comb_tailF]
  have hbz : b z - b z * (1 - ind 0 t z.1) = 0 := by
    by_cases hz : z.1 < (t : ℝ)
    · rw [h6 hz]; ring
    · have : ind 0 t z.1 = 0 := by simp [ind, Set.indicator_apply, hz]
      rw [this]; ring
  have key : oneA A z.2 * (x.sum (fun i c => c * efun i z) * (1 - ind 0 t z.1)) -
      oneA A z.2 * b z =
      (oneA A z.2 * (1 - ind 0 t z.1)) * (x.sum (fun i c => c * efun i z) - b z) := by
    linear_combination (-(oneA A z.2)) * hbz
  rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rw [abs_mul]
  exact mul_le_one₀ (abs_oneA_le A z.2) (abs_nonneg _) (abs_one_sub_ind_le t z.1)

lemma tail_TL_le (hW : IncrHyp m W P) {T t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) {θ θ' : Lp ℝ 2 P}
    (hθ' : θ' =ᵐ[P] fun ω => oneA A ω * θ ω) (x : Elem m T →₀ ℝ) :
    ‖TL hW T (tailF hW.mono htT hA x) - θ'‖ ≤
      ‖TL hW T (tailF hW.mono htT (univ_meas t) x) - θ‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (TL hW T (tailF hW.mono htT hA x)) θ',
    Lp.coeFn_sub (TL hW T (tailF hW.mono htT (univ_meas t) x)) θ,
    coe_TL hW T (tailF hW.mono htT hA x), coe_TL hW T (tailF hW.mono htT (univ_meas t) x), hθ']
    with ω h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, icomb_tailF, ← mul_sub, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_oneA_le A ω)

/-- L0 locality: for `A ∈ m t` and an integrand vanishing before `t`, `I(1_A b) = 1_A I(b)`. -/
theorem L0 (hW : IncrHyp m W P) (T : ℝ≥0) {t : ℝ≥0} (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[m t] A) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)} (h : Rep hW T θ b)
    (hv : ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → b z = 0)
    {θ' : Lp ℝ 2 P} (hθ' : θ' =ᵐ[P] fun ω => oneA A ω * θ ω)
    {b' : Lp ℝ 2 (μT P T)} (hb' : b' =ᵐ[μT P T] fun z => oneA A z.2 * b z) :
    Rep hW T θ' b' := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.1
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by simp_rw [hy]; exact hx
  have hE := eL_tendsto hW T h.2.2 h.2.1 hx'
  have hEn : Tendsto (fun n => ‖eL (P := P) hW.le T (y n) - b‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hE
  have hU : Tendsto (fun n => eL (P := P) hW.le T (tailF hW.mono htT (univ_meas t) (y n)))
      atTop (𝓝 b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => tail_eL_le hW htT (univ_meas t) hv ?_ (y n)) hEn
    exact Eventually.of_forall fun z => by simp [oneA_univ]
  have hUT := rep_conv hW T h hU
  have hA1 : Tendsto (fun n => eL (P := P) hW.le T (tailF hW.mono htT hA (y n))) atTop
      (𝓝 b') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => tail_eL_le hW htT hA hv hb' (y n)) hEn
  have hA2 : Tendsto (fun n => TL hW T (tailF hW.mono htT hA (y n))) atTop (𝓝 θ') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => tail_TL_le hW htT hA hθ' (y n))
      ((tendsto_iff_norm_sub_tendsto_zero).1 hUT)
  exact rep_lim hW T hA2 hA1

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/

lemma coeFn_fsum {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*} (S : Finset ι)
    (f : ι → Lp ℝ 2 μ) : ⇑(∑ i ∈ S, f i) =ᵐ[μ] fun x => ∑ i ∈ S, f i x := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp only [Finset.sum_empty]; exact Lp.coeFn_zero ..
  · intro j S hj ih
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ i ∈ S, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hj]

lemma rep_zero (hW : IncrHyp m W P) (T : ℝ≥0) : Rep hW T (0 : Lp ℝ 2 P) (0 : Lp ℝ 2 (μT P T)) :=
  rep_lim hW T (x := fun _ => 0) (by simp only [map_zero]; exact tendsto_const_nhds)
    (by simp only [map_zero]; exact tendsto_const_nhds)

lemma rep_sum (hW : IncrHyp m W P) (T : ℝ≥0) {ι : Type*} (S : Finset ι) {θ : ι → Lp ℝ 2 P}
    {b : ι → Lp ℝ 2 (μT P T)} (h : ∀ i ∈ S, Rep hW T (θ i) (b i)) :
    Rep hW T (∑ i ∈ S, θ i) (∑ i ∈ S, b i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _; simpa using rep_zero hW T
  · intro j S hj ih h
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact rep_add hW T (h j (Finset.mem_insert_self j S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma memLp_oneA_mul {A : Set Ω} (hA : MeasurableSet A) (f : Lp ℝ 2 P) :
    MemLp (fun ω => oneA A ω * f ω) 2 P := by
  have hm : Measurable (oneA A) := by unfold oneA; exact measurable_const.indicator hA
  refine (Lp.memLp f).of_le (hm.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_oneA_le A ω)

lemma memLp_oneA_mulT {T : ℝ≥0} {A : Set Ω} (hA : MeasurableSet A) (f : Lp ℝ 2 (μT P T)) :
    MemLp (fun z : ℝ × Ω => oneA A z.2 * f z) 2 (μT P T) := by
  have hm : Measurable (oneA A) := by unfold oneA; exact measurable_const.indicator hA
  refine (Lp.memLp f).of_le ((hm.comp measurable_snd).aestronglyMeasurable.mul
    (Lp.memLp f).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_oneA_le A z.2)

lemma memLp_tl {T : ℝ≥0} {a : ℝ × Ω → ℝ} (ha : MemLp a 2 (μT P T)) (t : ℝ≥0) :
    MemLp (fun z => a z * (1 - ind 0 t z.1)) 2 (μT P T) := by
  have hm : Measurable fun z : ℝ × Ω => 1 - ind 0 t z.1 :=
    measurable_const.sub ((ind_meas 0 t).comp measurable_fst)
  refine ha.of_le (ha.aestronglyMeasurable.mul hm.aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_one_sub_ind_le _ _)

lemma res_mem (hW : IncrHyp m W P) (T : ℝ≥0) {a : Lp ℝ 2 (μT P T)}
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (s : ℝ≥0) :
    (memLp_res (Lp.memLp a) s).toLp _ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 haP
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 a) := by
    simp_rw [hy]; exact hx
  have hres : Tendsto (fun n => eL (P := P) hW.le T (resF s (y n))) atTop
      (𝓝 ((memLp_res (Lp.memLp a) s).toLp _)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_res_sub_le hW.le a s (y n))
      ((tendsto_iff_norm_sub_tendsto_zero).1 hx')
  exact mem_closure_of_tendsto hres (Eventually.of_forall fun n => ⟨_, rfl⟩)

lemma tl_mem (hW : IncrHyp m W P) (T : ℝ≥0) {a : Lp ℝ 2 (μT P T)}
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (t : ℝ≥0) :
    (memLp_tl (Lp.memLp a) t).toLp _ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
  have e : (memLp_tl (Lp.memLp a) t).toLp _ = a - (memLp_res (Lp.memLp a) t).toLp _ := by
    refine Lp.ext ?_
    filter_upwards [(memLp_tl (Lp.memLp a) t).coeFn_toLp,
      Lp.coeFn_sub a ((memLp_res (Lp.memLp a) t).toLp _),
      (memLp_res (Lp.memLp a) t).coeFn_toLp] with z h1 h2 h3
    simp only [h1, h2, Pi.sub_apply, h3]
    ring
  rw [e]
  exact (mem_Pred_iff hW.le T _).1 ((Pred (P := P) hW.le T).sub_mem
    ((mem_Pred_iff hW.le T a).2 haP) ((mem_Pred_iff hW.le T _).2 (res_mem hW T haP t)))

lemma rep_perp_int (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {s : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), z.1 < (s : ℝ) → b z = 0)
    {g : Ω → ℝ} (hg : Measurable[m s] g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, θ ω * g ω ∂P = 0 := by
  have hg2 : MemLp g 2 P := MemLp.of_bound (hg.mono (hW.le s) le_rfl).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have h0 := rep_perp hW T h hv hg hg2
  rw [L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hg2.coeFn_toLp] with ω h1
  rw [h1, RCLike.inner_apply', conj_trivial]

lemma tl_vanish {T : ℝ≥0} (a : Lp ℝ 2 (μT P T)) (t : ℝ≥0) :
    ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → ((memLp_tl (Lp.memLp a) t).toLp _ : ℝ × Ω → ℝ) z = 0 := by
  filter_upwards [(memLp_tl (Lp.memLp a) t).coeFn_toLp, ae_fst_Ico (P := P) T] with z h1 h2 hz
  rw [h1]
  have : ind 0 t z.1 = 1 := by simp [ind, Set.indicator_apply, h2.1, hz]
  simp [this]


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


lemma eq_meas_of_stop (hmono : Monotone m) {τ : Ω → ℝ≥0} (S : Finset ℝ≥0) (hS : ∀ ω, τ ω ∈ S)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) (t : ℝ≥0) :
    MeasurableSet[m t] {ω | τ ω = t} := by
  classical
  have e : {ω | τ ω = t} = {ω | τ ω ≤ t} \ ⋃ s ∈ S.filter (fun s => s < t), {ω | τ ω ≤ s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro e
      refine ⟨e.le, ?_⟩
      rintro ⟨s, ⟨_, hs⟩, h⟩
      exact absurd (lt_of_le_of_lt h hs) (by rw [e]; exact lt_irrefl _)
    · rintro ⟨h1, h2⟩
      by_contra hne
      exact h2 ⟨τ ω, ⟨hS ω, lt_of_le_of_ne h1 hne⟩, le_rfl⟩
  rw [e]
  exact (hτ t).diff (Finset.measurableSet_biUnion _ fun s hs =>
    hmono (Finset.mem_filter.1 hs).2.le _ (hτ s))

lemma ae_ne_graph (T : ℝ≥0) {τ : Ω → ℝ≥0} (hτm : Measurable τ) :
    ∀ᵐ z ∂(μT P T), z.1 ≠ (τ z.2 : ℝ) := by
  have hp : MeasurableSet {z : ℝ × Ω | z.1 ≠ (τ z.2 : ℝ)} :=
    (measurableSet_eq_fun measurable_fst (hτm.comp measurable_snd).coe_nnreal_real).compl
  have h2 : ∀ᵐ z ∂(P.prod (volume.restrict (Set.Ico (0 : ℝ) T))),
      z.swap.1 ≠ (τ z.swap.2 : ℝ) := by
    refine (Measure.ae_prod_iff_ae_ae (measurable_swap hp)).2 (Eventually.of_forall fun ω => ?_)
    refine ae_restrict_of_ae ?_
    have : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ (τ ω : ℝ) := by
      rw [ae_iff]; simp
    exact this
  unfold μT
  rw [← Measure.prod_swap, ae_map_iff measurable_swap.aemeasurable hp]
  exact h2

/-- Dyadic ceiling capped at `T`. -/
noncomputable def gc (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  min T ((⌈(x : ℝ) * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n)

/-- Its (finite) value set. -/
noncomputable def gcS (T : ℝ≥0) (n : ℕ) : Finset ℝ≥0 :=
  (Finset.range (⌈(T : ℝ) * 2 ^ n⌉₊ + 1)).image (fun k : ℕ => min T ((k : ℝ≥0) / 2 ^ n))

lemma gc_real (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) :
    (gc T n x : ℝ) = min (T : ℝ) ((⌈(x : ℝ) * 2 ^ n⌉₊ : ℝ) / 2 ^ n) := by
  simp [gc]

lemma le_gc {T x : ℝ≥0} (n : ℕ) (hx : x ≤ T) : x ≤ gc T n x := by
  rw [← NNReal.coe_le_coe, gc_real]
  refine le_min (by exact_mod_cast hx) ?_
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

lemma gc_le_add (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : (gc T n x : ℝ) ≤ x + 1 / 2 ^ n := by
  rw [gc_real]
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact (Nat.ceil_lt_add_one (by positivity)).le

lemma gc_le (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : gc T n x ≤ T := min_le_left _ _

lemma gc_tendsto {T x : ℝ≥0} (hx : x ≤ T) :
    Tendsto (fun n => (gc T n x : ℝ)) atTop (𝓝 (x : ℝ)) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simp_rw [← one_div_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun n : ℕ => (x : ℝ) + 1 / 2 ^ n) atTop (𝓝 (x : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (x : ℝ))).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => by exact_mod_cast le_gc n hx) (fun n => gc_le_add T n x)

lemma gc_mem {T x : ℝ≥0} (n : ℕ) (hx : x ≤ T) : gc T n x ∈ gcS T n := by
  refine Finset.mem_image.2 ⟨⌈(x : ℝ) * 2 ^ n⌉₊, Finset.mem_range.2 (Nat.lt_succ_of_le
    (Nat.ceil_mono ?_)), rfl⟩
  have : (x : ℝ) ≤ T := by exact_mod_cast hx
  gcongr

lemma gcS_le {T t : ℝ≥0} {n : ℕ} (ht : t ∈ gcS T n) : t ≤ T := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 ht
  exact min_le_left _ _

lemma gc_stop (hmono : Monotone m) {T : ℝ≥0} {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s})
    (n : ℕ) (s : ℝ≥0) : MeasurableSet[m s] {ω | gc T n (τ ω) ≤ s} := by
  by_cases hs : T ≤ s
  · have e : {ω | gc T n (τ ω) ≤ s} = Set.univ :=
      Set.eq_univ_of_forall fun ω => (gc_le T n (τ ω)).trans hs
    rw [e]; exact @MeasurableSet.univ Ω (m s)
  · have hsT : (s : ℝ) < T := by exact_mod_cast lt_of_not_ge hs
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hs0 : (0 : ℝ) ≤ (s : ℝ) * 2 ^ n := by positivity
    obtain ⟨s', hs'⟩ : ∃ s' : ℝ≥0, (s' : ℝ) = (⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n :=
      ⟨⟨(⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n, by positivity⟩, rfl⟩
    have hss : s' ≤ s := by
      rw [← NNReal.coe_le_coe, hs', div_le_iff₀ h2]
      exact Nat.floor_le hs0
    have e : {ω | gc T n (τ ω) ≤ s} = {ω | τ ω ≤ s'} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe, gc_real, hs', min_le_iff,
        or_iff_right (not_le.2 hsT), div_le_iff₀ h2, le_div_iff₀ h2]
      constructor
      · intro h
        have := Nat.le_floor h
        exact (Nat.le_ceil _).trans (by exact_mod_cast this)
      · intro h
        have := Nat.ceil_le.2 h
        exact (by exact_mod_cast this : (⌈(τ ω : ℝ) * 2 ^ n⌉₊ : ℝ) ≤ ⌊(s : ℝ) * 2 ^ n⌋₊).trans
          (Nat.floor_le hs0)
    rw [e]
    exact hmono hss _ (hτ s')



end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma stop_meas (hle : ∀ t, m t ≤ mΩ) {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) :
    Measurable τ := measurable_of_Iic fun x => hle x _ (hτ x)

lemma gc_meas (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) (n : ℕ) : Measurable fun ω => gc T n (τ ω) :=
  measurable_of_Iic fun x => hle x _ (gc_stop hmono hτ n x)

lemma memLp_stopc {T : ℝ≥0} (a : Lp ℝ 2 (μT P T)) {σ : Ω → ℝ≥0} (hσ : Measurable σ) :
    MemLp (fun z => (if (σ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) 2 (μT P T) := by
  have hind : Measurable fun z : ℝ × Ω => (if (σ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (hσ.comp measurable_snd).coe_nnreal_real measurable_fst)
      measurable_const measurable_const
  refine (Lp.memLp a).of_le (hind.aestronglyMeasurable.mul (Lp.memLp a).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  split_ifs <;> simp

lemma stopc_tendsto (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) {T : ℝ≥0} (a : Lp ℝ 2 (μT P T))
    {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) :
    Tendsto (fun n => (memLp_stopc a (gc_meas hle hmono T hτ n)).toLp _) atTop
      (𝓝 ((memLp_stopc a (stop_meas hle hτ)).toLp _)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖(memLp_stopc a (gc_meas hle hmono T hτ n)).toLp _ -
      (memLp_stopc a (stop_meas hle hτ)).toLp _‖ =
      ‖((memLp_stopc a (gc_meas hle hmono T hτ n)).sub (memLp_stopc a (stop_meas hle hτ))).toLp _‖ := by
    intro n
    congr 1
  simp_rw [e]
  have hsq : Tendsto (fun n => ‖((memLp_stopc a (gc_meas hle hmono T hτ n)).sub
      (memLp_stopc a (stop_meas hle hτ))).toLp _‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [sq_norm_toLp]
    have hD : Tendsto (fun n => ∫ z, ((fun z => (if ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 then
        (1 : ℝ) else 0) * a z) - (fun z => (if ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 then (1 : ℝ) else 0) *
        a z)) z ^ 2 ∂(μT P T)) atTop (𝓝 (∫ z, (0 : ℝ) ∂(μT P T))) := by
      refine tendsto_integral_of_dominated_convergence (fun z => a z ^ 2) (fun n => ?_)
        ((Lp.memLp a).integrable_sq) (fun n => Eventually.of_forall fun z => ?_) ?_
      · exact ((memLp_stopc a (gc_meas hle hmono T hτ n)).sub (memLp_stopc a (stop_meas hle hτ))).aestronglyMeasurable.pow 2
      · simp only [Pi.sub_apply, Real.norm_eq_abs]
        rw [← sub_mul, mul_pow, abs_of_nonneg (by positivity)]
        refine mul_le_of_le_one_left (sq_nonneg _) ?_
        split_ifs <;> norm_num
      · filter_upwards [ae_ne_graph (P := P) T (stop_meas hle hτ)] with z hz
        refine tendsto_const_nhds.congr' ?_
        rcases lt_or_gt_of_ne hz with hlt | hgt
        · refine Eventually.of_forall fun n => ?_
          have h1 : ¬ ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 :=
            not_le.2 (lt_of_lt_of_le hlt (by exact_mod_cast le_gc n (hτT z.2)))
          have h2 : ¬ ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 := not_le.2 hlt
          simp [h1, h2]
        · filter_upwards [(gc_tendsto (hτT z.2)).eventually (gt_mem_nhds hgt)] with n hn
          have h1 : ((gc T n (τ z.2) : ℝ≥0) : ℝ) ≤ z.1 := hn.le
          have h2 : ((τ z.2 : ℝ≥0) : ℝ) ≤ z.1 := hgt.le
          simp [h1, h2]
    rw [integral_zero] at hD
    exact hD
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- L2 with existence: `1_{τ ≤ r} a` is an integrand, and its integral `δ` satisfies
`δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/
theorem L2full (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {bc : Lp ℝ 2 (μT P T)}
    (hbc : bc =ᵐ[μT P T] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) :
    ∃ δ, Rep hW T δ bc ∧ ∀ (u : ℝ≥0) (ξ : Ω → ℝ), Measurable[m u] ξ → ∀ C : ℝ,
      (∀ ω, |ξ ω| ≤ C) → ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by
  exact (by obtain ⟨δ, h1, h2⟩ := HedgePSNV.stopped_integrand_representation hW.mono hW.le hW.adapt hW.indep hW.mem2 hW.mean hW.var T (StochCalcP6.StochCalcO3.μT P T) rfl ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).1 ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).2.1 ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).2.2 hτT hτ hbc; exact ⟨δ, (StochCalcP6.StochCalcRU.rep_iff hW T δ bc).2 (by unfold StochCalcP6.StochCalcRU.RepU; exact h1), h2⟩)















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






lemma integrable_L2 (f : Lp ℝ 2 P) : Integrable (f : Ω → ℝ) P := (Lp.memLp f).integrable one_le_two






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

theorem rep_of_tendsto (hW : IncrHyp m W P) (T : ℝ≥0) {θ : ℕ → Lp ℝ 2 P}
    {b : ℕ → Lp ℝ 2 (μT P T)} (h : ∀ n, Rep hW T (θ n) (b n)) {bl : Lp ℝ 2 (μT P T)}
    (hb : Tendsto b atTop (𝓝 bl)) :
    ∃ θl, Tendsto θ atTop (𝓝 θl) ∧ Rep hW T θl bl := by
  have hc : CauchySeq θ := by
    have hcu : CauchySeq b := hb.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, rep_norm hW T (rep_sub hW T (h i) (h j)), ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨θl, hθ⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨θl, hθ, isClosed_closure.mem_of_tendsto hθ (Eventually.of_forall fun n => (h n).1),
    isClosed_closure.mem_of_tendsto hb (Eventually.of_forall fun n => (h n).2.1), fun x => ?_⟩
  have h1 : Tendsto (fun n => ⟪θ n, TL hW T x⟫_ℝ) atTop (𝓝 ⟪θl, TL hW T x⟫_ℝ) :=
    hθ.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪b n, eL (P := P) hW.le T x⟫_ℝ) atTop
      (𝓝 ⟪bl, eL (P := P) hW.le T x⟫_ℝ) := hb.inner tendsto_const_nhds
  have e : (fun n => ⟪θ n, TL hW T x⟫_ℝ) = fun n => ⟪b n, eL (P := P) hW.le T x⟫_ℝ :=
    funext fun n => (h n).2.2 x
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-- Monotone truncation in `L²` of a finite measure: bounded norms of `1_{S n} f` give
`f ∈ L²` and `1_{S n} f → f` in `L²`. -/
theorem memLp_tendsto_of_ind {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n))
    (hmono : Monotone S) (hcov : ∀ᵐ z ∂μ, ∃ n, z ∈ S n) {C : ℝ≥0∞} (hC : C < ⊤)
    (hb : ∀ n, eLpNorm ((S n).indicator f) 2 μ ≤ C) :
    MemLp f 2 μ ∧ Tendsto (fun n => eLpNorm ((S n).indicator f - f) 2 μ) atTop (𝓝 0) := by
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n => (S n).indicator f z) atTop (𝓝 (f z)) := by
    filter_upwards [hcov] with z hz
    obtain ⟨n0, hn0⟩ := hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n0] with n hn
    rw [Set.indicator_of_mem (hmono hn hn0)]
  have hfm : ∀ n, AEStronglyMeasurable ((S n).indicator f) μ := fun n => hf.indicator (hS n)
  have hle : eLpNorm f 2 μ ≤ C :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm f hlim).trans
      (liminf_le_of_frequently_le' (Eventually.of_forall hb).frequently)
  have hf2 : MemLp f 2 μ := ⟨hf, lt_of_le_of_lt hle hC⟩
  refine ⟨hf2, tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top hfm hf2 ?_ hlim⟩
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := unifIntegrable_const (μ := μ) one_le_two ENNReal.ofNat_ne_top hf2 hε
  refine ⟨δ, hδ, fun n s hs hμs => le_trans (eLpNorm_mono fun z => ?_) (hδ' 0 s hs hμs)⟩
  by_cases h1 : z ∈ s <;> by_cases h2 : z ∈ S n <;> simp [Set.indicator, h1, h2]

/-- **Z1 (truncation limit of `Rep`).**  If `Rep θ_n (1_{S n} f)` with `‖θ_n‖ ≤ C`, then
`f ∈ L²(μT)` and `θ_n` converges in `L²` to some `θ` with `Rep θ f`. -/
theorem rep_trunc (hW : IncrHyp m W P) (T : ℝ≥0) {f : ℝ × Ω → ℝ}
    (hf : AEStronglyMeasurable f (μT P T)) {S : ℕ → Set (ℝ × Ω)} (hS : ∀ n, MeasurableSet (S n))
    (hmono : Monotone S) (hcov : ∀ᵐ z ∂(μT P T), ∃ n, z ∈ S n)
    (hbn : ∀ n, MemLp ((S n).indicator f) 2 (μT P T)) {θ : ℕ → Lp ℝ 2 P}
    (h : ∀ n, Rep hW T (θ n) ((hbn n).toLp _)) {C : ℝ} (hC : ∀ n, ‖θ n‖ ≤ C) :
    ∃ hf2 : MemLp f 2 (μT P T), ∃ θl, Tendsto θ atTop (𝓝 θl) ∧ Rep hW T θl (hf2.toLp f) := by
  have hb : ∀ n, eLpNorm ((S n).indicator f) 2 (μT P T) ≤ ENNReal.ofReal C := fun n => by
    have h1 := rep_norm hW T (h n)
    rw [Lp.norm_toLp] at h1
    rw [← ENNReal.ofReal_toReal (hbn n).eLpNorm_lt_top.ne, ← h1]
    exact ENNReal.ofReal_le_ofReal (hC n)
  obtain ⟨hf2, ht⟩ := memLp_tendsto_of_ind hf hS hmono hcov ENNReal.ofReal_lt_top hb
  have hbt : Tendsto (fun n => (hbn n).toLp _) atTop (𝓝 (hf2.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hbn f hf2).2 ht
  obtain ⟨θl, hθ, hr⟩ := rep_of_tendsto hW T h hbt
  exact ⟨hf2, θl, hθ, hr⟩

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

lemma sel_sum {β : Type*} [AddCommMonoid β] (S : Finset ℝ≥0) (σ : Ω → ℝ≥0) (hS : ∀ ω, σ ω ∈ S)
    (h : ℝ≥0 → Ω → β) (ω : Ω) :
    h (σ ω) ω = ∑ t ∈ S, ({x | σ x = t} : Set Ω).indicator (h t) ω := by
  classical
  rw [Finset.sum_eq_single (σ ω)]
  · simp [Set.indicator_apply]
  · intro t _ ht
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [if_neg (fun e => ht e.symm)]
  · intro h'; exact absurd (hS ω) h'

lemma sq_restrict_eq (g : Ω → ℝ) (A : Set Ω) :
    eLpNorm g 2 (P.restrict A) ^ (2:ℝ) = ∫⁻ ω in A, ‖g ω‖ₑ ^ (2:ℝ) ∂P := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := P.restrict A) (f := g) (p := 2) two_ne_zero
  simpa using this

lemma loc_le (hle : ∀ t, m t ≤ mΩ) {T t : ℝ≥0} {Z : ℝ≥0 → Ω → ℝ} (hZT : MemLp (Z T) 2 P)
    (hmart : condExp (m t) P (Z T) =ᵐ[P] Z t) {A : Set Ω} (hA : MeasurableSet[m t] A) :
    ∫⁻ ω in A, ‖Z t ω‖ₑ ^ (2:ℝ) ∂P ≤ ∫⁻ ω in A, ‖Z T ω‖ₑ ^ (2:ℝ) ∂P := by
  rw [← sq_restrict_eq, ← sq_restrict_eq]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (hle t A hA),
    ← eLpNorm_indicator_eq_eLpNorm_restrict (hle t A hA)]
  have h1 : A.indicator (Z t) =ᵐ[P] condExp (m t) P (A.indicator (Z T)) := by
    have := condExp_indicator (m := m t) (μ := P) (hZT.integrable one_le_two) hA
    filter_upwards [this, hmart] with ω h2 h3
    rw [h2]
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]; exact h3.symm
    · simp only [Set.indicator_of_notMem hω]
  rw [eLpNorm_congr_ae h1]
  exact eLpNorm_condExp_le_eLpNorm _ one_le_two

lemma fin_le (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) {T : ℝ≥0} {Z : ℝ≥0 → Ω → ℝ}
    (hZm : ∀ t ≤ T, StronglyMeasurable[m t] (Z t)) (hZT : MemLp (Z T) 2 P)
    (hmart : ∀ t ≤ T, condExp (m t) P (Z T) =ᵐ[P] Z t)
    (S : Finset ℝ≥0) (hST : ∀ t ∈ S, t ≤ T) {σ : Ω → ℝ≥0} (hS : ∀ ω, σ ω ∈ S)
    (hσ : ∀ s, MeasurableSet[m s] {ω | σ ω ≤ s}) :
    ∫⁻ ω, ‖Z (σ ω) ω‖ₑ ^ (2:ℝ) ∂P ≤ ∫⁻ ω, ‖Z T ω‖ₑ ^ (2:ℝ) ∂P := by
  have hA : ∀ t, MeasurableSet[m t] {ω | σ ω = t} := eq_meas_of_stop hmono S hS hσ
  have hA' : ∀ t, MeasurableSet {ω | σ ω = t} := fun t => hle t _ (hA t)
  have e1 : (fun ω => ‖Z (σ ω) ω‖ₑ ^ (2:ℝ)) = fun ω => ∑ t ∈ S,
      ({x | σ x = t} : Set Ω).indicator (fun ω => ‖Z t ω‖ₑ ^ (2:ℝ)) ω :=
    funext fun ω => sel_sum S σ hS (fun t ω => ‖Z t ω‖ₑ ^ (2:ℝ)) ω
  have e2 : (fun ω => ‖Z T ω‖ₑ ^ (2:ℝ)) = fun ω => ∑ t ∈ S,
      ({x | σ x = t} : Set Ω).indicator (fun ω => ‖Z T ω‖ₑ ^ (2:ℝ)) ω :=
    funext fun ω => sel_sum S σ hS (fun _ ω => ‖Z T ω‖ₑ ^ (2:ℝ)) ω
  have m1 : ∀ t ∈ S, AEMeasurable (({x | σ x = t} : Set Ω).indicator
      (fun ω => ‖Z t ω‖ₑ ^ (2:ℝ))) P := fun t ht =>
    ((((hZm t (hST t ht)).mono (hle t)).measurable.enorm.pow_const _).indicator (hA' t)).aemeasurable
  have m2 : ∀ t ∈ S, AEMeasurable (({x | σ x = t} : Set Ω).indicator
      (fun ω => ‖Z T ω‖ₑ ^ (2:ℝ))) P := fun t _ =>
    (hZT.1.aemeasurable.enorm.pow_const _).indicator (hA' t)
  rw [e1, e2, lintegral_finset_sum' S m1, lintegral_finset_sum' S m2]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [lintegral_indicator (hA' t), lintegral_indicator (hA' t)]
  exact loc_le hle hZT (hmart t (hST t ht)) (hA t)

lemma gc_eq_top {T x : ℝ≥0} (n : ℕ) (hx : T ≤ x) : gc T n x = T := by
  rw [← NNReal.coe_inj, gc_real]
  refine min_eq_left ?_
  rw [le_div_iff₀ (by positivity)]
  calc (T : ℝ) * 2 ^ n ≤ x * 2 ^ n := by gcongr
    _ ≤ _ := Nat.le_ceil _

lemma gc_min (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : gc T n x = gc T n (min x T) := by
  rcases le_total x T with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, gc_eq_top n h, gc_eq_top n le_rfl]

lemma gc_tendsto_right {T x : ℝ≥0} (hx : x ≤ T) :
    Tendsto (fun n => gc T n x) atTop (𝓝[≥] x) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => Set.mem_Ici.2 (le_gc n hx)⟩
  rw [← NNReal.tendsto_coe]
  exact gc_tendsto hx

/-- **Z6.** L² optional-sampling bound. -/
theorem Z6 (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) {T : ℝ≥0} {Z : ℝ≥0 → Ω → ℝ}
    (hZm : ∀ t ≤ T, StronglyMeasurable[m t] (Z t)) (hZT : MemLp (Z T) 2 P)
    (hmart : ∀ t ≤ T, condExp (m t) P (Z T) =ᵐ[P] Z t)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t)
    {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) :
    MemLp (fun ω => Z (min (τ ω) T) ω) 2 P ∧
      eLpNorm (fun ω => Z (min (τ ω) T) ω) 2 P ≤ eLpNorm (Z T) 2 P := by
  classical
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → Ω → ℝ≥0, σ = fun n ω => gc T n (τ ω) := ⟨_, rfl⟩
  have hσ : ∀ n ω, σ n ω = gc T n (τ ω) := fun n ω => by rw [hσdef]
  have hσS : ∀ n ω, σ n ω ∈ gcS T n := fun n ω => by
    rw [hσ, gc_min T n (τ ω)]; exact gc_mem n (min_le_right _ _)
  have hσst : ∀ n s, MeasurableSet[m s] {ω | σ n ω ≤ s} := fun n s => by
    simp only [hσ]; exact gc_stop hmono hτ n s
  have hlim : ∀ ω, Tendsto (fun n => Z (σ n ω) ω) atTop (𝓝 (Z (min (τ ω) T) ω)) := by
    intro ω
    have h1 : Tendsto (fun n => σ n ω) atTop (𝓝[≥] (min (τ ω) T)) := by
      have e : (fun n => σ n ω) = fun n => gc T n (min (τ ω) T) :=
        funext fun n => by rw [hσ, gc_min T n (τ ω)]
      rw [e]
      exact gc_tendsto_right (min_le_right _ _)
    exact (hrc ω _).tendsto.comp h1
  have hmeas : ∀ n, StronglyMeasurable (fun ω => Z (σ n ω) ω) := by
    intro n
    have e : (fun ω => Z (σ n ω) ω) = fun ω => ∑ t ∈ gcS T n,
        ({x | σ n x = t} : Set Ω).indicator (Z t) ω :=
      funext fun ω => sel_sum _ (σ n) (hσS n) Z ω
    have e' : (fun ω => ∑ t ∈ gcS T n, ({x | σ n x = t} : Set Ω).indicator (Z t) ω) =
        ∑ t ∈ gcS T n, ({x | σ n x = t} : Set Ω).indicator (Z t) :=
      funext fun ω => (Finset.sum_apply ω _ _).symm
    rw [e, e']
    refine Finset.stronglyMeasurable_sum _ fun t ht => ?_
    exact ((hZm t (gcS_le ht)).mono (hle t)).indicator
      (hle t _ (eq_meas_of_stop hmono _ (hσS n) (hσst n) t))
  have hfin : ∀ n, ∫⁻ ω, ‖Z (σ n ω) ω‖ₑ ^ (2:ℝ) ∂P ≤ ∫⁻ ω, ‖Z T ω‖ₑ ^ (2:ℝ) ∂P := fun n =>
    fin_le hle hmono hZm hZT hmart (gcS T n) (fun t ht => gcS_le ht) (hσS n) (hσst n)
  have hae : AEStronglyMeasurable (fun ω => Z (min (τ ω) T) ω) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hmeas n).aestronglyMeasurable)
      (Eventually.of_forall hlim)
  have hlint : ∫⁻ ω, ‖Z (min (τ ω) T) ω‖ₑ ^ (2:ℝ) ∂P ≤ ∫⁻ ω, ‖Z T ω‖ₑ ^ (2:ℝ) ∂P := by
    calc ∫⁻ ω, ‖Z (min (τ ω) T) ω‖ₑ ^ (2:ℝ) ∂P
        = ∫⁻ ω, liminf (fun n => ‖Z (σ n ω) ω‖ₑ ^ (2:ℝ)) atTop ∂P := by
          refine lintegral_congr fun ω => ?_
          exact (((ENNReal.continuous_rpow_const.tendsto _).comp
            ((continuous_enorm.tendsto _).comp (hlim ω)))).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ‖Z (σ n ω) ω‖ₑ ^ (2:ℝ) ∂P) atTop :=
          lintegral_liminf_le' fun n => ((hmeas n).measurable.enorm.pow_const _).aemeasurable
      _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hfin)
  have hle2 : eLpNorm (fun ω => Z (min (τ ω) T) ω) 2 P ≤ eLpNorm (Z T) 2 P := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := P) (f := fun ω => Z (min (τ ω) T) ω)
      (p := 2) two_ne_zero
    have h' := eLpNorm_nnreal_pow_eq_lintegral (μ := P) (f := Z T) (p := 2) two_ne_zero
    simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h h'
    rw [← ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num), h, h']
    exact hlint
  exact ⟨⟨hae, hle2.trans_lt hZT.2⟩, hle2⟩

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

lemma ifun_resI_meas (hW : IncrHyp m W P) {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) :
    Measurable[m s] (ifun W (resI s i)) := by
  by_cases hus : i.u ≤ s
  · have hv : max i.u (min i.v s) ≤ s := max_le hus (min_le_right _ _)
    have hY : Measurable[m s] i.Y := i.hY.mono (hW.mono hus) le_rfl
    have h1 : Measurable[m s] (W (max i.u (min i.v s))) := (hW.adapt _).mono (hW.mono hv) le_rfl
    have h2 : Measurable[m s] (W i.u) := (hW.adapt _).mono (hW.mono hus) le_rfl
    show Measurable[m s] (fun ω => i.Y ω * (W (max i.u (min i.v s)) ω - W i.u ω))
    exact hY.mul (h1.sub h2)
  · have hv : max i.u (min i.v s) = i.u :=
      max_eq_left ((min_le_right _ _).trans (le_of_lt (lt_of_not_ge hus)))
    have e : ifun W (resI s i) = fun _ => 0 := by
      funext ω
      show i.Y ω * (W (max i.u (min i.v s)) ω - W i.u ω) = 0
      rw [hv, sub_self, mul_zero]
    rw [e]; exact measurable_const

lemma TL_resF_aesm (hW : IncrHyp m W P) (T : ℝ≥0) (s : ℝ≥0) (x : Elem m T →₀ ℝ) :
    AEStronglyMeasurable[m s] (TL hW T (resF s x) : Ω → ℝ) P := by
  have e : (fun ω => (resF s x).sum (fun i c => c * ifun W i ω)) =
      fun ω => x.sum (fun i c => c * ifun W (resI s i) ω) := by
    funext ω
    unfold resF
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  have hm : Measurable[m s] fun ω => (resF s x).sum (fun i c => c * ifun W i ω) := by
    rw [e]
    simp only [Finsupp.sum]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (ifun_resI_meas hW s i)
  exact ⟨_, hm.stronglyMeasurable, coe_TL hW T (resF s x)⟩

/-- Integrals of integrands vanishing on `[s, ∞)` are `m s`-measurable. -/
lemma rep_aesm (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {s : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), (s : ℝ) ≤ z.1 → b z = 0) :
    AEStronglyMeasurable[m s] (θ : Ω → ℝ) P := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.2.1
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  have hb : (memLp_res (Lp.memLp b) s).toLp _ = b := by
    refine Lp.ext ?_
    filter_upwards [(memLp_res (Lp.memLp b) s).coeFn_toLp, hv, ae_fst_Ico (P := P) T]
      with z h1 h2 h3
    rw [h1]
    by_cases hz : (s : ℝ) ≤ z.1
    · simp [h2 hz]
    · have : ind 0 s z.1 = 1 := by simp [ind, Set.indicator_apply, h3.1, lt_of_not_ge hz]
      simp [this]
  have hres : Tendsto (fun n => eL (P := P) hW.le T (resF s (y n))) atTop (𝓝 b) := by
    rw [← hb, tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_res_sub_le hW.le b s (y n))
      ((tendsto_iff_norm_sub_tendsto_zero).1 hx')
  have hθ := rep_conv hW T h hres
  exact (isClosed_aestronglyMeasurable (hW.le s)).mem_of_tendsto hθ
    (Eventually.of_forall fun n => TL_resF_aesm hW T s (y n))

lemma setInt_eq_oneA (f : Ω → ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, f ω ∂P = ∫ ω, f ω * oneA A ω ∂P := by
  rw [← integral_indicator hA]
  congr 1; funext ω
  by_cases hω : ω ∈ A <;> simp [oneA, hω]

/-- `E[θ | m t]` is the integral of `1_{s<t} a`. -/
theorem rep_ce (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) (t : ℝ≥0) {φ : Lp ℝ 2 P} (hφ : (φ : Ω → ℝ) =ᵐ[P] condExp (m t) P θ) :
    Rep hW T φ ((memLp_res (Lp.memLp a) t).toLp _) := by
  obtain ⟨d, hd⟩ := rep_exists hW T (tl_mem hW T h.2.1 t)
  have e : a - (memLp_tl (Lp.memLp a) t).toLp _ = (memLp_res (Lp.memLp a) t).toLp _ := by
    refine Lp.ext ?_
    filter_upwards [(memLp_tl (Lp.memLp a) t).coeFn_toLp,
      Lp.coeFn_sub a ((memLp_tl (Lp.memLp a) t).toLp _),
      (memLp_res (Lp.memLp a) t).coeFn_toLp] with z h1 h2 h3
    rw [h2, Pi.sub_apply, h1, h3]; ring
  have hr : Rep hW T (θ - d) ((memLp_res (Lp.memLp a) t).toLp _) := by
    rw [← e]; exact rep_sub hW T h hd
  have hvan : ∀ᵐ z ∂(μT P T), (t : ℝ) ≤ z.1 →
      ((memLp_res (Lp.memLp a) t).toLp _ : ℝ × Ω → ℝ) z = 0 := by
    filter_upwards [(memLp_res (Lp.memLp a) t).coeFn_toLp] with z h1 hz
    rw [h1]
    have : ind 0 t z.1 = 0 := by simp [ind, Set.indicator_apply, not_lt.2 hz]
    simp [this]
  have hmeas := rep_aesm hW T hr hvan
  have hce : ((θ - d : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] condExp (m t) P θ := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (hW.le t) (integrable_L2 θ)
      (fun A _ _ => (integrable_L2 _).integrableOn) (fun A hA _ => ?_) hmeas
    have hA' : MeasurableSet A := hW.le t _ hA
    have h0 : ∫ ω in A, d ω ∂P = 0 := by
      rw [setInt_eq_oneA _ hA']
      exact rep_perp_int hW T hd (tl_vanish a t) (oneA_meas hA) (abs_oneA_le A)
    rw [setIntegral_congr_ae (g := fun ω => θ ω - d ω) hA'
      ((Lp.coeFn_sub θ d).mono fun ω h _ => h), integral_sub
      (integrable_L2 θ).integrableOn (integrable_L2 d).integrableOn, h0, sub_zero]
  have hφd : φ = θ - d := Lp.ext (hφ.trans hce.symm)
  rw [hφd]; exact hr

/-- Finite-valued stopping times: `θ - K_τ` integrates `1_{τ ≤ s} a`. -/
theorem Z5fin (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {K : ℝ≥0 → Ω → ℝ} (hK : ∀ t ≤ T, K t =ᵐ[P] condExp (m t) P θ)
    {τ : Ω → ℝ≥0} (S : Finset ℝ≥0) (hS : ∀ ω, τ ω ∈ S)
    (hST : ∀ t ∈ S, t ≤ T) (hτ : ∀ t ∈ S, MeasurableSet[m t] {ω | τ ω = t})
    {bc : Lp ℝ 2 (μT P T)}
    (hbc : bc =ᵐ[μT P T] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) :
    ∃ δ : Lp ℝ 2 P, (δ : Ω → ℝ) =ᵐ[P] (fun ω => θ ω - K (τ ω) ω) ∧ Rep hW T δ bc := by
  classical
  have hφ : ∀ t : ℝ≥0, ∃ φ : Lp ℝ 2 P, (φ : Ω → ℝ) =ᵐ[P] condExp (m t) P θ := fun t => by
    have h2 : MemLp (condExp (m t) P (θ : Ω → ℝ)) 2 P := (Lp.memLp θ).condExp (by norm_num)
    exact ⟨h2.toLp _, h2.coeFn_toLp⟩
  choose φ hφ using hφ
  have hd : ∀ t, Rep hW T (θ - φ t) ((memLp_tl (Lp.memLp a) t).toLp _) := by
    intro t
    have h1 := rep_sub hW T h (rep_ce hW T h t (hφ t))
    have e : a - (memLp_res (Lp.memLp a) t).toLp _ = (memLp_tl (Lp.memLp a) t).toLp _ := by
      refine Lp.ext ?_
      filter_upwards [(memLp_tl (Lp.memLp a) t).coeFn_toLp,
        Lp.coeFn_sub a ((memLp_res (Lp.memLp a) t).toLp _),
        (memLp_res (Lp.memLp a) t).coeFn_toLp] with z h1 h2 h3
      rw [h2, Pi.sub_apply, h1, h3]; ring
    rw [← e]; exact h1
  have hτ' : ∀ t, MeasurableSet[m t] {ω | τ ω = t} := by
    intro t
    by_cases ht : t ∈ S
    · exact hτ t ht
    · have e : {ω | τ ω = t} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro e; exact ht (e ▸ hS ω)
      rw [e]; exact @MeasurableSet.empty Ω (m t)
  have hA0 : ∀ t, MeasurableSet {ω | τ ω = t} := fun t => hW.le t _ (hτ' t)
  have hrep : ∀ t ∈ S, Rep hW T ((memLp_oneA_mul (hA0 t) (θ - φ t)).toLp _)
      ((memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) := fun t ht =>
    L0 hW T (hST t ht) (hτ' t) (hd t) (tl_vanish a t)
      (memLp_oneA_mul (hA0 t) (θ - φ t)).coeFn_toLp (memLp_oneA_mulT (hA0 t) _).coeFn_toLp
  have hsum := rep_sum hW T S (θ := fun t => (memLp_oneA_mul (hA0 t) (θ - φ t)).toLp _)
    (b := fun t => (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) hrep
  have hbeq : (∑ t ∈ S, (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _) =
      bc := by
    refine Lp.ext ?_
    filter_upwards [coeFn_fsum S
        (fun t => (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _),
      hbc, ae_fst_Ico (P := P) T,
      (Filter.eventually_all_finset S).2 fun t _ =>
        (memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).coeFn_toLp,
      (Filter.eventually_all_finset S).2 fun t _ => (memLp_tl (Lp.memLp a) t).coeFn_toLp]
      with z h1 h2 h3 h4 h5
    have e : ∀ t ∈ S, ((memLp_oneA_mulT (hA0 t) ((memLp_tl (Lp.memLp a) t).toLp _)).toLp _ :
        ℝ × Ω → ℝ) z = oneA {ω | τ ω = t} z.2 * (a z * (1 - ind 0 t z.1)) := fun t ht => by
      rw [h4 t ht, h5 t ht]
    rw [h1, h2, Finset.sum_congr rfl e, Finset.sum_eq_single (τ z.2)]
    · simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq, if_true, one_mul]
      by_cases hle : (τ z.2 : ℝ) ≤ z.1
      · have : ind 0 (τ z.2) z.1 = 0 := by simp [ind, Set.indicator_apply, not_lt.2 hle]
        simp [hle, this]
      · have : ind 0 (τ z.2) z.1 = 1 := by
          simp [ind, Set.indicator_apply, h3.1, lt_of_not_ge hle]
        simp [hle, this]
    · intro t _ ht
      simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (Ne.symm ht)]; ring
    · intro hn; exact absurd (hS z.2) hn
  refine ⟨_, ?_, hbeq ▸ hsum⟩
  filter_upwards [coeFn_fsum S (fun t => (memLp_oneA_mul (hA0 t) (θ - φ t)).toLp _),
    (Filter.eventually_all_finset S).2 fun t _ => (memLp_oneA_mul (hA0 t) (θ - φ t)).coeFn_toLp,
    (Filter.eventually_all_finset S).2 fun t _ => Lp.coeFn_sub θ (φ t),
    (Filter.eventually_all_finset S).2 fun t _ => hφ t,
    (Filter.eventually_all_finset S).2 fun t ht => hK t (hST t ht)] with ω h1 h2 h3 h4 h5
  have e : ∀ t ∈ S, ((memLp_oneA_mul (hA0 t) (θ - φ t)).toLp _ : Ω → ℝ) ω =
      oneA {ω | τ ω = t} ω * (θ ω - φ t ω) := fun t ht => by
    rw [h2 t ht, h3 t ht, Pi.sub_apply]
  rw [h1, Finset.sum_congr rfl e, Finset.sum_eq_single (τ ω)]
  · simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq, if_true, one_mul]
    rw [h4 _ (hS ω), ← h5 _ (hS ω)]
  · intro t _ ht
    simp only [oneA, Set.indicator_apply, Set.mem_setOf_eq]
    rw [if_neg (Ne.symm ht)]; ring
  · intro hn; exact absurd (hS ω) hn

/-- **Z5.** Stopped identification: `K_τ` integrates `1_{s<τ} a`. -/
theorem Z5 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {K : ℝ≥0 → Ω → ℝ} (hK : ∀ t ≤ T, K t =ᵐ[P] condExp (m t) P θ)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => K s ω) (Set.Ici t) t)
    {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s})
    {bτ : Lp ℝ 2 (μT P T)}
    (hbτ : bτ =ᵐ[μT P T] fun z => (if z.1 < (τ z.2 : ℝ) then (1 : ℝ) else 0) * a z) :
    ∃ θτ : Lp ℝ 2 P, (θτ : Ω → ℝ) =ᵐ[P] (fun ω => K (τ ω) ω) ∧ Rep hW T θτ bτ := by
  classical
  obtain ⟨δ, hδ, -⟩ := L2full hW T h hτT hτ (memLp_stopc a (stop_meas hW.le hτ)).coeFn_toLp
  have hn : ∀ n : ℕ, ∃ δn : Lp ℝ 2 P,
      (δn : Ω → ℝ) =ᵐ[P] (fun ω => θ ω - K (gc T n (τ ω)) ω) ∧
      Rep hW T δn ((memLp_stopc a (gc_meas hW.le hW.mono T hτ n)).toLp _) := fun n =>
    Z5fin hW T h hK (gcS T n) (fun ω => gc_mem n (hτT ω)) (fun t ht => gcS_le ht)
      (fun t _ => eq_meas_of_stop hW.mono _ (fun ω => gc_mem n (hτT ω)) (gc_stop hW.mono hτ n) t)
      (memLp_stopc a (gc_meas hW.le hW.mono T hτ n)).coeFn_toLp
  choose δn hδn hrn using hn
  have hconv : Tendsto δn atTop (𝓝 δ) := by
    have hb := stopc_tendsto hW.le hW.mono a hτT hτ
    rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
    have e : ∀ n, ‖δn n - δ‖ = ‖(memLp_stopc a (gc_meas hW.le hW.mono T hτ n)).toLp _ -
        (memLp_stopc a (stop_meas hW.le hτ)).toLp _‖ :=
      fun n => rep_norm hW T (rep_sub hW T (hrn n) hδ)
    simp_rw [e]; exact hb
  obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hae : ∀ᵐ ω ∂P, ∀ n, δn n ω = θ ω - K (gc T n (τ ω)) ω := ae_all_iff.2 hδn
  have hδK : (δ : Ω → ℝ) =ᵐ[P] fun ω => θ ω - K (τ ω) ω := by
    filter_upwards [hns, hae] with ω h1 h2
    have h3 : Tendsto (fun i => δn (ns i) ω) atTop (𝓝 (θ ω - K (τ ω) ω)) := by
      simp_rw [h2]
      refine tendsto_const_nhds.sub ?_
      have hg : Tendsto (fun n => gc T n (τ ω)) atTop (𝓝[≥] τ ω) := gc_tendsto_right (hτT ω)
      exact ((hrc ω (τ ω)).tendsto.comp hg).comp hns_mono.tendsto_atTop
    exact tendsto_nhds_unique h1 h3
  refine ⟨θ - δ, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub θ δ, hδK] with ω h1 h2
    rw [h1, Pi.sub_apply, h2]; ring
  · have e : a - (memLp_stopc a (stop_meas hW.le hτ)).toLp _ = bτ := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub a ((memLp_stopc a (stop_meas hW.le hτ)).toLp _),
        (memLp_stopc a (stop_meas hW.le hτ)).coeFn_toLp, hbτ] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      by_cases hz : (τ z.2 : ℝ) ≤ z.1
      · simp [hz, not_lt.2 hz]
      · simp [hz, lt_of_not_ge hz]
    rw [← e]; exact rep_sub hW T h hδ

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


/-- **Z4m-b.** -/
theorem Z4m (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] {H J : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ u ω, |H u ω| ≤ D) (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) H J) (T : ℝ≥0)
    (hH2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT M.P T)) :
    ∃ θ : Lp ℝ 2 M.P, (θ : Ω → ℝ) =ᵐ[M.P] J T ∧ StochCalcO3.Rep (incr_B M hM) T θ (hH2.toLp _) := by
  exact (by obtain ⟨θ, h1, h2⟩ := HedgePSNV.bounded_integrand_ito_representation M hM (StochCalcBr.W M) (fun _ _ => rfl) hD0 hD hHm hJ T (StochCalcP6.StochCalcO3.μT M.P T) rfl hH2; exact ⟨θ, h1, (StochCalcP6.StochCalcRU.rep_iff (StochCalcP6.StochCalcO3M.incr_B M hM) T θ _).2 (by unfold StochCalcP6.StochCalcRU.RepU; exact h2)⟩)


























































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





lemma clamp_eq {c x : ℝ} (h : |x| ≤ c) : max (-c) (min c x) = x := by
  rw [min_eq_right (abs_le.mp h).2, max_eq_right (abs_le.mp h).1]






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

/-- An elementary process of horizon `t` seen at horizon `T ≥ t`. -/
def extE {t T : ℝ≥0} (htT : t ≤ T) (i : Elem m t) : Elem m T where
  u := i.u
  v := i.v
  huv := i.huv
  hvT := i.hvT.trans htT
  Y := i.Y
  hY := i.hY
  C := i.C
  hC := i.hC

/-- The time window `[0,t)` as a set of `ℝ × Ω`. -/
def winS (t : ℝ≥0) : Set (ℝ × Ω) := {z | z.1 ∈ Set.Ico (0 : ℝ) t}

omit [IsProbabilityMeasure P] in
lemma winS_meas (t : ℝ≥0) : MeasurableSet (winS (Ω := Ω) t) :=
  measurable_fst measurableSet_Ico

lemma muT_restrict {t T : ℝ≥0} (htT : t ≤ T) :
    (μT P T).restrict (winS t) = μT P t := by
  have e : winS (Ω := Ω) t = Set.Ico (0 : ℝ) t ×ˢ (Set.univ : Set Ω) := by
    ext z; simp [winS]
  rw [e, μT, μT, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict measurableSet_Ico]
  congr 2
  ext r
  simp only [Set.mem_inter_iff, Set.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, h1, h2.trans_le (by exact_mod_cast htT)⟩

omit [IsProbabilityMeasure P] in
lemma ind_eq_winS (t : ℝ≥0) (g : ℝ × Ω → ℝ) (z : ℝ × Ω) :
    (winS t).indicator g z = g z * ind 0 t z.1 := by
  by_cases hz : z.1 ∈ Set.Ico (0 : ℝ) t
  · have hz' : z ∈ winS (Ω := Ω) t := hz
    rw [Set.indicator_of_mem hz']
    simp [ind, Set.indicator_apply, hz]
  · have hz' : z ∉ winS (Ω := Ω) t := hz
    rw [Set.indicator_of_notMem hz']
    simp [ind, hz]

omit [IsProbabilityMeasure P] in
lemma efun_zero {t : ℝ≥0} (i : Elem m t) {z : ℝ × Ω} (hz : z ∉ winS (Ω := Ω) t) :
    efun i z = 0 := by
  unfold efun ind
  have hn : z.1 ∉ Set.Ico (i.u : ℝ) i.v := by
    intro h
    exact hz ⟨(NNReal.coe_nonneg i.u).trans h.1, h.2.trans_le (by exact_mod_cast i.hvT)⟩
  simp [Set.indicator_apply, hn]

lemma memLp_extL {t T : ℝ≥0} (htT : t ≤ T) (b : Lp ℝ 2 (μT P t)) :
    MemLp ((winS t).indicator (b : ℝ × Ω → ℝ)) 2 (μT P T) := by
  rw [memLp_indicator_iff_restrict (winS_meas t), muT_restrict htT]
  exact Lp.memLp b

/-- Extension by zero of a horizon-`t` integrand to horizon `T`. -/
noncomputable def extL {t T : ℝ≥0} (htT : t ≤ T) (b : Lp ℝ 2 (μT P t)) : Lp ℝ 2 (μT P T) :=
  (memLp_extL htT b).toLp _

lemma TL_ext (hW : IncrHyp m W P) {t T : ℝ≥0} (htT : t ≤ T) (x : Elem m t →₀ ℝ) :
    TL hW T (Finsupp.mapDomain (extE htT) x) = TL hW t x := by
  simp only [TL, Finsupp.linearCombination_mapDomain]
  congr 1

lemma norm_ext_sub (hle : ∀ t, m t ≤ mΩ) {t T : ℝ≥0} (htT : t ≤ T) (x : Elem m t →₀ ℝ)
    (b : Lp ℝ 2 (μT P t)) :
    ‖eL (P := P) hle T (Finsupp.mapDomain (extE htT) x) - extL htT b‖ =
      ‖eL (P := P) hle t x - b‖ := by
  set g : ℝ × Ω → ℝ := fun z => x.sum (fun i c => c * efun i z) with hg
  have h1 : (eL (P := P) hle T (Finsupp.mapDomain (extE htT) x) : ℝ × Ω → ℝ) =ᵐ[μT P T]
      (winS t).indicator g := by
    filter_upwards [coe_eL (P := P) hle T (Finsupp.mapDomain (extE htT) x)] with z hz
    rw [hz, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    by_cases hzt : z ∈ winS (Ω := Ω) t
    · rw [Set.indicator_of_mem hzt]; rfl
    · rw [Set.indicator_of_notMem hzt]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      show x i * efun i z = 0
      rw [efun_zero i hzt, mul_zero]
  have h2 : (eL (P := P) hle t x : ℝ × Ω → ℝ) =ᵐ[μT P t] g := coe_eL (P := P) hle t x
  have h3 : (extL htT b : ℝ × Ω → ℝ) =ᵐ[μT P T] (winS t).indicator (b : ℝ × Ω → ℝ) :=
    (memLp_extL htT b).coeFn_toLp
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  have e1 : eLpNorm (⇑(eL (P := P) hle T (Finsupp.mapDomain (extE htT) x) - extL htT b)) 2 (μT P T)
      = eLpNorm ((winS t).indicator (g - (b : ℝ × Ω → ℝ))) 2 (μT P T) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (eL (P := P) hle T (Finsupp.mapDomain (extE htT) x))
      (extL htT b), h1, h3] with z hz hz1 hz3
    rw [hz, Pi.sub_apply, hz1, hz3]
    by_cases hzt : z ∈ winS (Ω := Ω) t <;> simp [Set.indicator_apply, hzt]
  have e2 : eLpNorm (⇑(eL (P := P) hle t x - b)) 2 (μT P t) =
      eLpNorm (g - (b : ℝ × Ω → ℝ)) 2 (μT P t) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (eL (P := P) hle t x) b, h2] with z hz hz2
    rw [hz, Pi.sub_apply, hz2]
    rfl
  rw [e1, e2, eLpNorm_indicator_eq_eLpNorm_restrict (winS_meas t), muT_restrict htT]

/-- **Horizon change.** -/
theorem rep_ext (hW : IncrHyp m W P) {t T : ℝ≥0} (htT : t ≤ T) {θ : Lp ℝ 2 P}
    {b : Lp ℝ 2 (μT P t)} (h : Rep hW t θ b) : Rep hW T θ (extL htT b) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.2.1
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le t (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  have h1 := rep_conv hW t h hx'
  refine rep_lim hW T (x := fun n => Finsupp.mapDomain (extE htT) (y n)) ?_ ?_
  · exact h1.congr (fun n => (TL_ext hW htT (y n)).symm)
  · refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine (tendsto_iff_norm_sub_tendsto_zero.1 hx').congr (fun n => ?_)
    exact (norm_ext_sub hW.le htT (y n) b).symm

/-- A horizon-`t` representative of the same integrand is `E[θ | m t]`. -/
theorem ce_of_rep (hW : IncrHyp m W P) {t T : ℝ≥0} (htT : t ≤ T) {f : ℝ × Ω → ℝ}
    (hfT : MemLp f 2 (μT P T)) (hft : MemLp f 2 (μT P t)) {θ θt : Lp ℝ 2 P}
    (h : Rep hW T θ (hfT.toLp f)) (ht : Rep hW t θt (hft.toLp f)) :
    (θt : Ω → ℝ) =ᵐ[P] condExp (m t) P θ := by
  have h2c : MemLp (condExp (m t) P (θ : Ω → ℝ)) 2 P := (Lp.memLp θ).condExp (by norm_num)
  have hφ : ((h2c.toLp _ : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] condExp (m t) P θ := h2c.coeFn_toLp
  have h1 := rep_ce hW T h t hφ
  have h2 := rep_ext hW htT ht
  have e : extL htT (hft.toLp f) = (memLp_res (Lp.memLp (hfT.toLp f)) t).toLp _ := by
    refine Lp.ext ?_
    have hr : ∀ᵐ z ∂(μT P T), z ∈ winS t → (hft.toLp f : ℝ × Ω → ℝ) z = f z := by
      rw [← ae_restrict_iff' (winS_meas t), muT_restrict htT]
      exact hft.coeFn_toLp
    filter_upwards [(memLp_extL htT (hft.toLp f)).coeFn_toLp,
      (memLp_res (Lp.memLp (hfT.toLp f)) t).coeFn_toLp, hfT.coeFn_toLp, hr] with z h1 h2 h3 h4
    rw [extL, h1, h2, ind_eq_winS, h3]
    by_cases hz : z ∈ winS (Ω := Ω) t
    · rw [h4 hz]
    · have : ind 0 t z.1 = 0 := by
        have hz' : z.1 ∉ Set.Ico (0 : ℝ) t := hz
        simp [ind, Set.indicator_apply, hz']
      rw [this, mul_zero, mul_zero]
  rw [e] at h2
  rw [rep_unique hW T h2 h1]
  exact hφ

end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Z7a.** A bounded library Ito integral is an `M.F`-martingale. -/
theorem Jmart (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] {H J : ℝ≥0 → Ω → ℝ}
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) H J) {t T : ℝ≥0} (htT : t ≤ T) :
    J t =ᵐ[M.P] condExp (M.F t) M.P (J T) := by
  have hb : ∀ S : ℝ≥0, MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT M.P S) := fun S =>
    MemLp.of_bound hHm.aestronglyMeasurable D (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hD _ _)
  obtain ⟨θ, hθ, hR⟩ := Z4m M hM hD0 hD hHm hJ T (hb T)
  obtain ⟨θt, hθt, hRt⟩ := Z4m M hM hD0 hD hHm hJ t (hb t)
  have h := ce_of_rep (incr_B M hM) htT (hb T) (hb t) hR hRt
  filter_upwards [hθt, h, condExp_congr_ae (m := M.F t) hθ] with ω h1 h2 h3
  rw [← h1, h2, h3]

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

lemma joint_meas {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun s => X s ω)
    (hm : ∀ s, Measurable (X s)) : Measurable (fun z : ℝ × Ω => X z.1.toNNReal z.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable hc hm
  exact h.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)

lemma A_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) :
    Continuous fun s : ℝ≥0 => ∫ u in (0 : ℝ)..s.val, etaT M u.toNNReal ω ^ 2 :=
  (intervalIntegral.continuous_primitive (fun a b =>
    (((etaT_cont M hM ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

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

lemma Zc_cont (M : Model p Ω) (hM : M.Standing) (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (ω : Ω) : Continuous fun s => Zc M Ic s ω := by
  unfold Zc
  exact Real.continuous_exp.comp (((hIc ω).neg).sub (continuous_const.mul (A_cont M hM ω)))

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

lemma Zc_zero (M : Model p Ω) (hI0 : ∀ ω, Ic 0 ω = 0) (ω : Ω) : Zc M Ic 0 ω = 1 := by
  simp [Zc, hI0]

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

/-- The process `Zc η'` whose size is stopped. -/
noncomputable def Xp (M : Model p Ω) (Ic : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  Zc M Ic u ω * etaT M u ω

/-- The hitting time of `|Zc η'| ≥ R`, capped at `T`. -/
noncomputable def tau (M : Model p Ω) (Ic : ℝ≥0 → Ω → ℝ) (R : ℝ) : Ω → ℝ≥0 :=
  hitR (Xp M Ic) R p.T

/-- The integrand `-Zc η'` clamped to `[-R, R]`. -/
noncomputable def Hcl (M : Model p Ω) (Ic : ℝ≥0 → Ω → ℝ) (R : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  max (-R) (min R (-(Zc M Ic s ω * etaT M s ω)))

lemma Xp_cont (M : Model p Ω) (hM : M.Standing) (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (ω : Ω) : Continuous fun s => Xp M Ic s ω :=
  (Zc_cont M hM hIc ω).mul (etaT_cont M hM ω)

lemma Xp_measF (M : Model p Ω) (hM : M.Standing)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (s : ℝ≥0) : StronglyMeasurable[M.F s] (Xp M Ic s) := by
  have h2 : Measurable[M.F s] (etaT M s) :=
    (η_meas M hM (min s p.T)).measurable.mono (M.F.mono (min_le_left _ _)) le_rfl
  exact ((Zc_measF M hM hIa hIm s).mul h2).stronglyMeasurable

lemma tau_stop (M : Model p Ω) (hM : M.Standing) (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (R : ℝ) (s : ℝ≥0) :
    MeasurableSet[M.F s] {ω | tau M Ic R ω ≤ s} :=
  hitR_isStopping M.F (Xp_measF M hM hIa hIm) (Xp_cont M hM hIc) R p.T s

/-- **Z7c.** Locality at the stopping time. -/
theorem loc (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P]
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hI0 : ∀ ω, Ic 0 ω = 0) {K : ℝ≥0 → Ω → ℝ}
    (hK : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) K)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + K t ω) (R : ℝ) {J : ℝ≥0 → Ω → ℝ}
    (hJc : ∀ ω, Continuous fun t => J t ω) (hJ0 : ∀ ω, J 0 ω = 0)
    (hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (Hcl M Ic R) J) :
    ∀ᵐ ω ∂M.P, J (tau M Ic R ω) ω = Zc M Ic (tau M Ic R ω) ω - 1 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hW := isStandardBrownian M hM
  have hgm : ∀ s, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s]
      (fun ω => -(Zc M Ic s ω * etaT M s ω)) := fun s =>
    ((Zc_cBP M hM hIa s).mul (etaT_cBP M hM s)).neg
  have hgc : ∀ ω, Continuous fun s => -(Zc M Ic s ω * etaT M s ω) := fun ω =>
    ((Zc_cont M hM hIc ω).mul (etaT_cont M hM ω)).neg
  have hHm : ∀ s, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s] (Hcl M Ic R s) :=
    fun s => measurable_const.max (measurable_const.min (hgm s))
  have hHc : ∀ ω, Continuous fun s => Hcl M Ic R s ω := fun ω =>
    continuous_const.max (continuous_const.min (hgc ω))
  have hloc : ∀ t, ∀ᵐ ω ∂M.P, t < tau M Ic R ω → J t ω = K t ω := by
    intro t
    refine hasBrownianItoIntegral_eq_on hW 0 0 hHm hHc hgm hgc hJ hK t
      {ω | t < tau M Ic R ω} (fun ω hω N i hi => ?_)
    have h1 : dyTime t N i < hitR (Xp M Ic) R p.T ω := (dyTime_le t hi).trans_lt hω
    have h2 := abs_lt_of_lt_hitR h1
    unfold Hcl
    refine clamp_eq ?_
    rw [abs_neg]
    exact h2.le
  haveI : Countable D := hDc.to_subtype
  have hall' : ∀ᵐ ω ∂M.P, ∀ t : D, (t.1 < tau M Ic R ω → J t.1 ω = K t.1 ω) ∧
      Zc M Ic t.1 ω = 1 + K t.1 ω :=
    ae_all_iff.2 (fun t => (hloc t.1).and (hKz t.1))
  have hall : ∀ᵐ ω ∂M.P, ∀ t ∈ D, (t < tau M Ic R ω → J t ω = K t ω) ∧
      Zc M Ic t ω = 1 + K t ω := by
    filter_upwards [hall'] with ω hω t htD
    exact hω ⟨t, htD⟩
  filter_upwards [hall] with ω hω
  have hf : Continuous fun t => J t ω - (Zc M Ic t ω - 1) :=
    (hJc ω).sub ((Zc_cont M hM hIc ω).sub continuous_const)
  rcases (show (0 : ℝ≥0) ≤ tau M Ic R ω from zero_le).eq_or_lt with h0 | hpos
  · rw [← h0, hJ0, Zc_zero M hI0]; ring
  · have hz : ∀ t ∈ Set.Iio (tau M Ic R ω) ∩ D, J t ω - (Zc M Ic t ω - 1) = 0 := by
      rintro t ⟨htτ, htD⟩
      obtain ⟨a, b⟩ := hω t htD
      rw [a htτ, b]; ring
    have hsub : Set.Iio (tau M Ic R ω) ⊆ closure (Set.Iio (tau M Ic R ω) ∩ D) :=
      hDd.open_subset_closure_inter isOpen_Iio
    have hmem : tau M Ic R ω ∈ closure (Set.Iio (tau M Ic R ω)) := by
      first
        | rw [closure_Iio' (a := tau M Ic R ω) ⟨0, hpos⟩]; exact Set.mem_Iic.2 le_rfl
        | exact isLUB_Iio.mem_closure ⟨0, hpos⟩
        | exact (closure_Iio' (a := tau M Ic R ω) ⟨0, hpos⟩).symm ▸ Set.mem_Iic.2 le_rfl
    have hcl : closure (Set.Iio (tau M Ic R ω) ∩ D) ⊆
        {t | J t ω - (Zc M Ic t ω - 1) = 0} :=
      (isClosed_eq hf continuous_const).closure_subset_iff.2 hz
    have hm2 : tau M Ic R ω ∈ closure (Set.Iio (tau M Ic R ω) ∩ D) := by
      have := closure_mono hsub hmem
      rwa [closure_closure] at this
    have h3 : J (tau M Ic R ω) ω - (Zc M Ic (tau M Ic R ω) ω - 1) = 0 := hcl hm2
    linarith

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

lemma hitR_mono {X : ℝ≥0 → Ω → ℝ} {R R' : ℝ} (h : R ≤ R') (T : ℝ≥0) (ω : Ω) :
    hitR X R T ω ≤ hitR X R' T ω := by
  unfold hitR
  refine csInf_le_csInf (OrderBot.bddBelow _) ⟨T, Or.inr rfl⟩ ?_
  rintro v (⟨h1, h2⟩ | h3)
  · exact Or.inl ⟨h1, h.trans h2⟩
  · exact Or.inr h3

/-- **Z7 (O7.3 core).** -/
theorem Z7 (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    (hC : ContHyp M) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {K : ℝ≥0 → Ω → ℝ}
    (hK : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) K)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + K t ω) :
    ∃ hf2 : MemLp (fun z : ℝ × Ω => -(Zc M Ic z.1.toNNReal z.2 * etaT M z.1.toNNReal z.2)) 2
        (μT M.P p.T),
      ∃ θ : Lp ℝ 2 M.P, (θ : Ω → ℝ) =ᵐ[M.P] (fun ω => Zc M Ic p.T ω - 1) ∧
        StochCalcO3.Rep (incr_B M hM) p.T θ (hf2.toLp _) := by
  set g : ℝ × Ω → ℝ := fun z => -(Zc M Ic z.1.toNNReal z.2 * etaT M z.1.toNNReal z.2) with hgdef
  -- the clamped integrands
  have hgm0 : ∀ s, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s]
      (fun ω => -(Zc M Ic s ω * etaT M s ω)) := fun s =>
    ((Zc_cBP M hM hIa s).mul (etaT_cBP M hM s)).neg
  have hgc0 : ∀ ω, Continuous fun s => -(Zc M Ic s ω * etaT M s ω) := fun ω =>
    ((Zc_cont M hM hIc ω).mul (etaT_cont M hM ω)).neg
  have hHcB : ∀ n : ℕ, ∀ s, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s]
      (Hcl M Ic n s) := fun n s => measurable_const.max (measurable_const.min (hgm0 s))
  have hHme : ∀ n : ℕ, ∀ s, Measurable (Hcl M Ic n s) := fun n s =>
    measurable_const.max (measurable_const.min
      (((Zc_meas M hM hIm s).mul (etaT_meas M hM s)).neg))
  have hHco : ∀ n : ℕ, ∀ ω, Continuous fun s => Hcl M Ic n s ω := fun n ω =>
    continuous_const.max (continuous_const.min (hgc0 ω))
  have hHbd : ∀ n : ℕ, ∀ s ω, |Hcl M Ic n s ω| ≤ n := fun n s ω => by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold Hcl
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  choose J hJc hJa hJm hJ0 hJ using fun n : ℕ =>
    hC (Hcl M Ic n) (hHcB n) (hHme n) (hHco n) n (hHbd n)
  have hHm : ∀ n : ℕ, Measurable (fun z : ℝ × Ω => Hcl M Ic n z.1.toNNReal z.2) := fun n =>
    joint_meas (hHco n) (hHme n)
  have hb : ∀ n : ℕ, MemLp (fun z : ℝ × Ω => Hcl M Ic n z.1.toNNReal z.2) 2 (μT M.P p.T) :=
    fun n => MemLp.of_bound (hHm n).aestronglyMeasurable n (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hHbd n _ _)
  choose θ hθ hR using fun n : ℕ =>
    Z4m M hM (Nat.cast_nonneg n) (hHbd n) (hHm n) (hJ n) p.T (hb n)
  have hKn : ∀ n : ℕ, ∀ t ≤ p.T, J n t =ᵐ[M.P] condExp (M.F t) M.P (θ n) := fun n t ht =>
    (Jmart M hM (Nat.cast_nonneg n) (hHbd n) (hHm n) (hJ n) ht).trans
      (condExp_congr_ae (hθ n)).symm
  -- the truncation sets
  set S : ℕ → Set (ℝ × Ω) := fun n => {z | z.1 < (tau M Ic n z.2 : ℝ)} with hSdef
  have hτm : ∀ n : ℕ, Measurable (fun ω => (tau M Ic n ω : ℝ)) := fun n =>
    measurable_coe_nnreal_real.comp
      (measurable_of_Iic (fun s => M.F.le s _ (tau_stop M hM hIc hIa hIm n s)))
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_lt measurable_fst ((hτm n).comp measurable_snd)
  have hwin : ∀ᵐ z ∂(μT M.P p.T), z ∈ StochCalcO3.winS p.T := by
    have h := ae_restrict_mem (μ := μT M.P p.T) (StochCalcO3.winS_meas (Ω := Ω) p.T)
    rwa [StochCalcO3.muT_restrict le_rfl] at h
  have hgm : Measurable g := (joint_meas (Xp_cont M hM hIc)
    (fun s => (Zc_meas M hM hIm s).mul (etaT_meas M hM s))).neg
  have hSg : ∀ n : ℕ, ∀ᵐ z ∂(μT M.P p.T), (S n).indicator g z =
      (if z.1 < (tau M Ic n z.2 : ℝ) then (1 : ℝ) else 0) * Hcl M Ic n z.1.toNNReal z.2 := by
    intro n
    filter_upwards [hwin] with z hz
    by_cases h : z.1 < (tau M Ic n z.2 : ℝ)
    · have h' : z ∈ S n := h
      rw [Set.indicator_of_mem h', if_pos h, one_mul]
      have hlt : z.1.toNNReal < hitR (Xp M Ic) n p.T z.2 :=
        (Real.toNNReal_lt_iff_lt_coe hz.1).2 h
      have h2 := abs_lt_of_lt_hitR hlt
      show g z = max (-(n : ℝ)) (min (n : ℝ) (-(Zc M Ic z.1.toNNReal z.2 * etaT M z.1.toNNReal z.2)))
      rw [clamp_eq (by rw [abs_neg]; exact h2.le)]
    · have h' : z ∉ S n := h
      rw [Set.indicator_of_notMem h', if_neg h, zero_mul]
  have hbn : ∀ n : ℕ, MemLp ((S n).indicator g) 2 (μT M.P p.T) := fun n =>
    (hb n).of_le ((hgm.indicator (hSm n)).aestronglyMeasurable) (by
      filter_upwards [hSg n] with z hz
      rw [hz]
      split_ifs <;> simp)
  -- Z5 at the stopping times
  have hZ5 : ∀ n : ℕ, ∃ θτ : Lp ℝ 2 M.P, (θτ : Ω → ℝ) =ᵐ[M.P] (fun ω => J n (tau M Ic n ω) ω) ∧
      StochCalcO3.Rep (incr_B M hM) p.T θτ ((hbn n).toLp _) := fun n =>
    StochCalcO3.Z5 (incr_B M hM) p.T (hR n) (hKn n) (fun ω t => (hJc n ω).continuousWithinAt)
      (fun ω => hitR_le _ _ _ ω) (tau_stop M hM hIc hIa hIm n) (by
        filter_upwards [(hbn n).coeFn_toLp, hSg n, (hb n).coeFn_toLp] with z h1 h2 h3
        rw [h1, h2, h3]
        rfl)
  choose θτ hθτ hRτ using hZ5
  have hθτZ : ∀ n : ℕ, (θτ n : Ω → ℝ) =ᵐ[M.P] fun ω => Zc M Ic (tau M Ic n ω) ω - 1 := fun n =>
    (hθτ n).trans (loc M hM hIc hIa hI0 hK hKz n (hJc n) (hJ0 n) (hJ n))
  -- the uniform L² bound (Z6)
  have hmin : ∀ n : ℕ, ∀ ω, min (tau M Ic n ω) p.T = tau M Ic n ω := fun n ω =>
    min_eq_left (hitR_le _ _ _ ω)
  have hfin : eLpNorm (Zc M Ic p.T) 2 M.P ≠ ⊤ := (Zc_memLp M h5 hIe).eLpNorm_ne_top
  have hbound : ∀ n : ℕ, ‖θτ n‖ ≤ (eLpNorm (Zc M Ic p.T) 2 M.P).toReal + 1 := by
    intro n
    have hZ6 := StochCalcO3.Z6 (P := M.P) (m := M.F) M.F.le (fun _ _ h => M.F.mono h) (Z := Zc M Ic)
      (fun t _ => (Zc_measF M hM hIa hIm t).stronglyMeasurable) (Zc_memLp M h5 hIe)
      (fun t ht => Zc_mart M h5 hIe ht) (fun ω t => (Zc_cont M hM hIc ω).continuousWithinAt)
      (tau_stop M hM hIc hIa hIm n)
    have e1 : eLpNorm (θτ n : Ω → ℝ) 2 M.P = eLpNorm ((fun ω => Zc M Ic (min (tau M Ic n ω) p.T) ω)
        - fun _ => (1 : ℝ)) 2 M.P := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hθτZ n] with ω hω
      rw [hω, Pi.sub_apply, hmin]
    have e2 := eLpNorm_sub_le (p := 2) hZ6.1.aestronglyMeasurable
      (aestronglyMeasurable_const (b := (1 : ℝ))) (by norm_num)
    have e3 : eLpNorm (fun _ : Ω => (1 : ℝ)) 2 M.P = 1 := by
      rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero _)]
      simp
    rw [Lp.norm_def]
    calc (eLpNorm (θτ n : Ω → ℝ) 2 M.P).toReal ≤ (eLpNorm (Zc M Ic p.T) 2 M.P + 1).toReal := by
          refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.one_ne_top⟩) ?_
          rw [e1]
          refine e2.trans ?_
          rw [e3]
          gcongr
          exact hZ6.2
      _ = (eLpNorm (Zc M Ic p.T) 2 M.P).toReal + 1 := by
          rw [ENNReal.toReal_add hfin ENNReal.one_ne_top, ENNReal.toReal_one]
  -- truncation limit
  have hmono : Monotone S := by
    intro a b hab z hz
    show z.1 < (tau M Ic b z.2 : ℝ)
    have hab' : (a : ℝ) ≤ b := Nat.cast_le.2 hab
    exact lt_of_lt_of_le hz (by exact_mod_cast hitR_mono hab' p.T z.2)
  have hbig : ∀ ω, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → tau M Ic n ω = p.T := by
    intro ω
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) p.T)).exists_bound_of_continuousOn
      ((Xp_cont M hM hIc ω).continuousOn)
    obtain ⟨n0, hn0⟩ := exists_nat_gt C
    refine ⟨n0, fun n hn => hitR_eq_T (fun v hv => ?_)⟩
    have h1 := hC v ⟨zero_le, hv⟩
    rw [Real.norm_eq_abs] at h1
    have h2 : (n0 : ℝ) ≤ n := Nat.cast_le.2 hn
    linarith
  have hcov : ∀ᵐ z ∂(μT M.P p.T), ∃ n, z ∈ S n := by
    filter_upwards [hwin] with z hz
    obtain ⟨n0, hn0⟩ := hbig z.2
    refine ⟨n0, ?_⟩
    show z.1 < (tau M Ic n0 z.2 : ℝ)
    rw [hn0 n0 le_rfl]
    exact hz.2
  obtain ⟨hf2, θl, hlim, hRl⟩ := StochCalcO3.rep_trunc (incr_B M hM) p.T hgm.aestronglyMeasurable
    hSm hmono hcov hbn hRτ hbound
  refine ⟨hf2, θl, ?_, hRl⟩
  obtain ⟨ns, hnsm, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ ω ∂M.P, ∀ n : ℕ, (θτ n : Ω → ℝ) ω = Zc M Ic (tau M Ic n ω) ω - 1 :=
    ae_all_iff.2 hθτZ
  filter_upwards [hns, hall] with ω h1 h2
  obtain ⟨n0, hn0⟩ := hbig ω
  have hev : ∀ᶠ i in atTop, (θτ (ns i) : Ω → ℝ) ω = Zc M Ic p.T ω - 1 := by
    filter_upwards [hnsm.tendsto_atTop.eventually (eventually_ge_atTop n0)] with i hi
    rw [h2, hn0 _ hi]
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (hev.mono fun i hi => hi.symm))

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
-- ===== slice of P8c066573M17 (probe/slice8c/cuts/r_z7.lean.src/P8c066573M17.lean): 0/73 top-level decls kept =====

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

-- ===== slice of P8c066573M18 (probe/slice8c/cuts/r_z7.lean.src/P8c066573M18.lean): 0/23 top-level decls kept =====

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



end StochCalcO3


namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


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

-- ===== slice of RUb (probe/slice8c/cuts/r_z7.lean.src/RUb.lean): 0/17 top-level decls kept =====

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





end StochCalcQ2U

end StochCalcP6

-- ===== slice of __current__ (probe/slice8c/cuts/r_z7.lean.src/__current__.lean): 0/98 top-level decls kept =====

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
    {K : ℝ≥0 → Ω → ℝ}
    (hK : HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) (fun s ω => -(Z s ω * M.η (min s p.T) ω)) K)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Z t ω = 1 + K t ω)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) p.T)).prod M.P) :
    ∃ hf2 : MemLp (fun z : ℝ × Ω => -(Z z.1.toNNReal z.2 * M.η (min z.1.toNNReal p.T) z.2)) 2 μ,
      ∃ θ : Lp ℝ 2 M.P, (θ : Ω → ℝ) =ᵐ[M.P] (fun ω => Z p.T ω - 1) ∧
      (θ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 M.P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (M.B v ω - M.B u ω)) 2 M.P, g = h.toLp _} : Set (Lp ℝ 2 M.P)) ∧
      hf2.toLp _ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ u v : ℝ≥0, u ≤ v → v ≤ p.T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
          ∫ z, (hf2.toLp _ : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) := by
  obtain rfl : W = StochCalcBr.W M := funext fun t => funext fun ω => hW t ω
  obtain rfl : Z = StochCalcP6.StochCalcZ3.Zc M Ic := funext fun s => funext fun ω => hZ s ω
  subst hμ
  obtain ⟨hf2, θ, h1, h2⟩ := StochCalcP6.StochCalcZ7d.Z7 M hM h5 hC hIc hIa hIm hI0 hIe hK hKz
  have h3 := (StochCalcP6.StochCalcRU.rep_iff (StochCalcP6.StochCalcO3M.incr_B M hM) p.T θ _).1 h2
  unfold StochCalcP6.StochCalcRU.RepU at h3
  exact ⟨hf2, θ, h1, h3⟩
