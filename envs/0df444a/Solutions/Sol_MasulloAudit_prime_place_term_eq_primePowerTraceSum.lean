-- Prove2me | solution 1 for MasulloAudit.prime_place_term_eq_primePowerTraceSum
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:35:27.076462+00:00
-- url     : https://prove2.me/submissions/41fd4c8f-fb18-4544-94b6-3abef11cea1b

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped Topology ContDiff NNReal ENNReal Pointwise

namespace PrimePlaceAux

variable {p : ℕ} [hp : Fact p.Prime]

lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

/-- In `ℚ_[p]`, norms below `1` are at most `p⁻¹`. -/
lemma norm_le_inv_of_lt_one {x : ℚ_[p]} (hx : ‖x‖ < 1) : ‖x‖ ≤ (p : ℝ)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rw [Padic.norm_eq_zpow_neg_valuation h0] at hx ⊢
  have h1 : -x.valuation < 0 := by
    by_contra h
    push Not at h
    have := one_le_zpow₀ (one_lt_p (p := p)).le h
    linarith
  calc (p : ℝ) ^ (-x.valuation) ≤ (p : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (one_lt_p (p := p)).le (by omega)
    _ = (p : ℝ)⁻¹ := zpow_neg_one _

lemma ball_decomp :
    closedBall (0 : ℚ_[p]) 1 = ⋃ n ∈ Finset.range p, closedBall (n : ℚ_[p]) (p : ℝ)⁻¹ := by
  ext x
  simp only [mem_iUnion, Finset.mem_range, mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · intro hx
    let z : ℤ_[p] := ⟨x, hx⟩
    obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range z
    refine ⟨n, hn, norm_le_inv_of_lt_one ?_⟩
    have : ‖z - (n : ℤ_[p])‖ < 1 := PadicInt.mem_nonunits.mp hmem
    simpa [PadicInt.norm_def] using this
  · rintro ⟨n, -, hn⟩
    have h1 : ‖(n : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (n : ℤ)
    have h2 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_lt_p (p := p)).le
    calc ‖x‖ = ‖(x - n) + n‖ := by ring_nf
      _ ≤ max ‖x - n‖ ‖(n : ℚ_[p])‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (hn.trans h2) h1

lemma ball_disjoint :
    (↑(Finset.range p) : Set ℕ).PairwiseDisjoint
      (fun n : ℕ => closedBall (n : ℚ_[p]) (p : ℝ)⁻¹) := by
  intro n hn m hm hnm
  simp only [Finset.coe_range, mem_Iio] at hn hm
  rw [Function.onFun, Set.disjoint_left]
  intro x hxn hxm
  rw [mem_closedBall, dist_eq_norm] at hxn hxm
  have hlt : ‖(((n : ℤ) - m : ℤ) : ℚ_[p])‖ < 1 := by
    have : ‖(n : ℚ_[p]) - m‖ ≤ (p : ℝ)⁻¹ := by
      calc ‖(n : ℚ_[p]) - m‖ = ‖(x - m) + (n - x)‖ := by ring_nf
        _ ≤ max ‖x - m‖ ‖(n : ℚ_[p]) - x‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ _ := max_le hxm (by rw [norm_sub_rev]; exact hxn)
    have h2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_p (p := p))
    push_cast
    linarith
  rw [Padic.norm_intCast_lt_one_iff] at hlt
  apply hnm
  have := Int.eq_zero_of_abs_lt_dvd hlt (by
    rw [abs_lt]; constructor <;> omega)
  omega

variable [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]

/-- The unit `p ∈ ℚ_[p]ˣ`. -/
noncomputable def pu : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (by exact_mod_cast hp.out.ne_zero)

lemma unit_smul_set (u : ℚ_[p]ˣ) (s : Set ℚ_[p]) : u • s = (u : ℚ_[p]) • s := by
  ext x; simp [Set.mem_smul_set, Units.smul_def]

lemma ball_pos : μ (closedBall (0 : ℚ_[p]) 1) ≠ 0 :=
  (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).measure_ne_zero μ
    ⟨0, by simp⟩

lemma ball_fin : μ (closedBall (0 : ℚ_[p]) 1) ≠ (⊤ : ℝ≥0∞) :=
  (isCompact_closedBall _ _).measure_lt_top.ne

include μ in
lemma char_pu : distribHaarChar ℚ_[p] (pu (p := p)) = (p : ℝ≥0)⁻¹ := by
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (ball_pos μ) (ball_fin μ)
  have hsm : (pu (p := p)) • closedBall (0 : ℚ_[p]) 1 = closedBall 0 (p : ℝ)⁻¹ := by
    rw [unit_smul_set, _root_.smul_closedBall _ _ zero_le_one]
    simp [pu, Padic.norm_p]
  rw [hsm]
  have hdec := congrArg μ (ball_decomp (p := p))
  rw [measure_biUnion_finset ball_disjoint (fun _ _ => measurableSet_closedBall)] at hdec
  simp_rw [Measure.addHaar_closedBall_center] at hdec
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hdec
  rw [hdec, ← mul_assoc]
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [ENNReal.coe_inv (by exact_mod_cast hp.out.ne_zero), ENNReal.coe_natCast,
    ENNReal.inv_mul_cancel hp0 (ENNReal.natCast_ne_top p), one_mul]

include μ in
lemma char_pu_zpow (k : ℤ) :
    distribHaarChar ℚ_[p] ((pu (p := p)) ^ (-k)) = (p : ℝ≥0) ^ k := by
  rw [map_zpow' _ ?_, char_pu μ, inv_zpow', neg_neg]
  intro x
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

/-- The shells `{‖x‖ = p^k}`. -/
lemma shell_eq (k : ℤ) :
    ((pu (p := p)) ^ (-k)) • sphere (0 : ℚ_[p]) 1 = sphere 0 ((p : ℝ) ^ k) := by
  rw [unit_smul_set, smul_sphere' (Units.ne_zero _)]
  simp [pu, Padic.norm_p]

lemma shell_measure (k : ℤ) :
    μ (sphere (0 : ℚ_[p]) ((p : ℝ) ^ k)) = ((p : ℝ≥0) ^ k : ℝ≥0) * μ (sphere 0 1) := by
  rw [← shell_eq, ← distribHaarChar_mul, char_pu_zpow μ]

lemma shell_real (k : ℤ) :
    μ.real (sphere (0 : ℚ_[p]) ((p : ℝ) ^ k)) = (p : ℝ) ^ k * μ.real (sphere 0 1) := by
  simp [Measure.real, shell_measure μ k, ENNReal.toReal_mul]

lemma shell_fin (r : ℝ) : μ (sphere (0 : ℚ_[p]) r) ≠ (⊤ : ℝ≥0∞) :=
  ((isCompact_closedBall (0 : ℚ_[p]) r).measure_lt_top.trans_le'
    (measure_mono sphere_subset_closedBall)).ne

lemma unit_sphere_pos : 0 < μ.real (sphere (0 : ℚ_[p]) 1) := by
  apply ENNReal.toReal_pos _ (shell_fin μ 1)
  exact (IsUltrametricDist.isOpen_sphere 0 one_ne_zero).measure_ne_zero μ ⟨1, by simp⟩


open MasulloRH

omit [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] in
include p hp in
lemma exists_N (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ N : ℕ, ∀ k : ℤ, φ ((p : ℝ) ^ k) ≠ 0 → -(N : ℤ) ≤ k ∧ k ≤ N := by
  obtain ⟨-, hc, hpos, -⟩ := hφ
  rcases (tsupport φ).eq_empty_or_nonempty with he | hne
  · refine ⟨0, fun k hk => absurd (subset_tsupport φ (Function.mem_support.mpr hk)) ?_⟩
    simp [he]
  obtain ⟨m, hmK, hmin⟩ := hc.isCompact.exists_isMinOn hne continuousOn_id
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  have hm0 : 0 < m := hpos hmK
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max R m⁻¹) (one_lt_p (p := p))
  refine ⟨N, fun k hk => ?_⟩
  have hx := subset_tsupport φ (Function.mem_support.mpr hk)
  have h1 : m ≤ (p : ℝ) ^ k := hmin hx
  have h2 : (p : ℝ) ^ k ≤ R := hR hx
  have hpN : (0 : ℝ) < (p : ℝ) ^ N := pow_pos p_pos N
  constructor
  · by_contra hlt
    push Not at hlt
    have h3 : (p : ℝ) ^ k < (p : ℝ) ^ (-(N : ℤ)) := zpow_lt_zpow_right₀ one_lt_p hlt
    rw [zpow_neg, zpow_natCast] at h3
    have h4 : ((p : ℝ) ^ N)⁻¹ < m := by
      rw [inv_lt_comm₀ hpN hm0]; exact lt_of_le_of_lt (le_max_right _ _) hN
    linarith
  · by_contra hlt
    push Not at hlt
    have h3 : (p : ℝ) ^ (N : ℤ) < (p : ℝ) ^ k := zpow_lt_zpow_right₀ one_lt_p hlt
    rw [zpow_natCast] at h3
    have := lt_of_le_of_lt (le_max_left _ _) hN
    linarith

/-- Real weight of the shell `‖g‖ = p^k`. -/
noncomputable def w (p : ℕ) (k : ℤ) : ℝ :=
  ((p : ℝ) ^ k) ^ (1/2 : ℝ) / max 1 ((p : ℝ) ^ k) * (1 / (p : ℝ) ^ k)

omit [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] in
lemma integrand_on_shell (φ : ℝ → ℂ) (hφ1 : φ 1 = 0) (g : ℚ_[p]) (k : ℤ)
    (hg : ‖g‖ = (p : ℝ) ^ k) :
    φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) =
      φ ((p : ℝ) ^ k) * (w p k : ℂ) := by
  rw [hg]
  by_cases h : φ ((p : ℝ) ^ k) = 0
  · simp [h]
  have hne : ‖g‖ ≠ ‖(1 : ℚ_[p])‖ := by
    rw [hg, norm_one]; intro h'; rw [h', hφ1] at h; exact h rfl
  have h1g : ‖1 - g‖ = max 1 ((p : ℝ) ^ k) := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rwa [norm_neg, ne_comm]),
      norm_neg, norm_one, hg]
  rw [h1g, w]

omit [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] in
lemma integrand_eq_sum (φ : ℝ → ℂ) (hφ1 : φ 1 = 0) (N : ℕ)
    (hN : ∀ k : ℤ, φ ((p : ℝ) ^ k) ≠ 0 → -(N : ℤ) ≤ k ∧ k ≤ N) (g : ℚ_[p]) :
    φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        (sphere (0 : ℚ_[p]) ((p : ℝ) ^ k)).indicator (fun _ => φ ((p : ℝ) ^ k) * (w p k : ℂ)) g := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [Finset.sum_eq_zero]
    · simp
    intro k _
    have : (0 : ℚ_[p]) ∉ sphere (0 : ℚ_[p]) ((p : ℝ) ^ k) := by
      simp only [mem_sphere, dist_self]; exact (zpow_pos p_pos k).ne
    simp [Set.indicator_of_notMem this]
  set j : ℤ := -g.valuation
  have hgj : ‖g‖ = (p : ℝ) ^ j := Padic.norm_eq_zpow_neg_valuation hg0
  rw [integrand_on_shell φ hφ1 g j hgj]
  have hmem : ∀ k, g ∈ sphere (0 : ℚ_[p]) ((p : ℝ) ^ k) ↔ k = j := by
    intro k
    rw [mem_sphere_zero_iff_norm, hgj]
    exact ⟨fun h => (zpow_right_injective₀ p_pos one_lt_p.ne' h).symm, fun h => h ▸ rfl⟩
  by_cases hj : j ∈ Finset.Icc (-(N : ℤ)) N
  · rw [Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem ((hmem j).2 rfl)]
    · intro k _ hk; rw [Set.indicator_of_notMem (fun h => hk ((hmem k).1 h))]
    · intro h; exact absurd hj h
  · have : φ ((p : ℝ) ^ j) = 0 := by
      by_contra h; exact hj (Finset.mem_Icc.mpr (hN j h))
    rw [this, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [Set.indicator_of_notMem]
    intro h; rw [(hmem k).1 h] at hk; exact hj hk

lemma sum_Icc_eq (h : ℤ → ℂ) (N : ℕ) (hz : ∀ k ∉ Finset.Icc (-(N : ℤ)) N, h k = 0) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N, h k = h 0 + ∑' n : ℕ, (h ((n : ℤ) + 1) + h (-((n : ℤ) + 1))) := by
  have hs : Summable h := summable_of_ne_finset_zero hz
  have hs1 : Summable (fun n : ℕ => h n) := hs.comp_injective Nat.cast_injective
  have hs2 : Summable (fun n : ℕ => h (-((n : ℤ) + 1))) :=
    hs.comp_injective (fun a b hab => by simpa using hab)
  rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ) hz, tsum_of_nat_of_neg_add_one hs1 hs2, hs1.tsum_eq_zero_add]
  have hs3 : Summable (fun n : ℕ => h ((n + 1 : ℕ) : ℤ)) :=
    hs.comp_injective (fun a b hab => by simpa using hab)
  push_cast at hs3 ⊢
  rw [add_assoc, hs3.tsum_add hs2]

end PrimePlaceAux

open MasulloRH PrimePlaceAux

/-- Prime-place term of Masullo, Theorem 12.5.1.1 (ζ case), at a prime `p`. -/
theorem solution (p : ℕ) [hp : Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} μ ∧
    Summable (fun k : ℕ => primePowerTraceTerm φ (⟨p, hp.out⟩, k)) ∧
    ((Real.log p / μ.real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂μ =
      ∑' k : ℕ, primePowerTraceTerm φ (⟨p, hp.out⟩, k) := by
  obtain ⟨N, hN⟩ := exists_N (p := p) φ hφ
  have hφ1 : φ 1 = 0 := hφ.2.2.2
  set F : ℚ_[p] → ℂ := fun g => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ)
  have hF : F = fun g => ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      (sphere (0 : ℚ_[p]) ((p : ℝ) ^ k)).indicator (fun _ => φ ((p : ℝ) ^ k) * (w p k : ℂ)) g :=
    funext (integrand_eq_sum φ hφ1 N hN)
  have hint_k : ∀ k ∈ Finset.Icc (-(N : ℤ)) N, Integrable
      ((sphere (0 : ℚ_[p]) ((p : ℝ) ^ k)).indicator (fun _ => φ ((p : ℝ) ^ k) * (w p k : ℂ))) μ :=
    fun k _ => (integrable_indicator_iff isClosed_sphere.measurableSet).mpr
      (integrableOn_const (shell_fin μ _))
  have hFint : Integrable F μ := by rw [hF]; exact integrable_finset_sum _ hint_k
  -- the zeta-side function on ℤ
  set h : ℤ → ℂ := fun k => ((Real.log p * (p : ℝ) ^ k * w p k : ℝ) : ℂ) * φ ((p : ℝ) ^ k)
  have hz : ∀ k ∉ Finset.Icc (-(N : ℤ)) N, h k = 0 := by
    intro k hk
    have : φ ((p : ℝ) ^ k) = 0 := by
      by_contra hc; exact hk (Finset.mem_Icc.mpr (hN k hc))
    simp [h, this]
  have h0 : h 0 = 0 := by simp [h, hφ1]
  have hterm : ∀ n : ℕ, primePowerTraceTerm φ (⟨p, hp.out⟩, n) =
      h ((n : ℤ) + 1) + h (-((n : ℤ) + 1)) := by
    intro n
    set x : ℝ := (p : ℝ) ^ (n + 1)
    have hx1 : 1 ≤ x := one_le_pow₀ one_lt_p.le
    have hx0 : 0 < x := by linarith
    have e1 : (p : ℝ) ^ ((n : ℤ) + 1) = x := by
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    have e2 : (p : ℝ) ^ (-((n : ℤ) + 1)) = x⁻¹ := by rw [zpow_neg, e1]
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have w1 : (p : ℝ) ^ ((n : ℤ) + 1) * w p ((n : ℤ) + 1) = 1 / Real.sqrt x := by
      rw [w, e1, ← Real.sqrt_eq_rpow, max_eq_right hx1]
      have := Real.sq_sqrt hx0.le
      field_simp
      nlinarith
    have w2 : (p : ℝ) ^ (-((n : ℤ) + 1)) * w p (-((n : ℤ) + 1)) = 1 / Real.sqrt x := by
      rw [w, e2, ← Real.sqrt_eq_rpow, max_eq_left (inv_le_one_of_one_le₀ hx1), Real.sqrt_inv]
      field_simp
    simp only [primePowerTraceTerm, h]
    rw [mul_assoc, w1, mul_assoc, w2, e1, e2]
    push_cast
    ring
  refine ⟨hFint.integrableOn, ?_, ?_⟩
  · rw [funext hterm]
    have hs : Summable h := summable_of_ne_finset_zero hz
    have hs3 : Summable (fun n : ℕ => h ((n + 1 : ℕ) : ℤ)) :=
      hs.comp_injective (fun a b hab => by simpa using hab)
    have hs2 : Summable (fun n : ℕ => h (-((n : ℤ) + 1))) :=
      hs.comp_injective (fun a b hab => by simpa using hab)
    push_cast at hs3
    exact hs3.add hs2
  · rw [funext hterm, ← zero_add (∑' n : ℕ, _), ← h0, ← sum_Icc_eq h N hz]
    have hset : {g : ℚ_[p] | ‖g‖ = 1} = sphere (0 : ℚ_[p]) 1 := by ext; simp
    rw [hset, setIntegral_eq_integral_of_forall_compl_eq_zero (fun g hg => by
      simp only [mem_setOf_eq, not_not] at hg; simp [hg])]
    change _ * ∫ g, F g ∂μ = _
    rw [hF, integral_finset_sum _ hint_k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_indicator_const _ isClosed_sphere.measurableSet, shell_real μ k]
    have hm : (μ.real (sphere (0 : ℚ_[p]) 1) : ℂ) ≠ 0 := by
      exact_mod_cast (unit_sphere_pos μ).ne'
    simp only [h, Complex.real_smul]
    push_cast
    field_simp

