-- Prove2me | solution 1 for MasulloAudit.geometric_side_eq_formal_lhs
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:38:15.202406+00:00
-- url     : https://prove2.me/submissions/c8ba0683-beb8-4c6f-8faa-3289ec8f8fcc

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

open MasulloRH PrimePlaceAux in
/-- Prime-place term (copied from Prime_Sol). -/
theorem prime_solution (p : ℕ) [hp : Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
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

namespace RealPlaceAux

/-- Pointwise algebra on `(1,∞)`. -/
lemma w_pos_side (t : ℝ) (ht : 1 < t) :
    (|t| ^ (1/2 : ℝ) / |1 - t| * (1 / |t|)) + (|-t| ^ (1/2 : ℝ) / |1 - -t| * (1 / |-t|))
      = 2 * (Real.sqrt t / (t ^ 2 - 1)) := by
  have h0 : 0 < t := by linarith
  rw [abs_neg, abs_of_pos h0, abs_of_neg (by linarith : 1 - t < 0),
    abs_of_pos (by linarith : (0:ℝ) < 1 - -t), ← Real.sqrt_eq_rpow]
  obtain ⟨s, hs1, rfl⟩ : ∃ s, 1 < s ∧ t = s ^ 2 := by
    refine ⟨Real.sqrt t, ?_, (Real.sq_sqrt h0.le).symm⟩
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one ht
  have hs : 0 < s := by linarith
  rw [Real.sqrt_sq hs.le]
  have h1 : s ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (s ^ 2) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have h4 : 1 - -s ^ 2 ≠ 0 := by nlinarith
  have e : (s ^ 2) ^ 2 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by ring
  have h5 : s ^ 2 + 1 ≠ 0 := by positivity
  rw [e]
  field_simp
  ring

lemma w_neg_side (t : ℝ) (ht : 1 < t) :
    |-(t ^ 2)⁻¹| * ((|t⁻¹| ^ (1/2 : ℝ) / |1 - t⁻¹| * (1 / |t⁻¹|)) +
      (|-t⁻¹| ^ (1/2 : ℝ) / |1 - -t⁻¹| * (1 / |-t⁻¹|)))
      = 2 * (Real.sqrt t / (t ^ 2 - 1)) := by
  have h0 : 0 < t := by linarith
  have hi : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hi0 : 0 < t⁻¹ := inv_pos.2 h0
  rw [abs_neg, abs_neg, abs_of_pos hi0, abs_of_pos (by linarith : 0 < 1 - t⁻¹),
    abs_of_pos (by linarith : (0:ℝ) < 1 - -t⁻¹), abs_of_pos (by positivity : 0 < (t ^ 2)⁻¹),
    ← Real.sqrt_eq_rpow, Real.sqrt_inv]
  obtain ⟨s, hs1, rfl⟩ : ∃ s, 1 < s ∧ t = s ^ 2 := by
    refine ⟨Real.sqrt t, ?_, (Real.sq_sqrt h0.le).symm⟩
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one ht
  have hs : 0 < s := by linarith
  rw [Real.sqrt_sq hs.le]
  have h1 : s ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (s ^ 2) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : 1 - (s ^ 2)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h; field_simp at h; nlinarith
  have h4 : 1 - -(s ^ 2)⁻¹ ≠ 0 := by
    have : 0 < (s^2)⁻¹ := by positivity
    linarith
  have h6 : 1 + s ^ 2 ≠ 0 := by positivity
  have e : (s ^ 2) ^ 2 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by ring
  have h5 : s ^ 2 + 1 ≠ 0 := by positivity
  have e1 : 1 - (s ^ 2)⁻¹ = (s ^ 2 - 1) / s ^ 2 := by field_simp
  have e2 : 1 - -(s ^ 2)⁻¹ = (s ^ 2 + 1) / s ^ 2 := by field_simp; ring
  rw [e, e1, e2]
  field_simp
  ring

end RealPlaceAux

open RealPlaceAux in
theorem real_solution (φ : ℝ → ℂ) (hφ : MasulloRH.IsRationalTraceTest φ) :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (1/2 : ℂ) * ∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ) =
      ∫ t in Ioi (1:ℝ), MasulloRH.realTraceIntegrand φ t := by
  obtain ⟨hsmooth, hcpt, hsupp, h1⟩ := hφ
  set w : ℝ → ℝ := fun x => |x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) with hw
  set f : ℝ → ℂ := fun x => φ |x| * (w x : ℂ) with hf
  -- support bounds
  have hK : IsCompact (tsupport φ) := hcpt
  obtain ⟨ε, hε, hεball⟩ : ∃ ε > 0, Metric.ball (0:ℝ) ε ⊆ (tsupport φ)ᶜ := by
    have : (tsupport φ)ᶜ ∈ 𝓝 (0:ℝ) := by
      apply (isClosed_tsupport φ).isOpen_compl.mem_nhds
      intro h; exact lt_irrefl (0:ℝ) (hsupp h)
    exact Metric.mem_nhds_iff.1 this
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hzero : ∀ y, φ y ≠ 0 → ε ≤ |y| ∧ |y| ≤ R := by
    intro y hy
    have hy' : y ∈ tsupport φ := subset_tsupport _ hy
    refine ⟨?_, ?_⟩
    · by_contra hlt; push Not at hlt
      exact hεball (by simpa [Metric.mem_ball] using hlt) hy'
    · simpa [Metric.mem_closedBall] using hR hy'
  obtain ⟨C, hC⟩ := hsmooth.lipschitzWith_of_hasCompactSupport hcpt (by simp)
  have hlip : ∀ y, ‖φ y‖ ≤ C * |y - 1| := by
    intro y
    have := hC.dist_le_mul y 1
    simpa [h1, Real.dist_eq] using this
  -- f is bounded
  have hbound : ∀ x, ‖f x‖ ≤ C / Real.sqrt ε := by
    intro x
    by_cases hx : φ |x| = 0
    · simp only [hf, hx, zero_mul, norm_zero]; positivity
    obtain ⟨hεx, -⟩ := hzero _ hx
    rw [abs_abs] at hεx
    have hxpos : 0 < |x| := lt_of_lt_of_le hε hεx
    simp only [hf, hw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← Real.sqrt_eq_rpow]
    have hA : ‖φ |x|‖ ≤ C * |1 - x| := by
      refine (hlip _).trans (mul_le_mul_of_nonneg_left ?_ C.2)
      rw [abs_sub_comm 1 x]
      simpa using abs_abs_sub_abs_le x 1
    have hsq : 0 < Real.sqrt |x| := Real.sqrt_pos.2 hxpos
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt |x| / |1 - x|),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / |x|)]
    by_cases h1x : |1 - x| = 0
    · simp [h1x]; positivity
    have h1x' : 0 < |1 - x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h1x)
    calc ‖φ |x|‖ * (Real.sqrt |x| / |1 - x| * (1 / |x|))
        ≤ (C * |1 - x|) * (Real.sqrt |x| / |1 - x| * (1 / |x|)) := by
          gcongr
      _ = C / Real.sqrt |x| := by
          have : Real.sqrt |x| ^ 2 = |x| := Real.sq_sqrt hxpos.le
          field_simp
          rw [this]
      _ ≤ C / Real.sqrt ε := by
          gcongr
  have hmeas : AEStronglyMeasurable f volume := by
    have hc : Continuous φ := hsmooth.continuous
    apply AEStronglyMeasurable.mul
    · exact (hc.comp continuous_abs).aestronglyMeasurable
    · apply Measurable.aestronglyMeasurable
      apply Complex.measurable_ofReal.comp
      simp only [hw]; fun_prop
  have hfint : Integrable f := by
    have hsub : Function.support f ⊆ Metric.closedBall 0 R := by
      intro x hx
      have : φ |x| ≠ 0 := by
        intro h; apply hx; simp [hf, h]
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      simpa using (hzero _ this).2
    rw [← integrableOn_iff_integrable_of_support_subset hsub]
    exact Measure.integrableOn_of_bounded (measure_closedBall_lt_top).ne
      hmeas (Filter.Eventually.of_forall hbound)
  refine ⟨hfint.integrableOn, ?_⟩
  -- reduce to (0, ∞)
  have hset : ∫ x in {x : ℝ | x ≠ 0}, f x = ∫ x in Iic (0:ℝ) ∪ Ioi 0, f x := by
    apply setIntegral_congr_set
    rw [Iic_union_Ioi, ae_eq_univ]
    have : {x : ℝ | x ≠ 0}ᶜ = {0} := by ext; simp
    rw [this]; exact measure_singleton _
  have hsplit : ∫ x in {x : ℝ | x ≠ 0}, f x
      = (∫ y in Ioi (0:ℝ), f (-y)) + ∫ y in Ioi (0:ℝ), f y := by
    rw [hset, setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hfint.integrableOn hfint.integrableOn]
    have := integral_comp_neg_Ioi 0 f
    rw [neg_zero] at this
    rw [← this]
  set F : ℝ → ℂ := fun y => f (-y) + f y with hF
  have hFint : Integrable F := hfint.comp_neg.add hfint
  have hsplit2 : ∫ x in {x : ℝ | x ≠ 0}, f x = ∫ y in Ioi (0:ℝ), F y := by
    rw [hsplit, hF, integral_add hfint.comp_neg.integrableOn hfint.integrableOn]
  -- split (0,∞) = (0,1) ∪ [1,∞)
  have himg : (fun t : ℝ => t⁻¹) '' Ioi 1 = Ioo 0 1 := by
    ext y; constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨inv_pos.2 (by linarith [mem_Ioi.1 ht]), inv_lt_one_of_one_lt₀ ht⟩
    · rintro ⟨hy0, hy1⟩
      exact ⟨y⁻¹, (one_lt_inv₀ hy0).2 hy1, inv_inv y⟩
  have hderiv : ∀ t ∈ Ioi (1:ℝ), HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) (Ioi 1) t :=
    fun t ht => (hasDerivAt_inv (by linarith [mem_Ioi.1 ht] : t ≠ 0)).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t⁻¹) (Ioi 1) := inv_injective.injOn
  have hcov : ∫ y in Ioo (0:ℝ) 1, F y = ∫ t in Ioi (1:ℝ), |-(t ^ 2)⁻¹| • F t⁻¹ := by
    rw [← himg]
    exact integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj F
  have hcovint : IntegrableOn (fun t : ℝ => |-(t ^ 2)⁻¹| • F t⁻¹) (Ioi 1) := by
    rw [← integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj F,
      himg]
    exact hFint.integrableOn
  have hsplit3 : ∫ y in Ioi (0:ℝ), F y
      = ∫ t in Ioi (1:ℝ), (|-(t ^ 2)⁻¹| • F t⁻¹ + F t) := by
    rw [← Ioo_union_Ici_eq_Ioi zero_lt_one, setIntegral_union ((Iio_disjoint_Ici le_rfl).mono_left Ioo_subset_Iio_self)
      measurableSet_Ici hFint.integrableOn hFint.integrableOn, integral_Ici_eq_integral_Ioi,
      hcov, integral_add hcovint hFint.integrableOn]
  rw [hsplit2, hsplit3, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht1 : 1 < t := ht
  have ht0 : 0 < t := by linarith
  have hA := w_pos_side t ht1
  have hB := w_neg_side t ht1
  have hA' : (w (-t) : ℂ) + (w t : ℂ) = 2 * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ) := by
    rw [add_comm]; exact_mod_cast hA
  have hB' : ((|-(t ^ 2)⁻¹| : ℝ) : ℂ) * ((w (-t⁻¹) : ℂ) + (w t⁻¹ : ℂ))
      = 2 * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ) := by
    rw [add_comm (w (-t⁻¹) : ℂ)]; exact_mod_cast hB
  rw [abs_neg] at hB'
  simp only [hF, hf, MasulloRH.realTraceIntegrand, Complex.real_smul, abs_neg,
    abs_of_pos ht0, abs_of_pos (inv_pos.2 ht0)]
  linear_combination (1/2 : ℂ) * φ t * hA' + (1/2 : ℂ) * φ t⁻¹ * hB'

namespace GeomSideAux

open MasulloRH

/-- Admissible tests are supported in a compact subinterval `[ε, R]` of `(0, ∞)`. -/
lemma support_bounds (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ, 1 ≤ x → (φ x ≠ 0 ∨ φ x⁻¹ ≠ 0) → x ≤ M := by
  obtain ⟨-, hc, hpos, -⟩ := hφ
  rcases (tsupport φ).eq_empty_or_nonempty with he | hne
  · refine ⟨1, le_rfl, fun x _ hx => ?_⟩
    exfalso
    rcases hx with hx | hx
    · have := subset_tsupport φ (Function.mem_support.mpr hx); simp [he] at this
    · have := subset_tsupport φ (Function.mem_support.mpr hx); simp [he] at this
  obtain ⟨m, hmK, hmin⟩ := hc.isCompact.exists_isMinOn hne continuousOn_id
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  have hm0 : 0 < m := hpos hmK
  refine ⟨max 1 (max R m⁻¹), le_max_left _ _, fun x hx1 hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rcases hx with hx | hx
  · have := hR (subset_tsupport φ (Function.mem_support.mpr hx))
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h1 : m ≤ x⁻¹ := hmin (subset_tsupport φ (Function.mem_support.mpr hx))
    have : x ≤ m⁻¹ := by
      rw [le_inv_comm₀ hx0 hm0]; exact h1
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Nonzero prime-power terms have bounded prime and exponent. -/
lemma term_ne_zero_bound (φ : ℝ → ℂ) (M : ℝ)
    (hM : ∀ x : ℝ, 1 ≤ x → (φ x ≠ 0 ∨ φ x⁻¹ ≠ 0) → x ≤ M)
    (i : Nat.Primes × ℕ) (hi : primePowerTraceTerm φ i ≠ 0) :
    (i.1 : ℕ) ≤ ⌊M⌋₊ ∧ i.2 ≤ ⌊M⌋₊ := by
  obtain ⟨p, k⟩ := i
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
  set x : ℝ := ((p : ℕ) : ℝ) ^ (k + 1) with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hp1.le
  have hne : φ x ≠ 0 ∨ φ x⁻¹ ≠ 0 := by
    by_contra h
    push Not at h
    apply hi
    simp only [primePowerTraceTerm]
    rw [← hx, h.1, h.2]; simp
  have hxM := hM x hx1 hne
  have hpx : ((p : ℕ) : ℝ) ≤ x := by
    rw [hx]; exact le_self_pow₀ hp1.le (by omega)
  have hkx : ((k : ℕ) : ℝ) ≤ x := by
    have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    calc ((k : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
          exact_mod_cast (Nat.lt_two_pow_self).le
      _ ≤ ((p : ℕ) : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
      _ ≤ x := by rw [hx]; exact pow_le_pow_right₀ hp1.le (by omega)
  have hM0 : 0 ≤ M := by linarith
  exact ⟨Nat.le_floor (hpx.trans hxM), Nat.le_floor (hkx.trans hxM)⟩

lemma support_finite (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ N : ℕ, (Function.support (primePowerTraceTerm φ)).Finite ∧
      ∀ i : Nat.Primes × ℕ, primePowerTraceTerm φ i ≠ 0 → (i.1 : ℕ) ≤ N ∧ i.2 ≤ N := by
  obtain ⟨M, -, hM⟩ := support_bounds φ hφ
  refine ⟨⌊M⌋₊, ?_, term_ne_zero_bound φ M hM⟩
  have hfin : ((fun i : Nat.Primes × ℕ => ((i.1 : ℕ), i.2)) ⁻¹'
      (Iic ⌊M⌋₊ ×ˢ Iic ⌊M⌋₊)).Finite := by
    apply Set.Finite.preimage
    · intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (Subtype.ext hab.1) hab.2
    · exact (Set.finite_Iic _).prod (Set.finite_Iic _)
  refine hfin.subset ?_
  intro i hi
  have := term_ne_zero_bound φ M hM i hi
  simpa using this

end GeomSideAux

open MasulloRH GeomSideAux

local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p])
    [hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p]]
    (μ : ∀ p : Nat.Primes, Measure ℚ_[p]) [hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure] :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (∀ p : Nat.Primes,
      IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} (μ p)) ∧
    (Function.support (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p))).Finite ∧
    Summable (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p)) ∧
    Summable (primePowerTraceTerm φ) ∧
    (1/2 : ℂ) * (∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ)) +
      ∑' p : Nat.Primes,
        ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
          ∫ g in {g : ℚ_[p] | g ≠ 0},
            φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p) =
      (∫ t in Ioi (1:ℝ), realTraceIntegrand φ t) +
        ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i := by
  obtain ⟨hRint, hReq⟩ := real_solution φ hφ
  have hP := fun p : Nat.Primes => prime_solution (p : ℕ) (μ p) φ hφ
  obtain ⟨N, hfinT, hN⟩ := support_finite φ hφ
  have hsT : Summable (primePowerTraceTerm φ) := summable_of_finite_support hfinT
  have hfib : ∀ p : Nat.Primes, Summable (fun k : ℕ => primePowerTraceTerm φ (p, k)) :=
    fun p => hsT.comp_injective (Prod.mk_right_injective p)
  set P : Nat.Primes → ℂ := fun p =>
    ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
      ∫ g in {g : ℚ_[p] | g ≠ 0},
        φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p) with hPdef
  have hPeq : ∀ p : Nat.Primes, P p = ∑' k : ℕ, primePowerTraceTerm φ (p, k) :=
    fun p => (hP p).2.2
  have hPfin : (Function.support P).Finite := by
    refine ((Set.finite_Iic N).preimage
      (fun a _ b _ hab => Subtype.ext hab : InjOn (fun p : Nat.Primes => (p : ℕ)) _)).subset ?_
    intro p hp
    rw [Function.mem_support, hPeq] at hp
    obtain ⟨k, hk⟩ : ∃ k, primePowerTraceTerm φ (p, k) ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (by simp [h])
    exact (hN _ hk).1
  refine ⟨hRint, fun p => (hP p).1, hPfin, summable_of_finite_support hPfin, hsT, ?_⟩
  rw [hReq, hsT.tsum_prod' hfib]
  congr 1
  exact tsum_congr hPeq

