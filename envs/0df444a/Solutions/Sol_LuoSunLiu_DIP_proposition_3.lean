-- Prove2me | solution 1 for LuoSunLiu.DIP.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:05:30.063387+00:00
-- url     : https://prove2.me/submissions/a132ce12-d588-4854-a319-dc41a1c66995
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Theorems.Thm_LuoSunLiu_DIP_proposition_4
import Theorems.Thm_LuoSunLiu_DIP_lemma_S6

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace LuoSunLiu.DIP.P3Aux
open LuoSunLiu.DIP

theorem grid_near (g0 h pmax p : ℝ) (d : ℕ) (hd : 1 ≤ d) (hh : 0 < h) (hhp : h < pmax)
    (hg0 : g0 ≤ h / 2) (hgl : pmax - h / 2 ≤ g0 + ((d : ℝ) - 1) * h) (hp0 : 0 < p)
    (hp1 : p < pmax) :
    ∃ j : ℕ, j < d ∧ 0 < g0 + j * h ∧ g0 + j * h < pmax ∧ |p - (g0 + j * h)| ≤ h := by
  set r := (p - g0) / h with hr
  have hrh : r * h = p - g0 := by rw [hr]; field_simp
  set j1 := ⌈r⌉₊ with hj1
  have hle : r ≤ j1 := Nat.le_ceil r
  by_cases hjd : d ≤ j1
  · refine ⟨d - 1, by omega, ?_⟩
    have hlt : ((d - 1 : ℕ) : ℝ) < r := Nat.lt_ceil.1 (by omega)
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
    rw [hcast] at hlt ⊢
    have h1 : g0 + ((d : ℝ) - 1) * h < p := by nlinarith
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_of_pos (by linarith)]; linarith
  push Not at hjd
  rcases le_or_gt 0 r with hr0 | hr0
  · have hlt : (j1 : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
    have hpg : p ≤ g0 + j1 * h := by nlinarith
    have hgp : g0 + j1 * h < p + h := by nlinarith
    by_cases hgm : g0 + j1 * h < pmax
    · exact ⟨j1, hjd, by linarith, hgm, by rw [abs_of_nonpos (by linarith)]; linarith⟩
    · push Not at hgm
      have hj1pos : 1 ≤ j1 := by
        by_contra hc
        have : j1 = 0 := by omega
        rw [this] at hgm; simp at hgm; linarith
      refine ⟨j1 - 1, by omega, ?_⟩
      have hcast : ((j1 - 1 : ℕ) : ℝ) = (j1 : ℝ) - 1 := by rw [Nat.cast_sub hj1pos]; simp
      rw [hcast]
      have hq : g0 + ((j1 : ℝ) - 1) * h < p := by nlinarith
      refine ⟨by nlinarith, by linarith, ?_⟩
      rw [abs_of_pos (by linarith)]; nlinarith
  · have hj0 : j1 = 0 := Nat.ceil_eq_zero.2 hr0.le
    refine ⟨0, by omega, ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hpg : p < g0 := by
      have : r * h < 0 := mul_neg_of_neg_of_pos hr0 hh
      linarith
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_of_neg (by linarith)]; linarith

theorem abs_dot_le {d0 : ℕ} (y θ : Fin d0 → ℝ) (hy : ∀ i, |y i| ≤ 1) : |y ⬝ᵥ θ| ≤ l1 θ := by
  unfold dotProduct l1
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |y i| * |θ i| ≤ 1 * |θ i| := mul_le_mul_of_nonneg_right (hy i) (abs_nonneg _)
    _ = |θ i| := one_mul _

theorem l1_nonneg {d0 : ℕ} (θ : Fin d0 → ℝ) : 0 ≤ l1 θ :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

theorem cont_part {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (CA : ℝ)
    (hA2 : Assumption2 M CA) (θh : Fin d0 → ℝ) (hθW : l1 θh ≤ M.W) (d : ℕ) (hd : 1 ≤ d)
    (hgrid : M.pmax + 2 * l1 θh < d * M.pmax) (y : Fin d0 → ℝ) (hy : y ∈ M.X) :
    revenue M.F (y ⬝ᵥ M.θ0) (M.pstar y) - bestGridRevenue M θh d y ≤
      max CA 0 * (M.pmax + 2 * M.W) ^ 2 / (d : ℝ) ^ 2 := by
  obtain ⟨-, hp, hX, hst⟩ := hM
  obtain ⟨⟨hs0, hs1⟩, -⟩ := hst y hy
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl0 := l1_nonneg θh
  set h := gridStep M.pmax θh d with hhdef
  have hdh : (d : ℝ) * h = M.pmax + 2 * l1 θh := by rw [hhdef, gridStep]; field_simp
  have hh : 0 < h := by rw [hhdef, gridStep]; positivity
  have hhp : h < M.pmax := by
    by_contra hc; push Not at hc
    have : (d : ℝ) * M.pmax ≤ d * h := mul_le_mul_of_nonneg_left hc hd'.le
    linarith
  have hdot := abs_dot_le y θh (hX y hy)
  rw [abs_le] at hdot
  set g0 := -l1 θh + h / 2 + y ⬝ᵥ θh with hg0
  have hgrid_eq : ∀ j : Fin d, gridPrice M.pmax θh d j y = g0 + (j : ℕ) * h := by
    intro j; simp only [gridPrice, gridMid, hg0, ← hhdef]; ring
  obtain ⟨j, hjd, hj0, hj1, hjabs⟩ := grid_near g0 h M.pmax (M.pstar y) d hd hh hhp
    (by rw [hg0]; linarith) (by rw [hg0]; nlinarith) hs0 hs1
  set jf : Fin d := ⟨j, hjd⟩
  have hjf : gridPrice M.pmax θh d jf y = g0 + j * h := hgrid_eq jf
  have hav : jf ∈ avail M.pmax θh d y := by
    simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hjf]; exact ⟨hj0, hj1⟩
  have hne : (avail M.pmax θh d y).Nonempty := ⟨jf, hav⟩
  have hbest : revenue M.F (y ⬝ᵥ M.θ0) (gridPrice M.pmax θh d jf y) ≤
      bestGridRevenue M θh d y := by
    unfold bestGridRevenue
    rw [dif_pos hne]
    exact Finset.le_sup' (fun j => revenue M.F (y ⬝ᵥ M.θ0) (gridPrice M.pmax θh d j y)) hav
  have hA := hA2 y hy (gridPrice M.pmax θh d jf y) (by rw [hjf]; exact ⟨hj0.le, hj1.le⟩)
  rw [hjf] at hA hbest
  have hsq : (M.pstar y - (g0 + j * h)) ^ 2 ≤ h ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hjabs 2
  have hh2 : h ^ 2 ≤ (M.pmax + 2 * M.W) ^ 2 / (d : ℝ) ^ 2 := by
    rw [← div_pow]
    apply pow_le_pow_left₀ hh.le
    rw [hhdef, gridStep]
    exact div_le_div_of_nonneg_right (by linarith) hd'.le
  have hCA : CA * (M.pstar y - (g0 + j * h)) ^ 2 ≤ max CA 0 * ((M.pmax + 2 * M.W) ^ 2 / (d : ℝ) ^ 2) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hsq.trans hh2) (le_max_right _ _))
  rw [mul_div_assoc]
  linarith


theorem F_bounds {d0 : ℕ} (M : PricingModel d0) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p) (c : ℝ) :
    0 ≤ M.F c ∧ M.F c ≤ 1 := by
  obtain ⟨-, -, -, -, hF, -⟩ := hEnv 1 le_rfl
  rw [← hF c]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem perRegret_bounds {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing)
    (hF : ∀ c, 0 ≤ M.F c ∧ M.F c ≤ 1) (y : Fin d0 → ℝ) (hy : y ∈ M.X) (q : ℝ)
    (hq : q ∈ Set.Ioo 0 M.pmax) : 0 ≤ perRegret M y q ∧ perRegret M y q ≤ M.pmax := by
  obtain ⟨-, -, -, hst⟩ := hM
  obtain ⟨⟨hs0, hs1⟩, hmax⟩ := hst y hy
  unfold perRegret
  refine ⟨by linarith [hmax q hq.1], ?_⟩
  unfold revenue
  have h1 := hF (M.pstar y - y ⬝ᵥ M.θ0)
  have h2 := hF (q - y ⬝ᵥ M.θ0)
  have : 0 ≤ q * (1 - M.F (q - y ⬝ᵥ M.θ0)) := mul_nonneg hq.1.le (by linarith)
  nlinarith

/-- The continuous-part constant of Proposition 3(a). -/
noncomputable def Ccont {d0 : ℕ} (M : PricingModel d0) (CA : ℝ) : ℝ :=
  max CA 0 * (M.pmax + 2 * M.W) ^ 2 + 1

theorem Ccont_pos {d0 : ℕ} (M : PricingModel d0) (CA : ℝ) : 0 < Ccont M CA := by
  unfold Ccont; have := le_max_right CA 0; positivity

theorem part_a {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (CA : ℝ) (hA2 : Assumption2 M CA)
    (θh : Fin d0 → ℝ) (hθW : l1 θh ≤ M.W) (d : ℕ) (hd : 1 ≤ d)
    (hgrid : M.pmax + 2 * l1 θh < d * M.pmax) (lam δ : ℝ) (hlam : 0 < lam)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p)
    (T0 : ℕ) (hT0 : 1 ≤ T0)
    (hrun : ∀ ω, ∃ j : ℕ → Fin d, IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
      (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
      ∀ ω ∈ E, cumRegret M x p T0 ω ≤
        2 * Real.sqrt (2 * d * T0 * betaStar M.pmax lam d δ T0 *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) +
        4 * M.pmax * L * l1 (θh - M.θ0) * T0 + Ccont M CA * T0 / (d : ℝ) ^ 2 +
        2 * d * M.pmax := by
  obtain ⟨E, hE, hPE, hbd⟩ := proposition_4 M hM L hL θh d hd hgrid lam δ hlam hδ P 𝒢 x z p
    hEnv T0 hT0 hrun
  refine ⟨E, hE, hPE, fun ω hω => ?_⟩
  have h4 := hbd ω hω
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set K := max CA 0 * (M.pmax + 2 * M.W) ^ 2 with hK
  have hsplit : cumRegret M x p T0 ω = discreteRegret M θh d x p T0 ω +
      ∑ t ∈ Finset.Icc 1 T0, (revenue M.F (x t ω ⬝ᵥ M.θ0) (M.pstar (x t ω)) -
        bestGridRevenue M θh d (x t ω)) := by
    unfold cumRegret discreteRegret perRegret
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => by ring
  have hcont : ∑ t ∈ Finset.Icc 1 T0, (revenue M.F (x t ω ⬝ᵥ M.θ0) (M.pstar (x t ω)) -
      bestGridRevenue M θh d (x t ω)) ≤ Ccont M CA * T0 / (d : ℝ) ^ 2 := by
    calc _ ≤ ∑ t ∈ Finset.Icc 1 T0, K / (d : ℝ) ^ 2 := Finset.sum_le_sum fun t ht => by
            rw [Finset.mem_Icc] at ht
            exact cont_part M hM CA hA2 θh hθW d hd hgrid _ ((hEnv t ht.1).2.2.2.1 ω)
      _ = T0 * (K / (d : ℝ) ^ 2) := by simp
      _ ≤ Ccont M CA * T0 / (d : ℝ) ^ 2 := by
          rw [mul_div_assoc', mul_comm (T0 : ℝ)]
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          unfold Ccont; rw [← hK]; linarith
  rw [hsplit]
  linarith


theorem log3_ge_one : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

/-- The real-number estimate of the proof of Proposition 3(b), p. 54. -/
theorem real_b (pmax C1' Lg Cc Cd : ℝ) (T0 d : ℕ) (hp : 0 < pmax) (hC1' : 0 < C1')
    (hLg : 1 ≤ Lg) (hCc : 0 < Cc) (hCd : 1 ≤ Cd) (hT0 : 1 ≤ T0)
    (hd_lo : Cd * (T0 : ℝ) ^ ((1 : ℝ) / 6) ≤ d) (hd_hi : (d : ℝ) ≤ 2 * Cd * (T0 : ℝ) ^ ((1 : ℝ) / 6))
    (X : ℝ) (hX : X ≤ 2 * Real.sqrt 2 * C1' * d * Real.sqrt T0 * Lg) :
    X + Cc * T0 / (d : ℝ) ^ 2 + 2 * d * pmax + pmax ≤
      (4 * Real.sqrt 2 * C1' * Cd + Cc / Cd ^ 2 + 4 * Cd * pmax + pmax + 1) * Lg *
        (T0 : ℝ) ^ ((2 : ℝ) / 3) := by
  have hT : (1 : ℝ) ≤ T0 := by exact_mod_cast hT0
  have hT0' : (0 : ℝ) ≤ T0 := by linarith
  set u := (T0 : ℝ) ^ ((1 : ℝ) / 6) with hu
  set S := (T0 : ℝ) ^ ((2 : ℝ) / 3) with hS
  have hu1 : 1 ≤ u := Real.one_le_rpow hT (by norm_num)
  have hS1 : 1 ≤ S := Real.one_le_rpow hT (by norm_num)
  have huS : u ≤ S := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have huT : u * Real.sqrt T0 = S := by
    rw [Real.sqrt_eq_rpow, hu, hS, ← Real.rpow_add (by linarith)]; norm_num
  have hu2 : u ^ 2 * S = T0 := by
    rw [hu, hS, ← Real.rpow_natCast, ← Real.rpow_mul hT0', ← Real.rpow_add (by linarith)]
    norm_num
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le (by positivity) hd_lo
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsT : 0 ≤ Real.sqrt T0 := Real.sqrt_nonneg _
  -- term 1
  have h1 : X ≤ 4 * Real.sqrt 2 * C1' * Cd * S * Lg := by
    refine hX.trans ?_
    have : (d : ℝ) * Real.sqrt T0 ≤ 2 * Cd * S := by
      rw [← huT]; nlinarith
    have hc : 0 ≤ 2 * Real.sqrt 2 * C1' * Lg := by positivity
    nlinarith
  -- term 2
  have h2 : Cc * T0 / (d : ℝ) ^ 2 ≤ Cc / Cd ^ 2 * S := by
    rw [div_le_iff₀ (by positivity)]
    have hdd : (Cd * u) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hd_lo 2
    have : Cc / Cd ^ 2 * S * (d : ℝ) ^ 2 ≥ Cc / Cd ^ 2 * S * (Cd * u) ^ 2 :=
      mul_le_mul_of_nonneg_left hdd (by positivity)
    have heq : Cc / Cd ^ 2 * S * (Cd * u) ^ 2 = Cc * T0 := by
      rw [← hu2]; field_simp
    linarith
  -- term 3
  have h3 : 2 * d * pmax + pmax ≤ (4 * Cd * pmax + pmax) * S := by
    have : (d : ℝ) ≤ 2 * Cd * S := hd_hi.trans (by nlinarith)
    nlinarith
  have hS0 : 0 ≤ S := by linarith
  have hfin : (Cc / Cd ^ 2 * S) + (4 * Cd * pmax + pmax) * S ≤
      (Cc / Cd ^ 2 + 4 * Cd * pmax + pmax + 1) * Lg * S := by
    have hk : 0 ≤ Cc / Cd ^ 2 + 4 * Cd * pmax + pmax := by positivity
    have := mul_nonneg (mul_nonneg (by linarith : 0 ≤ Cc / Cd ^ 2 + 4 * Cd * pmax + pmax + 1)
      (sub_nonneg.2 hLg)) hS0
    have e : (Cc / Cd ^ 2 + 4 * Cd * pmax + pmax + 1) * Lg * S -
        ((Cc / Cd ^ 2 * S) + (4 * Cd * pmax + pmax) * S) =
        (Cc / Cd ^ 2 + 4 * Cd * pmax + pmax + 1) * (Lg - 1) * S + S := by ring
    linarith
  have e2 : (4 * Real.sqrt 2 * C1' * Cd + Cc / Cd ^ 2 + 4 * Cd * pmax + pmax + 1) * Lg * S =
      4 * Real.sqrt 2 * C1' * Cd * S * Lg + (Cc / Cd ^ 2 + 4 * Cd * pmax + pmax + 1) * Lg * S := by
    ring
  rw [e2]
  linarith

end LuoSunLiu.DIP.P3Aux

set_option maxHeartbeats 1000000 in
open LuoSunLiu.DIP LuoSunLiu.DIP.P3Aux in
theorem solution {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (CA : ℝ) (hA2 : Assumption2 M CA) :
    (∃ Ccont : ℝ, 0 < Ccont ∧
      ∀ (θh : Fin d0 → ℝ), l1 θh ≤ M.W → ∀ (d : ℕ), 1 ≤ d → M.pmax + 2 * l1 θh < d * M.pmax →
      ∀ (lam δ : ℝ), 0 < lam → δ ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ), IsPricingEnv M P 𝒢 x z p →
      ∀ (T0 : ℕ), 1 ≤ T0 →
      (∀ ω, ∃ j : ℕ → Fin d, IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
        (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
        ∀ ω ∈ E, cumRegret M x p T0 ω ≤
          2 * Real.sqrt (2 * d * T0 * betaStar M.pmax lam d δ T0 *
            Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) +
          4 * M.pmax * L * l1 (θh - M.θ0) * T0 + Ccont * T0 / (d : ℝ) ^ 2 +
          2 * d * M.pmax) ∧
    (∀ (Cdisc : ℕ), M.pmax + 2 * M.W < Cdisc * M.pmax → ∀ (lam : ℝ), 0 < lam →
      ∃ C2' C3' : ℝ, 0 < C2' ∧ 0 < C3' ∧
      ∀ (θh : Fin d0 → ℝ), l1 θh ≤ M.W →
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ), IsPricingEnv M P 𝒢 x z p →
      ∀ (T0 : ℕ), 1 ≤ T0 →
      (∀ ω, ∃ j : ℕ → Fin (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊),
        IsInnerBRun M.pmax θh lam
          (betaStar M.pmax lam (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊) (1 / (T0 : ℝ))) 0 T0
          (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) →
      ∫⁻ ω, ENNReal.ofReal (cumRegret M x p T0 ω) ∂P ≤
        ENNReal.ofReal (C3' * Real.log (C2' * T0) * (T0 : ℝ) ^ ((2 : ℝ) / 3) +
          4 * M.pmax * L * l1 (θh - M.θ0) * T0)) := by
  have hp : 0 < M.pmax := hM.2.1
  have hW0 : 0 ≤ M.W := (l1_nonneg _).trans hM.1
  refine ⟨⟨Ccont M CA, Ccont_pos M CA, fun θh hθW d hd hgrid lam δ hlam hδ Ω mΩ _ P _ 𝒢 x z p hEnv
    T0 hT0 hrun => part_a M hM L hL CA hA2 θh hθW d hd hgrid lam δ hlam hδ Ω mΩ P 𝒢 x z p hEnv
      T0 hT0 hrun⟩, ?_⟩
  intro Cdisc hCdisc lam hlam
  obtain ⟨C1', C2'', hC1', hC2'', hS6⟩ :=
    lemma_S6 M.pmax lam (1 / M.pmax) hp hlam (by positivity)
  have hCd : (1 : ℝ) ≤ Cdisc := by
    by_contra hc; push Not at hc
    have : (Cdisc : ℝ) * M.pmax ≤ 1 * M.pmax := mul_le_mul_of_nonneg_right hc.le hp.le
    linarith
  have hCcpos := Ccont_pos M CA
  refine ⟨max C2'' 3, 4 * Real.sqrt 2 * C1' * Cdisc + Ccont M CA / (Cdisc : ℝ) ^ 2 +
    4 * Cdisc * M.pmax + M.pmax + 1, by positivity, by positivity, ?_⟩
  intro θh hθW Ω mΩ _ P _ 𝒢 x z p hEnv T0 hT0 hrun
  set C3 := 4 * Real.sqrt 2 * C1' * Cdisc + Ccont M CA / (Cdisc : ℝ) ^ 2 +
    4 * Cdisc * M.pmax + M.pmax + 1 with hC3
  have hT : (1 : ℝ) ≤ T0 := by exact_mod_cast hT0
  set Lg := Real.log (max C2'' 3 * T0) with hLgdef
  have hLg : 1 ≤ Lg := log3_ge_one.trans
    (Real.log_le_log (by norm_num) (by nlinarith [le_max_right C2'' 3]))
  set S := (T0 : ℝ) ^ ((2 : ℝ) / 3) with hSdef
  have hS1 : 1 ≤ S := Real.one_le_rpow hT (by norm_num)
  have hFb := F_bounds M P 𝒢 x z p hEnv
  have hprice : ∀ ω, ∀ t ∈ Finset.Icc 1 T0, p t ω ∈ Set.Ioo 0 M.pmax := by
    intro ω t ht
    obtain ⟨j, hj⟩ := hrun ω
    obtain ⟨hav, hpr, -, -⟩ := hj t ht
    simp only [zero_add] at hav hpr
    rw [hpr]
    simp only [avail, Finset.mem_filter] at hav
    exact ⟨hav.2.1, hav.2.2⟩
  have hR : ∀ ω, 0 ≤ cumRegret M x p T0 ω ∧ cumRegret M x p T0 ω ≤ M.pmax * T0 := by
    intro ω
    have hb : ∀ t ∈ Finset.Icc 1 T0, 0 ≤ perRegret M (x t ω) (p t ω) ∧
        perRegret M (x t ω) (p t ω) ≤ M.pmax := fun t ht =>
      perRegret_bounds M hM hFb _ ((hEnv t (Finset.mem_Icc.1 ht).1).2.2.2.1 ω) _ (hprice ω t ht)
    refine ⟨Finset.sum_nonneg fun t ht => (hb t ht).1, ?_⟩
    calc cumRegret M x p T0 ω ≤ ∑ t ∈ Finset.Icc 1 T0, M.pmax :=
          Finset.sum_le_sum fun t ht => (hb t ht).2
      _ = M.pmax * T0 := by simp [mul_comm]
  have hl0 : 0 ≤ 4 * M.pmax * L * l1 (θh - M.θ0) * T0 := by
    have := l1_nonneg (θh - M.θ0); positivity
  have hC3ge : M.pmax ≤ C3 * Lg * S := by
    have h1 : M.pmax ≤ C3 := by
      rw [hC3]
      have : 0 ≤ 4 * Real.sqrt 2 * C1' * Cdisc + Ccont M CA / (Cdisc : ℝ) ^ 2 +
        4 * Cdisc * M.pmax := by positivity
      linarith
    have h2 : 1 ≤ Lg * S := by nlinarith
    have h3 : 0 ≤ C3 := by linarith
    nlinarith
  rcases Nat.lt_or_ge T0 2 with hT2 | hT2
  · have h1 : T0 = 1 := by omega
    calc ∫⁻ ω, ENNReal.ofReal (cumRegret M x p T0 ω) ∂P ≤ ∫⁻ _ω, ENNReal.ofReal M.pmax ∂P := by
          refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
          have := (hR ω).2
          have h1' : (T0 : ℝ) = 1 := by exact_mod_cast h1
          rw [h1', mul_one] at this; exact this
      _ = ENNReal.ofReal M.pmax := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  -- T0 ≥ 2
  set u := (T0 : ℝ) ^ ((1 : ℝ) / 6) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hT (by norm_num)
  set d := Cdisc * ⌈u⌉₊ with hd
  have hceil1 : 1 ≤ ⌈u⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
  have hCdn : 1 ≤ Cdisc := by exact_mod_cast hCd
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hdcast : (d : ℝ) = Cdisc * (⌈u⌉₊ : ℝ) := by rw [hd]; push_cast; ring
  have hd_lo : (Cdisc : ℝ) * u ≤ d := by
    rw [hdcast]; exact mul_le_mul_of_nonneg_left (Nat.le_ceil u) (by linarith)
  have hd_hi : (d : ℝ) ≤ 2 * Cdisc * u := by
    rw [hdcast]
    have := Nat.ceil_lt_add_one (show 0 ≤ u by linarith)
    nlinarith
  have hdge : (Cdisc : ℝ) ≤ d := by
    rw [hdcast]
    have : (1 : ℝ) ≤ (⌈u⌉₊ : ℝ) := by exact_mod_cast hceil1
    nlinarith
  have hgrid : M.pmax + 2 * l1 θh < d * M.pmax := by
    have : (Cdisc : ℝ) * M.pmax ≤ d * M.pmax := mul_le_mul_of_nonneg_right hdge hp.le
    linarith
  have hT2' : (2 : ℝ) ≤ T0 := by exact_mod_cast hT2
  have hδ : 1 / (T0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
  obtain ⟨E, hE, hPE, hbd⟩ := part_a M hM L hL CA hA2 θh hθW d hd1 hgrid lam (1 / T0) hlam hδ
    Ω mΩ P 𝒢 x z p hEnv T0 hT0 hrun
  set X := 2 * Real.sqrt (2 * d * T0 * betaStar M.pmax lam d (1 / T0) T0 *
    Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) with hXdef
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  -- the S6 estimate
  have hX : X ≤ 2 * Real.sqrt 2 * C1' * d * Real.sqrt T0 * Lg := by
    have hS6' := hS6 d hd1 T0 hT0
    have hβ : betaStar M.pmax lam d (1 / T0) T0 *
        Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam)) =
        M.pmax ^ 2 * max 1 ((1 / M.pmax * Real.sqrt (lam * d) +
          Real.sqrt (2 * Real.log T0 +
            d * Real.log ((d * lam + ((T0 : ℝ) - 1) * M.pmax ^ 2) / (d * lam)))) ^ 2) *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam)) := by
      unfold betaStar; rw [one_div_one_div]
    have hsplit : Real.sqrt (2 * d * T0 * betaStar M.pmax lam d (1 / T0) T0 *
        Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) =
        Real.sqrt (2 * d * T0) * Real.sqrt (betaStar M.pmax lam d (1 / T0) T0 *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) := by
      rw [← Real.sqrt_mul (by positivity)]; ring_nf
    have hlog : Real.log (C2'' * T0) ≤ Lg :=
      Real.log_le_log (by positivity) (by nlinarith [le_max_left C2'' 3])
    have hsq : Real.sqrt (2 * d * T0) = Real.sqrt 2 * Real.sqrt d * Real.sqrt T0 := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    have hdd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hdpos.le
    rw [hXdef, hsplit, hβ]
    have hA : Real.sqrt (M.pmax ^ 2 * max 1 ((1 / M.pmax * Real.sqrt (lam * d) +
          Real.sqrt (2 * Real.log T0 +
            d * Real.log ((d * lam + ((T0 : ℝ) - 1) * M.pmax ^ 2) / (d * lam)))) ^ 2) *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) ≤ C1' * Real.sqrt d * Lg :=
      hS6'.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
    have hpos : 0 ≤ Real.sqrt (2 * d * T0) := Real.sqrt_nonneg _
    calc 2 * (Real.sqrt (2 * d * T0) * _) ≤ 2 * (Real.sqrt (2 * d * T0) * (C1' * Real.sqrt d * Lg)) :=
          by gcongr
      _ = 2 * Real.sqrt 2 * C1' * (Real.sqrt d * Real.sqrt d) * Real.sqrt T0 * Lg := by
          rw [hsq]; ring
      _ = _ := by rw [hdd]
  have hreal := real_b M.pmax C1' Lg (Ccont M CA) Cdisc T0 d hp hC1' hLg hCcpos hCd hT0
    hd_lo hd_hi X hX
  set Bd := X + 4 * M.pmax * L * l1 (θh - M.θ0) * T0 + Ccont M CA * T0 / (d : ℝ) ^ 2 +
    2 * d * M.pmax with hBd
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hBd0 : 0 ≤ Bd := by rw [hBd]; positivity
  have hPEc : P Eᶜ ≤ ENNReal.ofReal (1 / T0) := by
    rw [prob_compl_eq_one_sub hE]
    calc 1 - P E ≤ 1 - ENNReal.ofReal (1 - 1 / T0) := tsub_le_tsub_left hPE _
      _ = ENNReal.ofReal (1 / T0) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith [hδ.2])]
        congr 1; ring
  calc ∫⁻ ω, ENNReal.ofReal (cumRegret M x p T0 ω) ∂P
      = ∫⁻ ω in E, ENNReal.ofReal (cumRegret M x p T0 ω) ∂P +
          ∫⁻ ω in Eᶜ, ENNReal.ofReal (cumRegret M x p T0 ω) ∂P :=
        (lintegral_add_compl _ hE).symm
    _ ≤ ∫⁻ _ω in E, ENNReal.ofReal Bd ∂P + ∫⁻ _ω in Eᶜ, ENNReal.ofReal (M.pmax * T0) ∂P := by
        exact add_le_add (setLIntegral_mono measurable_const fun ω hω =>
            ENNReal.ofReal_le_ofReal (hbd ω hω))
          (setLIntegral_mono measurable_const fun ω _ => ENNReal.ofReal_le_ofReal (hR ω).2)
    _ = ENNReal.ofReal Bd * P E + ENNReal.ofReal (M.pmax * T0) * P Eᶜ := by
        rw [setLIntegral_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal Bd * 1 + ENNReal.ofReal (M.pmax * T0) * ENNReal.ofReal (1 / T0) := by
        gcongr
        exact prob_le_one
    _ = ENNReal.ofReal (Bd + M.pmax) := by
        have e : M.pmax * T0 * (1 / (T0 : ℝ)) = M.pmax := by field_simp
        rw [mul_one, ← ENNReal.ofReal_mul (by positivity), e, ← ENNReal.ofReal_add hBd0 hp.le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hBd]
        have e : C3 * Real.log (max C2'' 3 * T0) * S = C3 * Lg * S := rfl
        linarith
