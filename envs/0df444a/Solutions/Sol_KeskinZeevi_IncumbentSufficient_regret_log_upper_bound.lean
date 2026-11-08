-- Prove2me | solution 1 for KeskinZeevi.IncumbentSufficient.regret_log_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:36:40.164317+00:00
-- url     : https://prove2.me/submissions/5f6f32e1-41a1-4668-bc1a-fd852bf70580

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares
import Definitions.Def_KeskinZeevi_IncumbentSufficient_Regret
import Theorems.Thm_KeskinZeevi_IncumbentSufficient_estimation_error_exponential_decay
import Theorems.Thm_KeskinZeevi_IncumbentSufficient_sq_estimation_error_bound_A19
import Theorems.Thm_KeskinZeevi_IncumbentSufficient_sq_pricing_error_split
open RobustBooking.Shared
open MeasureTheory ProbabilityTheory

namespace Aux_KZI_main
open KeskinZeevi.IncumbentSufficient

lemma priceAux_meas {M : Model} {Ω : Type*} [MeasurableSpace Ω] (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) (n : ℕ) :
    Measurable (fun ω => priceAux π β ε ω n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h : (fun ω => priceAux π β ε ω n) = fun ω => π.rule n (fun i : Fin n =>
        (M.DHat + β * (priceAux π β ε ω i - M.pHat) + ε ((i : ℕ) + 1) ω, priceAux π β ε ω i)) := by
      funext ω
      rw [priceAux]
    rw [h]
    refine (π.measurable_rule n).comp (measurable_pi_lambda _ (fun i => ?_))
    have hi := ih i i.isLt
    exact ((measurable_const.add (measurable_const.mul (hi.sub_const _))).add (hε _)).prodMk hi

lemma price_mem {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : price π β ε t ω ∈ Set.Icc M.l M.u := by
  unfold price
  rw [priceAux]
  exact π.rule_mem _ _

lemma dev_meas {M : Model} {Ω : Type*} [MeasurableSpace Ω] (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) (s : ℕ) :
    Measurable (fun ω => dev π β ε s ω) :=
  (priceAux_meas π β ε hε (s - 1)).sub_const _

lemma psiTrunc_meas {M : Model} {Ω : Type*} [MeasurableSpace Ω] (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) (t : ℕ) :
    Measurable (fun ω => M.psi (truncEst π β ε t ω)) := by
  have hdev := dev_meas π β ε hε
  have hdem : ∀ s, Measurable (fun ω => demand π β ε s ω) := fun s =>
    (measurable_const.add (measurable_const.mul (hdev s))).add (hε s)
  have hJ : Measurable (fun ω => Jhat π β ε t ω) :=
    Finset.measurable_sum _ (fun s _ => (hdev s).pow_const 2)
  have hbh : Measurable (fun ω => betaHat π β ε t ω) :=
    (Finset.measurable_sum _ (fun s _ => ((hdem s).sub_const _).mul (hdev s))).div hJ
  have htr : Measurable (fun ω => truncEst π β ε t ω) :=
    measurable_const.max (hbh.min measurable_const)
  exact measurable_const.sub (measurable_const.div (measurable_const.mul htr))

lemma sq_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable (fun ω => f ω ^ 2) P := by
  refine Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h ω) 2

lemma sq_le_of_abs_le {a c : ℝ} (h : |a| ≤ c) : a ^ 2 ≤ c ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma truncEst_mem {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : truncEst π β ε t ω ∈ M.B := by
  unfold truncEst Model.truncate Model.B
  exact ⟨le_max_left _ _, max_le (le_of_lt M.bMin_lt_bMax) (min_le_right _ _)⟩

lemma psi_dev_abs {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (b : ℝ) (hb : b ∈ M.B) (t : ℕ) (ω : Ω) :
    |M.psi b - dev π β ε t ω| ≤ M.u - M.l := by
  have h1 := M.interior b hb
  have h2 := price_mem π β ε t ω
  unfold dev Model.psi
  simp only [Set.mem_Ioo, Set.mem_Icc] at h1 h2
  rw [abs_le]; constructor <;> linarith

lemma psi_psi_abs (M : Model) (b c : ℝ) (hb : b ∈ M.B) (hc : c ∈ M.B) :
    |M.psi b - M.psi c| ≤ M.u - M.l := by
  have h1 := M.interior b hb
  have h2 := M.interior c hc
  unfold Model.psi
  simp only [Set.mem_Ioo] at h1 h2
  rw [abs_le]; constructor <;> linarith

lemma trunc_close (M : Model) (β y : ℝ) (hβ : β ∈ M.B) :
    |M.truncate y - β| ≤ |y - β| := by
  unfold Model.truncate
  obtain ⟨h1, h2⟩ := hβ
  rw [abs_le]
  rcases le_total y M.bMax with h | h
  · rw [min_eq_left h]
    rcases le_total M.bMin y with h' | h'
    · rw [max_eq_right h']; exact abs_le.mp le_rfl
    · rw [max_eq_left h']
      constructor <;> cases abs_cases (y - β) <;> linarith
  · rw [min_eq_right h, max_eq_right (le_of_lt M.bMin_lt_bMax)]
    constructor <;> cases abs_cases (y - β) <;> linarith

/-- the key Lipschitz step: if `|y - β| ≤ δ` then `b = truncate y` satisfies the `A_t` bound. -/
lemma psi_close (M : Model) (β y : ℝ) (hβ : β ∈ M.B)
    (hy : |y - β| ≤ |M.psi β| * M.bMax ^ 2 / (2 * (|M.DHat| + 1))) :
    (M.psi β - M.psi (M.truncate y)) ^ 2 ≤ M.psi β ^ 2 / 12 := by
  set b := M.truncate y with hbdef
  have hbB : b ∈ M.B := by
    unfold b Model.truncate Model.B
    exact ⟨le_max_left _ _, max_le (le_of_lt M.bMin_lt_bMax) (min_le_right _ _)⟩
  have hbm := M.bMax_neg
  have hb0 : b < 0 := lt_of_le_of_lt hbB.2 hbm
  have hβ0 : β < 0 := lt_of_le_of_lt hβ.2 hbm
  set δ := |M.psi β| * M.bMax ^ 2 / (2 * (|M.DHat| + 1)) with hδ
  have hD1 : 0 < |M.DHat| + 1 := by positivity
  have hδeq : 2 * (|M.DHat| + 1) * δ = |M.psi β| * M.bMax ^ 2 := by
    rw [hδ]; field_simp
  have hclose : |β - b| ≤ δ := by
    rw [abs_sub_comm]; exact (trunc_close M β y hβ).trans hy
  have hsq : (β - b) ^ 2 ≤ δ ^ 2 := sq_le_of_abs_le hclose
  have hbne : b ≠ 0 := ne_of_lt hb0
  have hβne : β ≠ 0 := ne_of_lt hβ0
  have hid : (M.psi β - M.psi b) * (2 * b * β) = M.DHat * (β - b) := by
    unfold Model.psi psiOf
    field_simp
    ring
  have hb2 : M.bMax ^ 2 ≤ b ^ 2 := by nlinarith [hbB.2]
  have hβ2 : M.bMax ^ 2 ≤ β ^ 2 := by nlinarith [hβ.2]
  have hbb : M.bMax ^ 2 * M.bMax ^ 2 ≤ b ^ 2 * β ^ 2 :=
    mul_le_mul hb2 hβ2 (sq_nonneg _) (sq_nonneg _)
  set e := M.psi β - M.psi b
  have he : e ^ 2 * (4 * (b ^ 2 * β ^ 2)) = M.DHat ^ 2 * (β - b) ^ 2 := by
    have := congrArg (fun z => z ^ 2) hid
    simp only [mul_pow] at this ⊢
    nlinarith [this]
  have hDsq : M.DHat ^ 2 ≤ (|M.DHat| + 1) ^ 2 := by
    rw [← sq_abs M.DHat]; nlinarith [abs_nonneg M.DHat]
  have h1 : M.DHat ^ 2 * (β - b) ^ 2 ≤ (|M.DHat| + 1) ^ 2 * δ ^ 2 :=
    mul_le_mul hDsq hsq (sq_nonneg _) (sq_nonneg _)
  have h2 : (|M.DHat| + 1) ^ 2 * δ ^ 2 = (M.psi β) ^ 2 * (M.bMax ^ 2) ^ 2 / 4 := by
    have : ((|M.DHat| + 1) * δ) ^ 2 = (|M.psi β| * M.bMax ^ 2 / 2) ^ 2 := by
      congr 1; linarith
    rw [← mul_pow, this, div_pow, mul_pow, sq_abs]; ring
  have hbm2 : 0 < M.bMax ^ 2 := by nlinarith
  have hbm4 : 0 < (M.bMax ^ 2) ^ 2 := pow_pos hbm2 2
  have h3 : e ^ 2 * (4 * (M.bMax ^ 2) ^ 2) ≤ e ^ 2 * (4 * (b ^ 2 * β ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [hbb]
  have h4 : e ^ 2 * (4 * (M.bMax ^ 2) ^ 2) ≤ (M.psi β) ^ 2 * (M.bMax ^ 2) ^ 2 / 4 := by
    linarith
  have h5 : e ^ 2 ≤ (M.psi β) ^ 2 / 16 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_lt_mul_of_pos_right hc hbm4]
  have : (M.psi β) ^ 2 / 16 ≤ (M.psi β) ^ 2 / 12 := by
    have := sq_nonneg (M.psi β); linarith
  linarith

lemma sum_icc_range (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, f t = ∑ k ∈ Finset.range T, f (k + 1) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_inv_le (T : ℕ) :
    ∑ k ∈ Finset.range T, (1 : ℝ) / k ≤ 2 * (1 + Real.log T) := by
  have hh := harmonic_le_one_add_log T
  have hcast : ((harmonic T : ℚ) : ℝ) = ∑ k ∈ Finset.range T, (1 : ℝ) / ((k : ℝ) + 1) := by
    simp [harmonic]
  rw [hcast] at hh
  have : ∑ k ∈ Finset.range T, (1 : ℝ) / k ≤ ∑ k ∈ Finset.range T, 2 * ((1 : ℝ) / ((k : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro k _
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have hk : (1 : ℝ) ≤ k := by exact_mod_cast h
      rw [div_le_iff₀ (by linarith), mul_comm, ← mul_assoc]
      rw [show (k : ℝ) * 2 * (1 / ((k : ℝ) + 1)) = 2 * k / (k + 1) by ring]
      rw [le_div_iff₀ (by linarith)]; linarith
  rw [← Finset.mul_sum] at this
  linarith

lemma final_arith (a K κ L : ℝ) (ha : 0 ≤ a) (hK : 0 ≤ K) (hL : 1 ≤ L) :
    a + K * (2 * (1 + L)) + 2 * (κ * L) ≤ (a + 4 * K + 2 * κ) * L := by
  nlinarith

end Aux_KZI_main

open KeskinZeevi.IncumbentSufficient Aux_KZI_main in
theorem solution (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (β : ℝ) (hβ : β ∈ M.B) (hψ : M.psi β ≠ 0) :
    ∃ κ₀' : ℝ, 0 < κ₀' ∧ ∀ κ₀ : ℝ, κ₀' ≤ κ₀ → ∀ κ₁ : ℝ, 0 < κ₁ → ∀ t₀ : ℕ, 1 ≤ t₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ π : Policy M,
        (∀ᵐ ω ∂P, ∀ t : ℕ, t₀ ≤ t →
          κ₀ * Real.log t ≤ Jhat π β ε t ω ∧
            ∑ s ∈ Finset.Icc 1 t, (M.psi (truncEst π β ε s ω) - dev π β ε (s + 1) ω) ^ 2 ≤
              κ₁ * Real.log t) →
        ∀ T : ℕ, 3 ≤ T → regret π β ε P T ≤ C * Real.log T := by
  obtain ⟨ρ, hρ, h5⟩ := estimation_error_exponential_decay M P ε σ hε
  have hbm := M.bMax_neg
  have hβ0 : β < 0 := lt_of_le_of_lt hβ.2 hbm
  have hul : 0 < M.u - M.l := by linarith [M.l_lt_u]
  set δ := |M.psi β| * M.bMax ^ 2 / (2 * (|M.DHat| + 1)) with hδ
  have hδpos : 0 < δ := by
    have : 0 < |M.psi β| := abs_pos.mpr hψ
    have hb2 : 0 < M.bMax ^ 2 := by nlinarith
    exact div_pos (mul_pos this hb2) (by positivity)
  set c := min δ (δ ^ 2) with hc
  have hcpos : 0 < c := lt_min hδpos (by positivity)
  refine ⟨2 / (ρ * c), by positivity, ?_⟩
  intro κ₀ hκ₀ κ₁ hκ₁ t₀ ht₀
  obtain ⟨N, hN⟩ := sq_estimation_error_bound_A19 M P ε σ hε β hβ hψ κ₁ hκ₁ t₀ ht₀
  set K₁ := 512 * (M.DHat ^ 2 / (4 * M.bMax ^ 4)) * σ ^ 2 * (M.u - M.l) ^ 2 / M.psi β ^ 4
    with hK₁
  set K₂ := 4 * (M.u - M.l) ^ 2 with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  set K := 2 * (K₁ + 32 * K₂) with hK
  have hK0 : 0 ≤ K := by positivity
  set N₀ := N + 2 * t₀ + 5 with hN₀
  set C := (-M.bMin) * (N₀ * (M.u - M.l) ^ 2 + 4 * K + 2 * κ₁) + 1 with hC
  have hbmin : M.bMin < 0 := lt_trans M.bMin_lt_bMax hbm
  have hκ₀pos : 0 < κ₀ := lt_of_lt_of_le (by positivity) hκ₀
  have hρcκ : 2 ≤ ρ * c * κ₀ := by
    have : ρ * c * (2 / (ρ * c)) = 2 := by field_simp
    have h' := mul_le_mul_of_nonneg_left hκ₀ (le_of_lt (mul_pos hρ hcpos))
    linarith
  refine ⟨C, by
    have : 0 ≤ (-M.bMin) * (N₀ * (M.u - M.l) ^ 2 + 4 * K + 2 * κ₁) := by
      apply mul_nonneg (by linarith); positivity
    linarith, ?_⟩
  intro π hπ T hT
  have hεm := hε.measurable
  -- notation
  set f : ℕ → ℝ := fun t => ∫ ω, (M.psi β - dev π β ε t ω) ^ 2 ∂P with hf
  have hf_int : ∀ t, Integrable (fun ω => (M.psi β - dev π β ε t ω) ^ 2) P := fun t =>
    sq_int P _ (measurable_const.sub (dev_meas π β ε hεm t)) (M.u - M.l)
      (fun ω => psi_dev_abs π β ε β hβ t ω)
  have hd_int : ∀ k, Integrable
      (fun ω => (M.psi (truncEst π β ε k ω) - dev π β ε (k + 1) ω) ^ 2) P := fun k =>
    sq_int P _ ((psiTrunc_meas π β ε hεm k).sub (dev_meas π β ε hεm (k + 1))) (M.u - M.l)
      (fun ω => psi_dev_abs π β ε _ (truncEst_mem π β ε k ω) (k + 1) ω)
  -- Step 1: regret as a sum of squared pricing errors
  have hr : ∀ x, M.revenue β x = M.optRevenue β + β * (M.psi β - x) ^ 2 := by
    intro x
    have hβne : β ≠ 0 := ne_of_lt hβ0
    unfold Model.optRevenue Model.revenue Model.psi psiOf
    field_simp
    ring
  have hreg : regret π β ε P T = -β * ∑ t ∈ Finset.Icc 1 T, f t := by
    unfold regret
    simp_rw [hr]
    rw [integral_finset_sum (Finset.Icc 1 T)
      (f := fun t ω => M.optRevenue β + β * (M.psi β - dev π β ε t ω) ^ 2)
      (fun t _ => (integrable_const _).add ((hf_int t).const_mul β))]
    have : ∀ t ∈ Finset.Icc 1 T, ∫ ω, (M.optRevenue β + β * (M.psi β - dev π β ε t ω) ^ 2) ∂P
        = M.optRevenue β + β * f t := by
      intro t _
      rw [integral_add (integrable_const _) ((hf_int t).const_mul β), integral_const_mul]
      simp [hf]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      ← Finset.mul_sum]
    simp
  -- Step 2: bound on P(A_kᶜ)
  have hAc : ∀ k, N₀ ≤ k → (P (goodEvent π β ε k)ᶜ).toReal ≤ 32 / k := by
    intro k hk
    set a := (k - 1) / 2 with ha
    have hak : k ≤ 4 * a := by omega
    have hat₀ : t₀ ≤ a := by omega
    have ha2 : 2 ≤ a := by omega
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha2
    have hsub : (goodEvent π β ε k)ᶜ ⊆ ⋃ s ∈ Finset.Icc a (k - 1),
        {ω | M.psi β ^ 2 / 12 < (M.psi β - M.psi (truncEst π β ε s ω)) ^ 2} := by
      intro ω hω
      simp only [goodEvent, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hω
      obtain ⟨s, hs, hlt⟩ := hω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨s, hs, hlt⟩
    have hEs : ∀ s ∈ Finset.Icc a (k - 1),
        P {ω | M.psi β ^ 2 / 12 < (M.psi β - M.psi (truncEst π β ε s ω)) ^ 2} ≤
          ENNReal.ofReal (2 / (a : ℝ) ^ 2) := by
      intro s hs
      simp only [Finset.mem_Icc] at hs
      have hs2 : 2 ≤ s := by omega
      have hst₀ : t₀ ≤ s := by omega
      have hsR : (a : ℝ) ≤ s := by exact_mod_cast hs.1
      have hlogs : 0 < Real.log s := Real.log_pos (by exact_mod_cast (show 1 < s by omega))
      refine le_trans (measure_mono_ae ?_) (le_trans (h5 π β hβ δ (κ₀ * Real.log s) hδpos
        (by positivity) s hs2) ?_)
      · filter_upwards [hπ] with ω hω hE
        change M.psi β ^ 2 / 12 < _ at hE
        show δ < |betaHat π β ε s ω - β| ∧ κ₀ * Real.log s ≤ Jhat π β ε s ω
        refine ⟨?_, (hω s hst₀).1⟩
        by_contra hcon
        push_neg at hcon
        have := psi_close M β (betaHat π β ε s ω) hβ hcon
        unfold truncEst at hE
        linarith
      · apply ENNReal.ofReal_le_ofReal
        have hexp : Real.exp (-(ρ * c * (κ₀ * Real.log s))) ≤ Real.exp (-(2 * Real.log s)) := by
          apply Real.exp_le_exp.mpr
          have : 2 * Real.log s ≤ ρ * c * κ₀ * Real.log s :=
            mul_le_mul_of_nonneg_right hρcκ (le_of_lt hlogs)
          linarith
        have he2 : Real.exp (-(2 * Real.log s)) = 1 / (s : ℝ) ^ 2 := by
          rw [Real.exp_neg, show 2 * Real.log s = Real.log ((s : ℝ) ^ 2) by
            rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
          simp
        have hsa : 1 / (s : ℝ) ^ 2 ≤ 1 / (a : ℝ) ^ 2 := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_left₀ (by positivity) hsR 2
        rw [he2] at hexp
        have : 2 * (1 / (a : ℝ) ^ 2) = 2 / (a : ℝ) ^ 2 := by ring
        linarith
    have hP : P (goodEvent π β ε k)ᶜ ≤ ENNReal.ofReal (32 / k) := by
      refine le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le _ _)
        (le_trans (Finset.sum_le_sum hEs) ?_))
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      have hcard : ((k - 1 + 1 - a : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega)
      have hka : (k : ℝ) ≤ 4 * a := by exact_mod_cast hak
      calc ((k - 1 + 1 - a : ℕ) : ℝ) * (2 / (a : ℝ) ^ 2) ≤ k * (2 / (a : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ 32 / k := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            rw [show (k : ℝ) * (2 * ((a : ℝ) ^ 2)⁻¹) = 2 * k / (a : ℝ) ^ 2 by ring]
            rw [show 32 * (k : ℝ)⁻¹ = 32 / k by ring]
            rw [div_le_div_iff₀ (by positivity) hkpos]
            nlinarith
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hP
  -- Step 3: pointwise bound on f (k+1)
  set H : ℕ → ℝ := fun k => ∫ ω, (if N₀ ≤ k then
    (M.psi (truncEst π β ε k ω) - dev π β ε (k + 1) ω) ^ 2 else 0) ∂P with hH
  have hHint : ∀ k, Integrable (fun ω => if N₀ ≤ k then
      (M.psi (truncEst π β ε k ω) - dev π β ε (k + 1) ω) ^ 2 else 0) P := by
    intro k; split_ifs
    · exact hd_int k
    · exact integrable_zero _ _ _
  have hH0 : ∀ k, 0 ≤ H k := fun k => integral_nonneg (fun ω => by split_ifs <;> positivity)
  have hfbd : ∀ k, f (k + 1) ≤ (if k < N₀ then (M.u - M.l) ^ 2 else 0) + K * (1 / (k : ℝ))
      + 2 * H k := by
    intro k
    by_cases hk : k < N₀
    · rw [if_pos hk]
      have h1 : f (k + 1) ≤ (M.u - M.l) ^ 2 := by
        have := integral_mono (hf_int (k + 1)) (integrable_const ((M.u - M.l) ^ 2))
          (fun ω => sq_le_of_abs_le (psi_dev_abs π β ε β hβ (k + 1) ω))
        simpa [hf] using this
      have h2 : 0 ≤ K * (1 / (k : ℝ)) := by positivity
      linarith [hH0 k]
    · rw [if_neg hk, zero_add]
      push_neg at hk
      have hk1 : 1 ≤ k := by omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hsplit := sq_pricing_error_split M P ε σ hε π β hβ k hk1
      have hA19 := hN π (by filter_upwards [hπ] with ω hω t ht using (hω t ht).2) k (by omega)
      have hAc' := hAc k hk
      have hHk : H k = ∫ ω, (M.psi (truncEst π β ε k ω) - dev π β ε (k + 1) ω) ^ 2 ∂P := by
        simp [hH, if_pos hk]
      rw [hHk]
      have : (M.DHat ^ 2 / (4 * M.bMax ^ 4)) = M.DHat ^ 2 / (4 * M.bMax ^ 4) := rfl
      have hK1k : 512 * (M.DHat ^ 2 / (4 * M.bMax ^ 4)) * σ ^ 2 * (M.u - M.l) ^ 2 /
          M.psi β ^ 4 / k = K₁ * (1 / (k : ℝ)) := by rw [hK₁]; ring
      rw [hK1k] at hA19
      have hK2k : 4 * (M.u - M.l) ^ 2 * (P (goodEvent π β ε k)ᶜ).toReal ≤ K₂ * (32 * (1 / (k : ℝ))) := by
        rw [hK₂]; apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show 32 * (1 / (k : ℝ)) = 32 / k by ring]; exact hAc'
      have : f (k + 1) = ∫ ω, (M.psi β - dev π β ε (k + 1) ω) ^ 2 ∂P := rfl
      rw [this, hK]
      linarith
  -- Step 4: summation
  have hT1 : (1 : ℝ) ≤ Real.log T := by
    have h3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
    have : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith [Real.log_le_log (by norm_num) h3]
  have hsumA : ∑ k ∈ Finset.range T, (if k < N₀ then (M.u - M.l) ^ 2 else 0) ≤
      N₀ * (M.u - M.l) ^ 2 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : (Finset.filter (fun k => k < N₀) (Finset.range T)).card ≤ N₀ := by
      calc (Finset.filter (fun k => k < N₀) (Finset.range T)).card ≤ (Finset.range N₀).card :=
            Finset.card_le_card (fun k hk => by simp at hk ⊢; omega)
        _ = N₀ := Finset.card_range _
    exact_mod_cast this
  have hsumH : ∑ k ∈ Finset.range T, H k ≤ κ₁ * Real.log T := by
    rw [hH, ← integral_finset_sum _ (fun k _ => hHint k)]
    have hle : (∀ᵐ ω ∂P, ∑ k ∈ Finset.range T, (if N₀ ≤ k then
        (M.psi (truncEst π β ε k ω) - dev π β ε (k + 1) ω) ^ 2 else 0) ≤ κ₁ * Real.log T) := by
      filter_upwards [hπ] with ω hω
      by_cases hT0 : t₀ ≤ T
      · rw [← Finset.sum_filter]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _))
          (hω T hT0).2
        intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk
        simp only [Finset.mem_Icc]; omega
      · rw [Finset.sum_eq_zero (fun k hk => by
          simp only [Finset.mem_range] at hk; rw [if_neg (by omega)])]
        positivity
    have := integral_mono_ae (integrable_finset_sum _ (fun k _ => hHint k))
      (integrable_const (κ₁ * Real.log T)) hle
    simpa using this
  have hsumI := sum_inv_le T
  have hSf : ∑ t ∈ Finset.Icc 1 T, f t ≤
      N₀ * (M.u - M.l) ^ 2 + K * (2 * (1 + Real.log T)) + 2 * (κ₁ * Real.log T) := by
    rw [sum_icc_range]
    refine le_trans (Finset.sum_le_sum (fun k _ => hfbd k)) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hsumI hK0
    linarith
  have hSf0 : 0 ≤ ∑ t ∈ Finset.Icc 1 T, f t :=
    Finset.sum_nonneg (fun t _ => integral_nonneg (fun ω => sq_nonneg _))
  rw [hreg]
  have hB : N₀ * (M.u - M.l) ^ 2 + K * (2 * (1 + Real.log T)) + 2 * (κ₁ * Real.log T) ≤
      (N₀ * (M.u - M.l) ^ 2 + 4 * K + 2 * κ₁) * Real.log T := by
    exact final_arith _ _ _ _ (by positivity) hK0 hT1
  have hβb : -β ≤ -M.bMin := by linarith [hβ.1]
  calc -β * ∑ t ∈ Finset.Icc 1 T, f t ≤ -M.bMin * ∑ t ∈ Finset.Icc 1 T, f t :=
        mul_le_mul_of_nonneg_right hβb hSf0
    _ ≤ -M.bMin * ((N₀ * (M.u - M.l) ^ 2 + 4 * K + 2 * κ₁) * Real.log T) :=
        mul_le_mul_of_nonneg_left (hSf.trans hB) (by linarith)
    _ ≤ C * Real.log T := by
        rw [hC, show ∀ b X L : ℝ, (b * X + 1) * L = b * (X * L) + L from
          fun _ _ _ => by ring]
        linarith
