-- Prove2me | solution 1 for MDPFinance.DividendProblems.corollary_9_2_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:00:52.757523+00:00
-- url     : https://prove2.me/submissions/1ef666f3-4fad-4178-a693-467cd27a45b7

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter MDPFinance.DividendProblems

namespace Div924

variable (M : DividendModel)

theorem q_nonneg (k : ℤ) : 0 ≤ M.q k := ENNReal.toReal_nonneg

theorem q_summable : Summable M.q :=
  ENNReal.summable_toReal (by rw [M.Zpmf.tsum_coe]; exact ENNReal.one_ne_top)

theorem q_sum : ∑' k, M.q k = 1 := by
  unfold DividendModel.q
  rw [← ENNReal.tsum_toReal_eq (fun k => M.Zpmf.apply_ne_top k), M.Zpmf.tsum_coe]
  rfl

theorem EZplus_nonneg : 0 ≤ M.EZplus :=
  tsum_nonneg fun k => mul_nonneg (q_nonneg M k) (le_max_right _ _)

theorem step_lint (x : ℤ) (a : ℕ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ y, f y ∂(M.toMDM.step (x, a)) = ∑' k, M.Zpmf k * f (DividendModel.Tnext x a k) := by
  show ∫⁻ y, f y ∂(M.Zpmf.map (DividendModel.Tnext x a)).toMeasure = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _), lintegral_countable']
  congr 1
  funext k
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

/-- `∑ q_k (c + A k⁺) = c + A 𝔼Z⁺`, as an `ℝ≥0∞` identity. -/
theorem tsum_bound (c A : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    ∑' k, M.Zpmf k * ENNReal.ofReal (c + A * max (k : ℝ) 0) =
      ENNReal.ofReal (c + A * M.EZplus) := by
  have hs1 : Summable fun k => c * M.q k := (q_summable M).mul_left c
  have hs2 : Summable fun k => A * (M.q k * max (k : ℝ) 0) := M.hEZplus.mul_left A
  have hsum : Summable fun k => M.q k * (c + A * max (k : ℝ) 0) := by
    refine (hs1.add hs2).congr fun k => ?_
    ring
  have hnn : ∀ k, 0 ≤ M.q k * (c + A * max (k : ℝ) 0) := fun k =>
    mul_nonneg (q_nonneg M k) (by positivity)
  have : ∀ k, M.Zpmf k * ENNReal.ofReal (c + A * max (k : ℝ) 0) =
      ENNReal.ofReal (M.q k * (c + A * max (k : ℝ) 0)) := by
    intro k
    rw [ENNReal.ofReal_mul (q_nonneg M k), DividendModel.q,
      ENNReal.ofReal_toReal (M.Zpmf.apply_ne_top k)]
  simp only [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  congr 1
  rw [show (fun k => M.q k * (c + A * max (k : ℝ) 0)) =
    fun k => c * M.q k + A * (M.q k * max (k : ℝ) 0) by funext k; ring]
  rw [hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, q_sum]
  unfold DividendModel.EZplus DividendModel.q
  ring

/-- The basic one-step estimate: from `x ≥ 0` paying `a ≤ x`, a function bounded by
`A y⁺ + B` integrates to at most `A (x - a) + B + A 𝔼Z⁺`. -/
theorem step_bound (x : ℤ) (hx : 0 ≤ x) (a : ℕ) (ha : (a : ℤ) ≤ x) (f : ℤ → ℝ≥0∞) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : ∀ y, f y ≤ ENNReal.ofReal (A * max (y : ℝ) 0 + B)) :
    ∫⁻ y, f y ∂(M.toMDM.step (x, a)) ≤
      ENNReal.ofReal (A * ((x : ℝ) - a) + B + A * M.EZplus) := by
  rw [step_lint]
  have hxa : (0 : ℝ) ≤ (x : ℝ) - a := by
    have : ((a : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha
    simpa using this
  calc ∑' k, M.Zpmf k * f (DividendModel.Tnext x a k)
      ≤ ∑' k, M.Zpmf k * ENNReal.ofReal ((A * ((x : ℝ) - a) + B) + A * max (k : ℝ) 0) := by
        refine ENNReal.tsum_le_tsum fun k => mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (hf _).trans (ENNReal.ofReal_le_ofReal ?_)
        unfold DividendModel.Tnext
        rw [if_pos hx]
        push_cast
        have : max ((x : ℝ) - a + k) 0 ≤ ((x : ℝ) - a) + max (k : ℝ) 0 := by
          apply max_le
          · linarith [le_max_left (k : ℝ) 0]
          · linarith [le_max_right (k : ℝ) 0]
        nlinarith [mul_le_mul_of_nonneg_left this hA]
    _ = ENNReal.ofReal (A * ((x : ℝ) - a) + B + A * M.EZplus) :=
        tsum_bound M _ _ (by positivity) hA

/-- From a ruined state `x < 0` the state is frozen. -/
theorem step_neg (x : ℤ) (hx : x < 0) (a : ℕ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ y, f y ∂(M.toMDM.step (x, a)) = f x := by
  rw [step_lint]
  unfold DividendModel.Tnext
  simp only [if_neg (show ¬ 0 ≤ x by omega)]
  rw [ENNReal.tsum_mul_right, M.Zpmf.tsum_coe, one_mul]

theorem memD (x : ℤ) (a : ℕ) : a ∈ M.toMDM.Dx x ↔ (0 ≤ x → (a : ℤ) ≤ x) ∧ (x < 0 → a = 0) := by
  show a ∈ DividendModel.D x ↔ _
  unfold DividendModel.D
  split_ifs with h
  · simp only [Set.mem_setOf_eq]
    constructor
    · intro ha; exact ⟨fun _ => ha, fun h' => absurd h h'.not_ge⟩
    · intro ha; exact ha.1 h
  · simp only [Set.mem_singleton_iff]
    constructor
    · intro ha; exact ⟨fun h' => absurd h' h, fun _ => ha⟩
    · intro ha; exact ha.2 (lt_of_not_ge h)

/-- The bounding function `b(x) = 1 + x` on `x ≥ 0`, `0` on the ruin states. -/
noncomputable def bfun (x : ℤ) : ℝ := if 0 ≤ x then 1 + (x : ℝ) else 0

theorem bfun_le (y : ℤ) : bfun y ≤ max (y : ℝ) 0 + 1 := by
  unfold bfun; split_ifs
  · linarith [le_max_left (y : ℝ) 0]
  · linarith [le_max_right (y : ℝ) 0]

theorem bfun_nonneg (y : ℤ) : 0 ≤ bfun y := by
  unfold bfun; split_ifs with h
  · have : (0 : ℝ) ≤ y := by exact_mod_cast h
    linarith
  · exact le_rfl

theorem beta_pos : 0 < M.β := M.hβ.1
theorem beta_lt : M.β < 1 := M.hβ.2

noncomputable def K : ℝ := M.β * M.EZplus / (1 - M.β)

theorem K_nonneg : 0 ≤ K M := by
  unfold K
  exact div_nonneg (mul_nonneg (beta_pos M).le (EZplus_nonneg M)) (by linarith [beta_lt M])

theorem K_eq : K M * (1 - M.β) = M.β * M.EZplus := by
  unfold K
  field_simp [show (1 - M.β) ≠ 0 by linarith [beta_lt M]]

/-- `H(x) := x + β𝔼Z⁺/(1-β)` on `x ≥ 0`, `0` on the ruin states. -/
noncomputable def H (x : ℤ) : ℝ := if 0 ≤ x then (x : ℝ) + K M else 0

theorem H_le (y : ℤ) : H M y ≤ 1 * max (y : ℝ) 0 + K M := by
  unfold H; split_ifs
  · linarith [le_max_left (y : ℝ) 0]
  · linarith [le_max_right (y : ℝ) 0, K_nonneg M]

theorem Jnpi_le : ∀ (n : ℕ) (π : ℕ → ℤ → ℕ), M.toMDM.IsPolicyOf π → ∀ x,
    Jnpi M.toMDM π n x ≤ ENNReal.ofReal (H M x) := by
  intro n
  induction n with
  | zero => intro π _ x; exact bot_le
  | succ n ih =>
    intro π hπ x
    have hπ' : M.toMDM.IsPolicyOf (fun k => π (k + 1)) := fun k => hπ (k + 1)
    have hmem : π 0 x ∈ M.toMDM.Dx x := (hπ 0).2 x
    rw [memD] at hmem
    show M.toMDM.r (x, π 0 x) + ENNReal.ofReal M.toMDM.β *
      ∫⁻ y, Jnpi M.toMDM (fun k => π (k + 1)) n y ∂(M.toMDM.step (x, π 0 x)) ≤ _
    by_cases hx : 0 ≤ x
    · have ha := hmem.1 hx
      have hI := step_bound M x hx (π 0 x) ha _ 1 (K M) zero_le_one (K_nonneg M)
        (fun y => (ih _ hπ' y).trans (ENNReal.ofReal_le_ofReal (H_le M y)))
      have hr : M.toMDM.r (x, π 0 x) = ENNReal.ofReal (π 0 x : ℝ) := by
        show ((π 0 x : ℕ) : ℝ≥0∞) = _
        rw [ENNReal.ofReal_natCast]
      rw [hr]
      calc ENNReal.ofReal (π 0 x : ℝ) + ENNReal.ofReal M.toMDM.β *
            ∫⁻ y, Jnpi M.toMDM (fun k => π (k + 1)) n y ∂(M.toMDM.step (x, π 0 x))
          ≤ ENNReal.ofReal (π 0 x : ℝ) + ENNReal.ofReal M.β *
            ENNReal.ofReal (1 * ((x : ℝ) - π 0 x) + K M + 1 * M.EZplus) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (by positivity) :
              ENNReal.ofReal M.β * _ ≤ ENNReal.ofReal M.β * _)
        _ = ENNReal.ofReal ((π 0 x : ℝ) +
              M.β * (1 * ((x : ℝ) - π 0 x) + K M + 1 * M.EZplus)) := by
            rw [← ENNReal.ofReal_mul (beta_pos M).le, ← ENNReal.ofReal_add (by positivity)]
            have : (0 : ℝ) ≤ (x : ℝ) - π 0 x := by
              have : ((π 0 x : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha
              simpa using this
            exact mul_nonneg (beta_pos M).le (by nlinarith [K_nonneg M, EZplus_nonneg M])
        _ ≤ ENNReal.ofReal (H M x) := by
            apply ENNReal.ofReal_le_ofReal
            unfold H; rw [if_pos hx]
            have hax : ((π 0 x : ℕ) : ℝ) ≤ (x : ℝ) := by
              have : ((π 0 x : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha
              simpa using this
            have := K_eq M
            nlinarith [beta_lt M, beta_pos M]
    · have hx' : x < 0 := lt_of_not_ge hx
      have h0 := hmem.2 hx'
      rw [step_neg M x hx', h0]
      have := ih _ hπ' x
      unfold H at this ⊢
      rw [if_neg hx] at this ⊢
      rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
      rw [this]
      show ((0 : ℕ) : ℝ≥0∞) + _ * 0 ≤ _
      simp

theorem Jinf_le (x : ℤ) : M.Jinf x ≤ ENNReal.ofReal (H M x) :=
  iSup₂_le fun π hπ => iSup_le fun n => Jnpi_le M n π hπ x


theorem Jinf_ge (π : ℕ → ℤ → ℕ) (hπ : M.toMDM.IsPolicyOf π) (n : ℕ) (x : ℤ) :
    Jnpi M.toMDM π n x ≤ M.Jinf x :=
  le_iSup₂_of_le π hπ (le_iSup_of_le n le_rfl)

/-- Pay out everything. -/
def pall : ℕ → ℤ → ℕ := fun _ x => x.toNat

theorem pall_pol : M.toMDM.IsPolicyOf pall := by
  intro n
  refine ⟨measurable_of_countable _, fun x => ?_⟩
  show x.toNat ∈ M.toMDM.Dx x
  rw [memD]
  constructor
  · intro hx; omega
  · intro hx; omega

theorem q_zero_of {s : Set ℤ} (hs : M.Zpmf.toMeasure s = 1) (k : ℤ) (hk : k ∉ s) : M.Zpmf k = 0 := by
  have hc : M.Zpmf.toMeasure sᶜ = 0 := by
    rw [measure_compl (MeasurableSet.of_discrete) (measure_ne_top _ _), hs, measure_univ, tsub_self]
  have : M.Zpmf.toMeasure {k} = 0 :=
    measure_mono_null (Set.singleton_subset_iff.mpr hk) hc
  rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at this

/-- The value of action `a` against `v`. -/
noncomputable def val (v : ℤ → ℝ≥0∞) (x : ℤ) (a : ℕ) : ℝ≥0∞ :=
  M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, v y ∂(M.toMDM.step (x, a))

theorem is_max (v : ℤ → ℝ≥0∞) (x : ℤ) (hle : ∀ a ∈ M.toMDM.Dx x, val M v x a ≤ val M v x x.toNat) :
    val M v x x.toNat = TL M.toMDM v x := by
  have hmem : x.toNat ∈ M.toMDM.Dx x := (pall_pol M 0).2 x
  exact le_antisymm (le_iSup₂ (f := fun a _ => val M v x a) x.toNat hmem) (iSup₂_le hle)

theorem largest (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar)
    (h : ∀ x, ∀ a ∈ M.toMDM.Dx x, val M M.Jinf x a ≤ val M M.Jinf x x.toNat) (x : ℤ) :
    (fstar x : ℤ) = max x 0 := by
  have hg : M.toMDM.IsMaximizerOf M.Jinf (fun y => y.toNat) :=
    ⟨(pall_pol M 0), fun y => is_max M M.Jinf y (h y)⟩
  have h1 := hfstar.2 _ hg x
  have h2 : fstar x ∈ M.toMDM.Dx x := hfstar.1.1.2 x
  rw [memD] at h2
  by_cases hx : 0 ≤ x
  · have := h2.1 hx
    rw [max_eq_left hx]; omega
  · have := h2.2 (by omega)
    rw [this, max_eq_right (by omega)]; rfl

end Div924

open Div924 in
theorem solution (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (M.Zpmf.toMeasure {k : ℤ | k ≤ 0} = 1 →
        (∀ x : ℤ, M.Jinf x = ((max x 0).toNat : ℝ≥0∞)) ∧ ∀ x : ℤ, (fstar x : ℤ) = max x 0) ∧
      (M.Zpmf.toMeasure {k : ℤ | 0 ≤ k} = 1 →
        (∀ x : ℤ, 0 ≤ x → M.Jinf x = ENNReal.ofReal ((x : ℝ) + M.β * M.EZ / (1 - M.β))) ∧
          ∀ x : ℤ, (fstar x : ℤ) = max x 0) := by
  have hβ := beta_pos M
  have hβ1 := beta_lt M
  constructor
  · intro hZ
    have hq : ∀ k : ℤ, 0 < k → M.Zpmf k = 0 := fun k hk =>
      q_zero_of M hZ k (by simp only [Set.mem_setOf_eq]; omega)
    have hE : M.EZplus = 0 := by
      unfold DividendModel.EZplus
      refine (tsum_congr fun k => ?_).trans tsum_zero
      by_cases hk : 0 < k
      · simp [DividendModel.q, hq k hk]
      · have : (k : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp hk)
        simp [max_eq_right this]
    have hK : K M = 0 := by unfold K; rw [hE]; simp
    have hJ : ∀ x : ℤ, M.Jinf x = ((max x 0).toNat : ℝ≥0∞) := by
      intro x
      apply le_antisymm
      · refine (Jinf_le M x).trans (le_of_eq ?_)
        unfold H; rw [hK]
        rw [← ENNReal.ofReal_natCast]
        congr 1
        split_ifs with hx
        · rw [max_eq_left hx]
          have h := Int.toNat_of_nonneg hx
          have : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast h
          rw [this, add_zero]
        · rw [max_eq_right (by omega)]; simp
      · refine le_trans ?_ (Jinf_ge M pall (pall_pol M) 1 x)
        show _ ≤ M.toMDM.r (x, x.toNat) + _
        refine le_trans ?_ le_self_add
        show _ ≤ ((x.toNat : ℕ) : ℝ≥0∞)
        rw [show (max x 0).toNat = x.toNat by omega]
    refine ⟨hJ, largest M fstar hfstar ?_⟩
    intro x a ha
    rw [memD] at ha
    by_cases hx : 0 ≤ x
    · -- every action is worth at most `x`, and paying everything is worth at least `x`
      have hJ' : ∀ y, M.Jinf y ≤ ENNReal.ofReal (1 * max (y : ℝ) 0 + 0) := by
        intro y; rw [hJ]
        rw [← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        rcases le_total 0 y with hy | hy
        · have h := Int.toNat_of_nonneg hy
          have : ((y.toNat : ℕ) : ℝ) = (y : ℝ) := by exact_mod_cast h
          rw [max_eq_left hy, this, max_eq_left (by exact_mod_cast hy)]; simp
        · rw [max_eq_right hy]; simp
      have hI := step_bound M x hx a (ha.1 hx) M.Jinf 1 0 zero_le_one le_rfl hJ'
      rw [hE] at hI
      have hxa : ((a : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha.1 hx
      push_cast at hxa
      calc val M M.Jinf x a
          ≤ ENNReal.ofReal (a : ℝ) + ENNReal.ofReal M.β *
              ENNReal.ofReal (1 * ((x : ℝ) - a) + 0 + 1 * 0) := by
            unfold val
            show ((a : ℕ) : ℝ≥0∞) + _ ≤ _
            rw [← ENNReal.ofReal_natCast]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (by positivity) :
              ENNReal.ofReal M.β * _ ≤ ENNReal.ofReal M.β * _)
        _ = ENNReal.ofReal ((a : ℝ) + M.β * ((x : ℝ) - a)) := by
            rw [← ENNReal.ofReal_mul hβ.le, ← ENNReal.ofReal_add (Nat.cast_nonneg _)
              (mul_nonneg hβ.le (by linarith))]
            ring_nf
        _ ≤ ENNReal.ofReal (x : ℝ) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith
        _ ≤ val M M.Jinf x x.toNat := by
            unfold val
            refine le_trans ?_ le_self_add
            show _ ≤ ((x.toNat : ℕ) : ℝ≥0∞)
            rw [← ENNReal.ofReal_natCast]
            apply ENNReal.ofReal_le_ofReal
            have : ((x.toNat : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx
            push_cast at this; linarith
    · have h0 := ha.2 (by omega)
      rw [h0, show x.toNat = 0 by omega]
  · intro hZ
    have hq : ∀ k : ℤ, k < 0 → M.Zpmf k = 0 := fun k hk =>
      q_zero_of M hZ k (by simp only [Set.mem_setOf_eq]; omega)
    have hEZ : M.EZ = M.EZplus := by
      unfold DividendModel.EZ DividendModel.EZplus
      refine tsum_congr fun k => ?_
      by_cases hk : k < 0
      · simp [DividendModel.q, hq k hk]
      · have : (0 : ℝ) ≤ k := by exact_mod_cast (not_lt.mp hk)
        rw [max_eq_left this]
    set E := M.EZplus with hEdef
    have hE0 : 0 ≤ E := EZplus_nonneg M
    set c := K M with hc
    have hc0 : 0 ≤ c := K_nonneg M
    have hcE : c * (1 - M.β) = M.β * E := K_eq M
    -- the value of paying everything
    have hpall : ∀ n : ℕ, ∀ x : ℤ, 0 ≤ x →
        Jnpi M.toMDM pall (n + 1) x = ENNReal.ofReal ((x : ℝ) + c * (1 - M.β ^ n)) := by
      intro n
      induction n with
      | zero =>
        intro x hx
        show M.toMDM.r (x, x.toNat) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, Jnpi M.toMDM
          (fun k => pall (k + 1)) 0 y ∂(M.toMDM.step (x, x.toNat)) = _
        show ((x.toNat : ℕ) : ℝ≥0∞) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, (0 : ℝ≥0∞) ∂_ = _
        rw [lintegral_zero, mul_zero, add_zero, ← ENNReal.ofReal_natCast]
        congr 1
        have : ((x.toNat : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx
        push_cast at this; rw [this]; simp
      | succ n ih =>
        intro x hx
        show ((x.toNat : ℕ) : ℝ≥0∞) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, Jnpi M.toMDM
          (fun k => pall (k + 1)) (n + 1) y ∂(M.toMDM.step (x, x.toNat)) = _
        have hsh : (fun k => pall (k + 1)) = pall := rfl
        rw [hsh, step_lint]
        have hT : ∀ k, M.Zpmf k * Jnpi M.toMDM pall (n + 1) (DividendModel.Tnext x x.toNat k) =
            M.Zpmf k * ENNReal.ofReal (c * (1 - M.β ^ n) + 1 * max (k : ℝ) 0) := by
          intro k
          by_cases hk : k < 0
          · rw [hq k hk, zero_mul, zero_mul]
          · have hk0 : 0 ≤ k := by omega
            unfold DividendModel.Tnext
            rw [if_pos hx, show x - (x.toNat : ℤ) + k = k by omega, ih k hk0,
              max_eq_left (by exact_mod_cast hk0 : (0 : ℝ) ≤ k)]
            ring_nf
        rw [tsum_congr hT, tsum_bound M _ _ (by
          have : M.β ^ n ≤ 1 := pow_le_one₀ hβ.le hβ1.le
          nlinarith) zero_le_one]
        rw [show M.toMDM.β = M.β from rfl]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hβ.le,
          ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by
            have : M.β ^ n ≤ 1 := pow_le_one₀ hβ.le hβ1.le
            have := EZplus_nonneg M
            have : 0 ≤ c * (1 - M.β ^ n) := mul_nonneg hc0 (by linarith)
            positivity)]
        congr 1
        have : ((x.toNat : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx
        push_cast at this; rw [this]
        rw [pow_succ]
        show (x : ℝ) + M.β * (c * (1 - M.β ^ n) + 1 * E) = _
        nlinarith
    have hJx : ∀ x : ℤ, 0 ≤ x → M.Jinf x = ENNReal.ofReal ((x : ℝ) + c) := by
      intro x hx
      apply le_antisymm
      · refine (Jinf_le M x).trans (le_of_eq ?_)
        unfold H; rw [if_pos hx]
      · have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((x : ℝ) + c * (1 - M.β ^ n))) atTop
            (nhds (ENNReal.ofReal ((x : ℝ) + c))) := by
          apply ENNReal.tendsto_ofReal
          have := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
          have h2 := ((this.const_sub 1).const_mul c).const_add (x : ℝ)
          simpa using h2
        refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
        rw [← hpall n x hx]
        exact Jinf_ge M pall (pall_pol M) (n + 1) x
    refine ⟨fun x hx => ?_, largest M fstar hfstar ?_⟩
    · rw [hJx x hx, hEZ, hc]; rfl
    · intro x a ha
      rw [memD] at ha
      by_cases hx : 0 ≤ x
      · have hsum : ∀ b : ℕ, (b : ℤ) ≤ x → ∫⁻ y, M.Jinf y ∂(M.toMDM.step (x, b)) =
            ENNReal.ofReal (((x : ℝ) - b + c) + 1 * E) := by
          intro b hb
          rw [step_lint]
          have hT : ∀ k, M.Zpmf k * M.Jinf (DividendModel.Tnext x b k) =
              M.Zpmf k * ENNReal.ofReal (((x : ℝ) - b + c) + 1 * max (k : ℝ) 0) := by
            intro k
            by_cases hk : k < 0
            · rw [hq k hk, zero_mul, zero_mul]
            · have hk0 : 0 ≤ k := by omega
              unfold DividendModel.Tnext
              rw [if_pos hx, hJx _ (by omega), max_eq_left (by exact_mod_cast hk0 : (0 : ℝ) ≤ k)]
              push_cast; ring_nf
          rw [tsum_congr hT, tsum_bound M _ _ (by
            have : ((b : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hb
            push_cast at this; linarith) zero_le_one]
        have hval : ∀ b : ℕ, (b : ℤ) ≤ x → val M M.Jinf x b =
            ENNReal.ofReal ((b : ℝ) + M.β * (((x : ℝ) - b + c) + 1 * E)) := by
          intro b hb
          have : ((b : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hb
          push_cast at this
          unfold val
          show ((b : ℕ) : ℝ≥0∞) + ENNReal.ofReal M.β * _ = _
          rw [hsum b hb, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hβ.le,
            ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by nlinarith)]
        have hxx : ((x.toNat : ℕ) : ℤ) ≤ x := by omega
        rw [hval a (ha.1 hx), hval _ hxx]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ((a : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha.1 hx
        have h2 : ((x.toNat : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx
        push_cast at h1 h2
        rw [h2]
        nlinarith
      · have h0 := ha.2 (by omega)
        rw [h0, show x.toNat = 0 by omega]

#print axioms solution
