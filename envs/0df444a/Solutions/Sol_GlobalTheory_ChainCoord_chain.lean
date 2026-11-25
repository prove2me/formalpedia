-- Prove2me | solution 1 for GlobalTheory.ChainCoord.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:10.508071+00:00
-- url     : https://prove2.me/submissions/35f1624f-9360-4c73-8f47-209a8b0712a8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_ChainCoord_ord_mono
import Theorems.Thm_GlobalTheory_ChainCoord_ord_zero
import Theorems.Thm_GlobalTheory_ChainCoord_ord_add
import Theorems.Thm_GlobalTheory_ChainCoord_ord_neg
import Theorems.Thm_GlobalTheory_ChainCoord_ord_sum
import Theorems.Thm_GlobalTheory_ChainCoord_ord_C_mul
import Theorems.Thm_GlobalTheory_ChainCoord_ord_pow
import Theorems.Thm_GlobalTheory_ChainCoord_ord_pure
import Theorems.Thm_GlobalTheory_ChainCoord_ord_of_step
import Theorems.Thm_GlobalTheory_ChainCoord_high_real
import Theorems.Thm_GlobalTheory_ChainCoord_kap_succ
import Theorems.Thm_GlobalTheory_ChainCoord_ord_pure_level
import Theorems.Thm_GlobalTheory_WeightFrobenius_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
namespace GlobalTheory.ChainCoord
theorem _root_.solution :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 3 ≤ l → ∀ (d M s₀ : ℕ) (good : Set (Fin d)) (Gs : ℕ → Finset (Fin d)) (al : Fin d → ℕ → Fin d → C) (π : ℕ → Fin d → Fin M → C)
    (t : Fin d → MvPowerSeries (Fin M) C), (∀ s c, c ∈ Gs s → c ∈ good) → (∀ s s' c, s ≤ s₀ → s' ≤ s₀ → c ∈ Gs s → c ∈ Gs s' → s = s') →
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ c ∈ good, al c 1 = 0 ∧ ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e)) →
    (∀ c j, 0 ≤ v (π 0 c j)) → (∀ c, c ∉ Gs 0 → π 0 c = 0) →
    (∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (R := C) (π 0 e j) * MvPowerSeries.X j) →
    (∀ s ≤ s₀, ∀ c ∈ Gs s, OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c - ∑ j, MvPowerSeries.C (R := C) ((-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹ * π s c j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s)) (1 + 1 / ((l : ℝ) ^ 2 - 1))) ∧
    ∀ c, (∀ s ≤ s₀, c ∉ Gs s) → OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c) (1 + 1 / ((l : ℝ) ^ 2 - 1))) := by
  intro C _ _ v l hp hv hl d M s₀ good Gs al π t hgood huniq h0 hall hg hout hπ0 hπ0' hπ ht hz
  classical
  have h3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hq : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hl0 : (l : C) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 / ((l : ℝ) ^ 2 - 1) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1)) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hρq : (l : ℝ) ^ 2 * ρ = 1 + ρ := by rw [hρ]; field_simp; ring
  have hσq : ((l : ℝ) ^ 2) ^ (s₀ + 1) * σ = 3 * l / 8 := by rw [hσ]; field_simp; ring
  have hv1 : ((1 : ℝ) : WithTop ℝ) ≤ v (l : C) := by rw [hv]; simp

  have hint : ∀ s c j, ((0 : ℝ) : WithTop ℝ) ≤ v (π s c j) := by
    intro s
    induction s with
    | zero => exact hπ0
    | succ s ih =>
      intro e j
      rw [hπ]
      refine v.map_le_sum fun c hc => ?_
      rw [v.map_mul, v.map_mul, v.map_pow]
      have h1 := ((hg c (hgood s c hc)).2 2 e (by norm_num))
      refine le_trans ?_ (add_le_add (add_le_add hv1 h1) (nsmul_nonneg (ih c j) _))
      rw [← WithTop.coe_add]
      norm_num
  have hint1 : ∀ s < s₀, ∀ e, e ∉ Gs (s + 1) → ∀ j,
      ((1 : ℝ) : WithTop ℝ) ≤ v (π (s + 1) e j) := by
    intro s hs e he j
    rw [hπ]
    refine v.map_le_sum fun c hc => ?_
    rw [v.map_mul, v.map_mul, v.map_pow]
    refine le_trans ?_ (add_le_add (add_le_add hv1 (hout s hs c hc e he))
      (nsmul_nonneg (hint s c j) _))
    simp
  have hlev : ∀ (s : ℕ) (c : Fin d) (a : ℝ), (∀ j, (a : WithTop ℝ) ≤ v (π s c j)) → ∀ j,
      ((a + ρ + ((l : ℝ) ^ 2) ^ s * σ - (ρ + σ) * (((l ^ 2) ^ s : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤
        v (kap C l s * π s c j) := fun s c a h j => by
    rw [hρ]; exact ord_pure_level hl hv h j
  have hP : ∀ (s : ℕ) (c : Fin d) (a : ℝ), (∀ j, (a : WithTop ℝ) ≤ v (π s c j)) →
      OrdGe v (fun _ => ρ + σ) (pure l π s c) (a + ρ + ((l : ℝ) ^ 2) ^ s * σ) :=
    fun s c a h => ord_pure (hlev s c a h)
  let μ : Fin d → MvPowerSeries (Fin M) C := fun c =>
    ∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then pure l π s c else 0
  have hsel : ∀ (f : ℕ → MvPowerSeries (Fin M) C) s, s ≤ s₀ → ∀ c ∈ Gs s,
      (∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then f s else 0) = f s := by
    intro f s hs c hc
    rw [Finset.sum_eq_single s, if_pos hc]
    · intro b hb hbs
      rw [if_neg]
      intro h
      exact hbs (huniq b s c (by simpa [Nat.lt_succ_iff] using hb) hs h hc)
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hsel0 : ∀ (f : ℕ → MvPowerSeries (Fin M) C) c, (∀ s ≤ s₀, c ∉ Gs s) →
      (∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then f s else 0) = 0 := fun f c hc =>
    Finset.sum_eq_zero fun s hs => if_neg (hc s (by simpa [Nat.lt_succ_iff] using hs))
  have main : ∀ c, OrdGe v (fun _ => ρ + σ) (t c - μ c) (1 + ρ) := by
    refine ord_of_step (by omega) al h0 t μ _ ht (fun c => ?_) hz _ ?_
    · simp only [μ, map_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      split_ifs
      · simp only [pure, map_sum, map_mul, map_pow, constantCoeff_X]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [zero_pow (by positivity), mul_zero]
      · simp
    intro t' ht' N e
    let F : ℕ → Fin d → MvPowerSeries (Fin M) C := fun s c =>
      MvPowerSeries.C (R := C) (al c 2 e) *
        ∑ j, MvPowerSeries.C (R := C) ((kap C l s * π s c j) ^ (l ^ 2)) *
          (X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s * l ^ 2)
    let G : Fin d → MvPowerSeries (Fin M) C := fun c =>
      ∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then F s c else 0
    have hF : ∀ s, ∑ c ∈ Gs s, F s c = - pure l π (s + 1) e := by
      intro s
      simp only [F, pure, Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_succ, ← neg_mul, ← map_neg, hπ, kap_succ (hp.odd_of_ne_two (by omega)),
        Finset.mul_sum, ← Finset.sum_neg_distrib, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_assoc, ← map_mul]
      congr 2
      rw [mul_pow]
      field_simp
    have hG : ∑ c, G c = - ∑ s ∈ Finset.range (s₀ + 1), pure l π (s + 1) e := by
      simp only [G]
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← hF, Finset.sum_ite_mem, Finset.univ_inter]
    have hz0 : (∑ j, MvPowerSeries.C (R := C) (π 0 e j) * (X j : MvPowerSeries (Fin M) C)) =
        pure l π 0 e := by
      simp [pure, kap]
    have hA : OrdGe v (fun _ => ρ + σ)
        (∑ s ∈ Finset.range (s₀ + 1), (pure l π s e - if e ∈ Gs s then pure l π s e else 0))
        (1 + ρ) := by
      refine ord_sum _ fun s hs => ?_
      split_ifs with he
      · rw [sub_self]; exact ord_zero _
      · rw [sub_zero]
        cases s with
        | zero =>
          have : pure l π 0 e = 0 := by simp [pure, hπ0' e he]
          rw [this]; exact ord_zero _
        | succ s =>
          refine ord_mono (hP _ _ 1 (hint1 s (by simpa using hs) e he)) ?_
          have : 0 ≤ ((l : ℝ) ^ 2) ^ (s + 1) * σ := by positivity
          linarith
    have hB : OrdGe v (fun _ => ρ + σ) (pure l π (s₀ + 1) e) (1 + ρ) :=
      ord_mono (hP _ _ 0 (hint _ e)) (by rw [hσq]; linarith)
    have hT : ∀ n c, OrdGe v (fun _ => ρ + σ)
        (MvPowerSeries.C (R := C) (al c (n + 1) e) * t' c ^ (l ^ (n + 1)) -
          if n = 1 then G c else 0) (1 + ρ) := by
      intro n c
      by_cases hc : ∃ s ≤ s₀, c ∈ Gs s
      · obtain ⟨s, hs, hc⟩ := hc
        have hν := ht' c
        have hμ : μ c = pure l π s c := hsel (fun s => pure l π s c) s hs c hc
        rw [hμ] at hν
        obtain ⟨hg1, hg2⟩ := hg c (hgood s c hc)
        have hqs : 0 ≤ ((l : ℝ) ^ 2) ^ s * σ := by positivity
        match n with
        | 0 => simp [hg1, ord_zero]
        | 1 =>
          have hGc : G c = F s c := hsel (fun s => F s c) s hs c hc
          have h1 := GlobalTheory.WeightFrobenius.main C v l hp hv M ((l ^ 2) ^ s) 2 (ρ + σ) ρ (1 + ρ)
            (fun j => kap C l s * π s c j) (t' c - pure l π s c) (by linarith)
            (fun j => le_trans (WithTop.coe_le_coe.2 (by linarith)) (hlev s c 0 (hint s c) j)) hν
          have h2 := ord_C_mul (hg2 2 e (by norm_num)) h1
          rw [if_pos rfl, hGc]
          refine ord_mono (w := _) (by
            convert h2 using 1
            simp only [F, pure, add_sub_cancel, mul_sub]) ?_
          rw [mul_add, hρq]
          rcases min_cases (1 + (1 + ρ)) ((l : ℝ) ^ 2 * 1 + (1 + ρ)) with h | h <;>
            rw [h.1] <;> push_cast <;> nlinarith
        | k + 2 =>
          rw [if_neg (by omega), sub_zero]
          have h1 : OrdGe v (fun _ => ρ + σ) (t' c) ρ := by
            have := ord_add (ord_mono hν (by linarith : ρ ≤ 1 + ρ))
              (ord_mono (hP s c 0 (hint s c)) (by linarith : ρ ≤ _))
            rwa [sub_add_cancel] at this
          refine ord_mono (ord_C_mul (hg2 _ e (by omega)) (ord_pow h1 _)) ?_
          rw [hρ]
          exact high_real hl k
      · push_neg at hc
        have hν := ht' c
        have hμ : μ c = 0 := hsel0 (fun s => pure l π s c) c hc
        have hGc : G c = 0 := hsel0 (fun s => F s c) c hc
        rw [hμ, sub_zero] at hν
        rw [hGc, ite_self, sub_zero]
        refine ord_mono (ord_C_mul (hall c _ e) (ord_pow hν _)) ?_
        have h1 : n + 1 < l ^ (n + 1) := Nat.lt_pow_self (by omega)
        have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ ((l ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        have h4 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
        nlinarith
    have hS := ord_sum (Finset.range (N + 2)) fun n _ => ord_sum Finset.univ fun c _ => hT n c
    have hfin := ord_add (ord_add hA hB) (ord_neg hS)
    convert hfin using 1
    have hi : ∑ n ∈ Finset.range (N + 2), ∑ c, (if n = 1 then G c else 0) = ∑ c, G c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_ite_eq', if_pos (by simp)]
    have hs : ∑ s ∈ Finset.range (s₀ + 1), pure l π (s + 1) e + pure l π 0 e =
        ∑ s ∈ Finset.range (s₀ + 1), pure l π s e + pure l π (s₀ + 1) e := by
      rw [← Finset.sum_range_succ' (fun s => pure l π s e), Finset.sum_range_succ]
    simp only [Finset.sum_sub_distrib, hi, hG, hz0]
    linear_combination hs
  rw [← hρ, ← hσ]
  refine ⟨fun s hs c hc => ?_, fun c hc => ?_⟩
  · have := main c
    rwa [show μ c = pure l π s c from hsel (fun s => pure l π s c) s hs c hc] at this
  · have := main c
    rwa [show μ c = 0 from hsel0 (fun s => pure l π s c) c hc, sub_zero] at this
end GlobalTheory.ChainCoord
