-- Prove2me | solution 1 for HarmonicGames.Projection.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:09:39.740388+00:00
-- url     : https://prove2.me/submissions/89980e4b-a2c9-453a-81eb-8db373015fe2

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Closest
import Theorems.Thm_HarmonicGames_Decomposition_theorem_4_1
import Theorems.Thm_HarmonicGames_Decomposition_lemma_4_4_i
import Theorems.Thm_HarmonicGames_Decomposition_lemma_4_4_iii
import Theorems.Thm_HarmonicGames_Decomposition_lemma_4_4_iv
import Theorems.Thm_HarmonicGames_Projection_theorem_5_1
import Theorems.Thm_HarmonicGames_Projection_theorem_6_1

open HarmonicGames.Decomposition
open HarmonicGames.Projection (innerME normME toGames IsClosestPotential IsClosestHarmonic)

section Aux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

private abbrev F := ι → (∀ k, E k) → ℝ

private lemma innerME_comm (a b : ι → (∀ k, E k) → ℝ) : innerME E a b = innerME E b a := by
  unfold innerME
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

private lemma innerME_add_left (a b c : ι → (∀ k, E k) → ℝ) :
    innerME E (a + b) c = innerME E a c + innerME E b c := by
  simp [innerME, add_mul, mul_add, Finset.sum_add_distrib]

private lemma innerME_add_right (a b c : ι → (∀ k, E k) → ℝ) :
    innerME E a (b + c) = innerME E a b + innerME E a c := by
  rw [innerME_comm, innerME_add_left, innerME_comm E b a, innerME_comm E c a]

private lemma innerME_self_nonneg (a : ι → (∀ k, E k) → ℝ) : 0 ≤ innerME E a a :=
  Finset.sum_nonneg fun m _ =>
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun p _ => mul_self_nonneg _)

private lemma innerME_self_eq_zero [∀ m, Nonempty (E m)] (a : ι → (∀ k, E k) → ℝ)
    (h : innerME E a a = 0) : a = 0 := by
  unfold innerME at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun p _ => mul_self_nonneg (a m p)))).1 h
  funext m p
  have h2 := h1 m (Finset.mem_univ m)
  have hc : (Fintype.card (E m) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := E m)).ne'
  have h3 : ∑ p, a m p * a m p = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hc
    · exact h
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_self_nonneg (a m p))).1 h3 p
    (Finset.mem_univ p)
  simpa using h4

private lemma closest_iff [∀ m, Nonempty (E m)] (S : Set (ι → (∀ k, E k) → ℝ))
    (hS : ∀ v ∈ S, ∀ w ∈ S, v - w ∈ S) (u q : ι → (∀ k, E k) → ℝ) (hq : q ∈ S)
    (horth : ∀ w ∈ S, innerME E (u - q) w = 0) (û : ι → (∀ k, E k) → ℝ) :
    (û ∈ S ∧ ∀ v ∈ S, normME E (u - û) ≤ normME E (u - v)) ↔ û = q := by
  have hid : ∀ v ∈ S, innerME E (u - v) (u - v) =
      innerME E (u - q) (u - q) + innerME E (q - v) (q - v) := by
    intro v hv
    have e : u - v = (u - q) + (q - v) := (sub_add_sub_cancel u q v).symm
    have hw : innerME E (u - q) (q - v) = 0 := horth _ (hS q hq v hv)
    have hw' : innerME E (q - v) (u - q) = 0 := by rw [innerME_comm]; exact hw
    rw [e, innerME_add_left, innerME_add_right, innerME_add_right, hw, hw']
    ring
  constructor
  · rintro ⟨hû, hmin⟩
    have h1 := hmin q hq
    unfold normME at h1
    rw [Real.sqrt_le_sqrt_iff (innerME_self_nonneg E _)] at h1
    have h2 := hid û hû
    have h3 : innerME E (q - û) (q - û) = 0 :=
      le_antisymm (by linarith) (innerME_self_nonneg E _)
    have h4 := innerME_self_eq_zero E _ h3
    exact (sub_eq_zero.1 h4).symm
  · rintro rfl
    refine ⟨hq, fun v hv => ?_⟩
    unfold normME
    apply Real.sqrt_le_sqrt
    rw [hid v hv]
    linarith [innerME_self_nonneg E (û - v)]

/-- a game, as an element of `Games E`, seen again as a plain family of utilities -/
private def fn (X : Games E) : ι → (∀ k, E k) → ℝ := fun m p => X m p

private lemma toGames_fn (X : Games E) : toGames E (fn E X) = X := by
  ext m p
  simp [fn, HarmonicGames.Projection.toGames_apply]

private lemma toGames_sub (a b : ι → (∀ k, E k) → ℝ) :
    toGames E (a - b) = toGames E a - toGames E b := by
  ext m p
  simp [HarmonicGames.Projection.toGames_apply]

private lemma c1_sum_apply {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {κ : Type*} (s : Finset κ) (X : κ → C1 G) (p q : V) :
    (∑ k ∈ s, X k) p q = ∑ k ∈ s, X k p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- `D_m†` only sees the `m`-edges, where `δ0 φ` and `D_m φ` agree. -/
private lemma adjoint_Dm_delta0 (m : ι) (φ : Util E) :
    LinearMap.adjoint (Dm E m) (delta0 (gameGraph E) φ) =
      LinearMap.adjoint (Dm E m) (Dm E m φ) := by
  refine ext_inner_right ℝ fun y => ?_
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  show innerC1 (gameGraph E) _ _ = innerC1 (gameGraph E) _ _
  unfold innerC1
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hadj
  · by_cases hc : MComparable E m p q
    · have h1 : (delta0 (gameGraph E) φ) p q = (Dm E m φ) p q := by
        show (if (gameGraph E).Adj p q then (1 : ℝ) else 0) * (φ q - φ p) =
          (if MComparable E m p q then (1 : ℝ) else 0) * (φ q - φ p)
        rw [if_pos hadj, if_pos hc]
      rw [h1]
    · have h0 : (Dm E m y) p q = 0 := by
        show (if MComparable E m p q then (1 : ℝ) else 0) * (y q - y p) = 0
        rw [if_neg hc, zero_mul]
      rw [h0]; simp
  · rfl

end Aux

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : ι → (∀ m, E m) → ℝ) (φ : HarmonicGames.Decomposition.Util E) (hφ : φ = HarmonicGames.Decomposition.potentialFunction E (HarmonicGames.Projection.toGames E u)) :
    (∀ û : ι → (∀ m, E m) → ℝ, HarmonicGames.Projection.IsClosestPotential E u û ↔
        û = fun m p => HarmonicGames.Decomposition.Pim E m φ p + (u m p - HarmonicGames.Decomposition.Pim E m (WithLp.toLp 2 (u m)) p)) ∧
      (∀ û : ι → (∀ m, E m) → ℝ, HarmonicGames.Projection.IsClosestHarmonic E u û ↔
        û = fun m p => u m p - HarmonicGames.Decomposition.Pim E m φ p) := by
  classical
  set U := toGames E u with hU
  obtain ⟨hmem, -⟩ := (theorem_4_1 ι E).2
  obtain ⟨hsum, hPmem, hHmem, hNmem⟩ := hmem U
  set uP := potentialComponent E U
  set uH := harmonicComponent E U
  set uN := nonstrategicComponent E U
  have hpt : ∀ m p, uP m p + uH m p + uN m p = u m p := fun m p => by
    have := congrArg (fun w : Games E => w m p) hsum
    simpa [hU, HarmonicGames.Projection.toGames_apply] using this
  -- explicit formulas for the components
  have hNform : ∀ m p, uN m p = u m p - Pim E m (WithLp.toLp 2 (u m)) p := by
    intro m p
    have h4 := LinearMap.congr_fun (lemma_4_4_iv ι E) U
    have : uN = U - PiOp E U := by
      show (LinearMap.id - pinv (Dop E) ∘ₗ Dop E : Games E →ₗ[ℝ] Games E) U = U - PiOp E U
      rw [LinearMap.sub_apply, LinearMap.id_apply, ← h4]
    rw [this]
    simp [hU, PiOp, HarmonicGames.Projection.toGames_apply]
    try rfl
  have hPform : ∀ m p, uP m p = Pim E m φ p := by
    intro m p
    have h1 : uP = pinv (Dop E) (delta0 (gameGraph E) φ) := by
      show pinv (Dop E) (delta0 (gameGraph E) (pinv (delta0 (gameGraph E)) (Dop E U))) = _
      rw [hφ]; rfl
    have h2 : uP m = pinv (Dm E m) (delta0 (gameGraph E) φ) := by
      rw [h1]; exact lemma_4_4_iii ι E _ m
    have h3 : pinv (Dm E m) (delta0 (gameGraph E) φ) = Pim E m φ := by
      show pinv (Dm E m) (delta0 (gameGraph E) φ) = pinv (Dm E m) (Dm E m φ)
      rw [lemma_4_4_i ι E m]
      simp only [LinearMap.smul_apply, adjoint_Dm_delta0]
    have := congrArg (fun v : Util E => v p) (h2.trans h3)
    exact this
  have hF : ∀ (X Y : Games E), (fn E X + fn E Y) = fn E (X + Y) := by
    intro X Y; funext m p; rfl
  constructor
  · intro û
    -- closest potential game
    have hS : ∀ v w : ι → (∀ k, E k) → ℝ, MondererShapley.ClosedPath.IsPotentialGame v →
        MondererShapley.ClosedPath.IsPotentialGame w →
        MondererShapley.ClosedPath.IsPotentialGame (v - w) := by
      intro v w hv hw
      rw [HarmonicGames.Projection.theorem_5_1 E] at hv hw ⊢
      rw [toGames_sub]
      exact Submodule.sub_mem _ hv hw
    have hqS : MondererShapley.ClosedPath.IsPotentialGame (fn E (uP + uN)) := by
      rw [HarmonicGames.Projection.theorem_5_1 E, toGames_fn]
      exact Submodule.mem_sup.2 ⟨_, hPmem, _, hNmem, rfl⟩
    have hres : u - fn E (uP + uN) = fn E uH := by
      funext m p
      have := hpt m p
      simp only [Pi.sub_apply, fn, PiLp.add_apply]
      linarith
    have horth : ∀ w, MondererShapley.ClosedPath.IsPotentialGame w →
        innerME E (u - fn E (uP + uN)) w = 0 := by
      intro w hw
      rw [HarmonicGames.Projection.theorem_5_1 E] at hw
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hw
      have hw' : w = fn E x + fn E y := by
        funext m p
        have := congrArg (fun z : Games E => z m p) hxy
        simpa [HarmonicGames.Projection.toGames_apply, fn] using this.symm
      obtain ⟨h61a, h61b, h61c⟩ := HarmonicGames.Projection.theorem_6_1 E
      rw [hres, hw', innerME_add_right]
      have e1 : innerME E (fn E uH) (fn E x) = 0 := by
        rw [innerME_comm]
        exact h61a _ _ (by rw [toGames_fn]; exact hx) (by rw [toGames_fn]; exact hHmem)
      have e2 : innerME E (fn E uH) (fn E y) = 0 :=
        h61c _ _ (by rw [toGames_fn]; exact hHmem) (by rw [toGames_fn]; exact hy)
      rw [e1, e2]; ring
    have key := closest_iff E {v | MondererShapley.ClosedPath.IsPotentialGame v}
      (fun v hv w hw => hS v w hv hw) u (fn E (uP + uN)) hqS (fun w hw => horth w hw) û
    have hform : fn E (uP + uN) = fun m p => Pim E m φ p +
        (u m p - Pim E m (WithLp.toLp 2 (u m)) p) := by
      funext m p
      simp only [fn, PiLp.add_apply]
      rw [hPform, hNform]
    rw [← hform]
    exact key
  · intro û
    -- closest harmonic game
    have hS : ∀ v w : ι → (∀ k, E k) → ℝ, HarmonicGames.Projection.IsHarmonicGame E v →
        HarmonicGames.Projection.IsHarmonicGame E w →
        HarmonicGames.Projection.IsHarmonicGame E (v - w) := by
      intro v w hv hw
      unfold HarmonicGames.Projection.IsHarmonicGame at hv hw ⊢
      rw [toGames_sub]
      exact Submodule.sub_mem _ hv hw
    have hqS : HarmonicGames.Projection.IsHarmonicGame E (fn E (uH + uN)) := by
      unfold HarmonicGames.Projection.IsHarmonicGame
      rw [toGames_fn]
      exact Submodule.mem_sup.2 ⟨_, hHmem, _, hNmem, rfl⟩
    have hres : u - fn E (uH + uN) = fn E uP := by
      funext m p
      have := hpt m p
      simp only [Pi.sub_apply, fn, PiLp.add_apply]
      linarith
    have horth : ∀ w, HarmonicGames.Projection.IsHarmonicGame E w →
        innerME E (u - fn E (uH + uN)) w = 0 := by
      intro w hw
      unfold HarmonicGames.Projection.IsHarmonicGame at hw
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hw
      have hw' : w = fn E x + fn E y := by
        funext m p
        have := congrArg (fun z : Games E => z m p) hxy
        simpa [HarmonicGames.Projection.toGames_apply, fn] using this.symm
      obtain ⟨h61a, h61b, h61c⟩ := HarmonicGames.Projection.theorem_6_1 E
      rw [hres, hw', innerME_add_right]
      have e1 : innerME E (fn E uP) (fn E x) = 0 :=
        h61a _ _ (by rw [toGames_fn]; exact hPmem) (by rw [toGames_fn]; exact hx)
      have e2 : innerME E (fn E uP) (fn E y) = 0 :=
        h61b _ _ (by rw [toGames_fn]; exact hPmem) (by rw [toGames_fn]; exact hy)
      rw [e1, e2]; ring
    have key := closest_iff E {v | HarmonicGames.Projection.IsHarmonicGame E v}
      (fun v hv w hw => hS v w hv hw) u (fn E (uH + uN)) hqS (fun w hw => horth w hw) û
    have hform : fn E (uH + uN) = fun m p => u m p - Pim E m φ p := by
      funext m p
      simp only [fn, PiLp.add_apply]
      have := hpt m p
      rw [hPform] at this
      linarith
    rw [← hform]
    exact key
