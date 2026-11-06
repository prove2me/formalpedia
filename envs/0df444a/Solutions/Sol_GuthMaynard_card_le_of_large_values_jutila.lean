-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_values_jutila
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:44:50.649372+00:00
-- url     : https://prove2.me/submissions/143bb4a7-12f0-46e5-9559-93f3a6d52b29

import Mathlib
import Theorems.Thm_GuthMaynard_card_le_of_large_values_jutila_q_one
section
/-!
# Blueprint: Huxley 1972 (2.9), the Montgomery–Halász–Huxley large values estimate

Route (elementary, no ζ):
* `partial_sum_cpow_le` (van der Corput second-derivative test via Kusmin–Landau):
  `|∑_{m ≤ c} m^{-it}| ≪ |t|^{1/2} log(|t|+2)` for `c ≤ 11|t|+2`.
* `block_sum_sub_integral_le` (sum vs integral on a dyadic block where the phase is slow).
* `kernel_bound`: the tent-weighted kernel `K(s) = ∑ w(m) m^{-s}` is
  `≪ N/t² + |t|^{1/2} log(|t|+2) + log(N+2)`.
* `halasz_ineq`, `sum_inv_sq_le_of_separated`, `card_le_of_separated`, `card_le_of_halasz`:
  Halász–Montgomery, giving `R ≪ GN/V²` when `V² ≫ G (T^{1/2} log(T+2) + log(N+2))`.
* `huxley_main`: subdivision of the `t`-range into pieces of length `T₀`.
-/

open Finset Complex

namespace GuthMaynard.CitedLV

noncomputable section

/-! ## Part V: van der Corput partial sums -/

/-! ## Part B: sum versus integral on a block with slowly varying phase -/

/-! ## Part K: the kernel bound -/

/-! ## Part H: Halász–Montgomery and subdivision -/

end

end GuthMaynard.CitedLV
end

section
open Finset Complex

namespace GuthMaynard.CitedLV.PartH

noncomputable section

/-! ## Helpers -/

lemma norm_natCast_cpow_neg_le (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖(m : ℂ) ^ (-z)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm)
  simp; linarith

/-! ## Targets -/

theorem card_le_of_separated {ι : Type*} (P : Finset ι) (t : ι → ℝ) (T : ℝ) (hT0 : 0 ≤ T)
    (ht : ∀ r ∈ P, ∀ q ∈ P, r ≠ q → 1 ≤ |t r - t q|)
    (hT : ∀ r ∈ P, ∀ q ∈ P, |t r - t q| ≤ T) :
    (P.card : ℝ) ≤ T + 1 := by
  classical
  rcases P.eq_empty_or_nonempty with h | hne
  · simp [h]; linarith
  obtain ⟨r0, hr0, hmin⟩ := P.exists_min_image t hne
  let k : ι → ℕ := fun q => ⌊t q - t r0⌋₊
  have hmaps : ∀ q ∈ P, k q ∈ range (⌊T⌋₊ + 1) := by
    intro q hq
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    exact le_trans (le_abs_self _) (hT q hq r0 hr0)
  have hinj : Set.InjOn k P := by
    intro q hq q' hq' h
    by_contra hne
    have hsep := ht q hq q' hq' hne
    have a1 := Nat.floor_le (sub_nonneg.2 (hmin q hq))
    have a2 := Nat.lt_floor_add_one (t q - t r0)
    have a3 := Nat.floor_le (sub_nonneg.2 (hmin q' hq'))
    have a4 := Nat.lt_floor_add_one (t q' - t r0)
    simp only [k] at h
    rw [h] at a1 a2
    have : |t q - t q'| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith
  have := card_le_card_of_injOn k (fun q hq => hmaps q hq) hinj
  simp only [card_range] at this
  calc (P.card : ℝ) ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
    _ ≤ T + 1 := by push_cast; linarith [Nat.floor_le hT0]

end

end GuthMaynard.CitedLV.PartH
end

section
namespace GuthMaynard.CitedLV.Jut
/-!
# Blueprint: Jutila 1977 (1.4) from (1.2) at q = 1 by Huxley's subdivision

Jutila, Acta Arith. 32 (1977), p. 60: "for the proof of (1.4), we use (1.2) and the Huxley subdivision
of the points s_r. It means we apply (1.2) with q = 1, T = T₀ and multiply the resulting estimate by
1 + T₀⁻¹T; an optimal choice of T₀ completes the proof."
-/
/-- Jutila's (1.2) with `q = 1` (the published standalone `GuthMaynard.card_le_of_large_values_jutila_q_one`). -/
theorem jutila12 (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re) → (∀ r q, |(s r).im - (s q).im| ≤ T) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im|) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-s r)‖) →
      let G : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
      (R : ℝ) ≤ C * (G * N / V ^ 2 + T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ k +
        (T * G ^ 2 / V ^ 4) ^ k) * T ^ ε := by
  exact GuthMaynard.card_le_of_large_values_jutila_q_one ε hε k hk

end GuthMaynard.CitedLV.Jut
end

section
open Finset
namespace GuthMaynard.CitedLV.Jut.PartS
noncomputable section
/-! ## Piece decomposition -/
lemma fiber_count {R : ℕ} (t : Fin R → ℝ) (T L : ℝ) (hL : 0 < L) (hLT : L ≤ T)
    (hdiam : ∀ r q, |t r - t q| ≤ T) (X : ℝ)
    (hX : ∀ P : Finset (Fin R), (∀ r ∈ P, ∀ q ∈ P, |t r - t q| ≤ L) → (P.card : ℝ) ≤ X) :
    (R : ℝ) ≤ 2 * (T / L) * X := by
  have hX0 : 0 ≤ X := by simpa using hX ∅ (by simp)
  have hTL : 1 ≤ T / L := by rw [le_div_iff₀ hL]; linarith
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    have : 0 ≤ 2 * (T / L) * X := mul_nonneg (by linarith) hX0
    simpa using this
  obtain ⟨r0, -, hmin⟩ := (univ : Finset (Fin R)).exists_min_image t ⟨⟨0, hR⟩, mem_univ _⟩
  let j : Fin R → ℕ := fun r => ⌊(t r - t r0) / L⌋₊
  set M := ⌊T / L⌋₊ with hM
  have hmaps : ∀ r ∈ (univ : Finset (Fin R)), j r ∈ range (M + 1) := by
    intro r _
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hL.le
    exact (le_abs_self _).trans (hdiam r r0)
  have hcard := card_eq_sum_card_fiberwise hmaps
  have hpiece : ∀ i ∈ range (M + 1),
      ((((univ : Finset (Fin R)).filter (fun r => j r = i)).card : ℕ) : ℝ) ≤ X := by
    intro i _
    apply hX
    intro r hr q hq
    simp only [mem_filter, mem_univ, true_and, j] at hr hq
    have hxr := hmin r (mem_univ _)
    have hxq := hmin q (mem_univ _)
    set xr := (t r - t r0) / L with hxr'
    set xq := (t q - t r0) / L with hxq'
    have a1 : (⌊xr⌋₊ : ℝ) ≤ xr := Nat.floor_le (div_nonneg (sub_nonneg.2 hxr) hL.le)
    have a2 : xr < ⌊xr⌋₊ + 1 := Nat.lt_floor_add_one xr
    have a3 : (⌊xq⌋₊ : ℝ) ≤ xq := Nat.floor_le (div_nonneg (sub_nonneg.2 hxq) hL.le)
    have a4 : xq < ⌊xq⌋₊ + 1 := Nat.lt_floor_add_one xq
    have er : (⌊xr⌋₊ : ℝ) = i := by exact_mod_cast hr
    have eq' : (⌊xq⌋₊ : ℝ) = i := by exact_mod_cast hq
    have dr : xr * L = t r - t r0 := div_mul_cancel₀ _ hL.ne'
    have dq : xq * L = t q - t r0 := div_mul_cancel₀ _ hL.ne'
    have hlt1 : xr - xq ≤ 1 := by linarith
    have hgt1 : -1 ≤ xr - xq := by linarith
    have b1 := mul_le_mul_of_nonneg_right hlt1 hL.le
    have b2 := mul_le_mul_of_nonneg_right hgt1 hL.le
    rw [abs_le]; constructor <;> linarith
  have hsum : (R : ℝ) ≤ (M + 1) * X := by
    have : (R : ℝ) = ∑ i ∈ range (M + 1),
        ((((univ : Finset (Fin R)).filter (fun r => j r = i)).card : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, ← hcard]; simp
    rw [this]
    calc _ ≤ ∑ i ∈ range (M + 1), X := sum_le_sum hpiece
      _ = _ := by simp
  have hMle : (M : ℝ) ≤ T / L := Nat.floor_le (by linarith)
  have : ((M : ℝ) + 1) * X ≤ 2 * (T / L) * X := mul_le_mul_of_nonneg_right (by linarith) hX0
  linarith

/-! ## `jutila12` over an arbitrary `Finset` of indices -/
lemma jut_finset (ε : ℝ) (k : ℕ) (C₀ : ℝ)
    (hJ : ∀ T : ℝ, 2 ≤ T → ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re) → (∀ r q, |(s r).im - (s q).im| ≤ T) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im|) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-s r)‖) →
      let G : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
      (R : ℝ) ≤ C₀ * (G * N / V ^ 2 + T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ k +
        (T * G ^ 2 / V ^ 4) ^ k) * T ^ ε)
    (L : ℝ) (hL : 2 ≤ L) (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (V : ℝ) (hV : 0 < V)
    {R : ℕ} (s : Fin R → ℂ) (hre : ∀ r, 0 ≤ (s r).re)
    (hsep : ∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im|)
    (hF : ∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-s r)‖)
    (P : Finset (Fin R)) (hP : ∀ r ∈ P, ∀ q ∈ P, |(s r).im - (s q).im| ≤ L) :
    (P.card : ℝ) ≤ C₀ * ((∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2) * N / V ^ 2 +
      L * ((∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2) ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ k +
        (L * (∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2) ^ 2 / V ^ 4) ^ k) * L ^ ε := by
  let e := P.equivFin
  let s' : Fin P.card → ℂ := fun i => s ((e.symm i : P) : Fin R)
  exact hJ L hL N hN a V hV P.card s' (fun i => hre _)
    (fun i j => hP _ (e.symm i).2 _ (e.symm j).2)
    (fun i j hij => hsep _ _ (fun h => hij (e.symm.injective (Subtype.ext h))))
    (fun i => hF _)

/-! ## Real-power identities -/
lemma mid_eq (G N V κ : ℝ) (hG : 0 < G) (hN : 0 < N) (hV : 0 < V) :
    G ^ (3 - 1 / κ) * N ^ (1 - 1 / κ) * V ^ (-6 + 2 / κ) * (G * N / V ^ 2) ^ (1 / κ) =
      G * N / V ^ 2 * (G ^ 2 / V ^ 4) := by
  have h1 : (G * N / V ^ 2) ^ (1 / κ) = G ^ (1 / κ) * N ^ (1 / κ) / V ^ ((2 : ℕ) * (1 / κ)) := by
    rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hG.le hN.le,
      ← Real.rpow_natCast V 2, ← Real.rpow_mul hV.le]
  rw [h1]
  have h2 : G ^ (3 - 1 / κ) * N ^ (1 - 1 / κ) * V ^ (-6 + 2 / κ) *
      (G ^ (1 / κ) * N ^ (1 / κ) / V ^ ((2 : ℕ) * (1 / κ))) =
      (G ^ (3 - 1 / κ) * G ^ (1 / κ)) * (N ^ (1 - 1 / κ) * N ^ (1 / κ)) *
        (V ^ (-6 + 2 / κ) / V ^ ((2 : ℕ) * (1 / κ))) := by ring
  rw [h2, ← Real.rpow_add hG, ← Real.rpow_add hN, ← Real.rpow_sub hV]
  have e1 : (3 : ℝ) - 1 / κ + 1 / κ = ((3 : ℕ) : ℝ) := by push_cast; ring
  have e2 : (1 : ℝ) - 1 / κ + 1 / κ = 1 := by ring
  have e3 : (-6 : ℝ) + 2 / κ - (2 : ℕ) * (1 / κ) = -((6 : ℕ) : ℝ) := by push_cast; ring
  rw [e1, e2, e3, Real.rpow_natCast, Real.rpow_one, Real.rpow_neg hV.le, Real.rpow_natCast]
  field_simp

lemma T0_pow (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (m : ℕ) :
    (A ^ (1 / ((m + 1 : ℕ) : ℝ)) / B) ^ (m + 1) * B ^ (m + 1) = A := by
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hB.ne'), one_div,
    Real.rpow_inv_natCast_pow hA (by omega)]

/-! ## The abstract case analysis -/
lemma abstract_bound (ε : ℝ) (hε : 0 < ε) (m : ℕ) (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (T : ℝ)
    (hT : 2 ≤ T) (A B D T₀ : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hD : 0 ≤ D) (hT₀ : 0 < T₀)
    (hk : T₀ ^ (m + 1) * B ^ (m + 1) = A) (R : ℝ) (hRT : R ≤ T + 1)
    (hpiece : ∀ L, 2 ≤ L → L ≤ T →
      R ≤ 2 * (T / L) * (C₁ * (A + L * D ^ (m + 1) + (L * B) ^ (m + 1)) * T ^ ε)) :
    R ≤ (2 + 2 ^ (m + 1 + 1) * C₁) * (A + T * (A / T₀) + T * D ^ (m + 1)) * T ^ ε := by
  set S := A + T * (A / T₀) + T * D ^ (m + 1) with hS
  set Te := T ^ ε with hTe
  set P2 : ℝ := 2 ^ m with hP2
  have hTe1 : 1 ≤ Te := Real.one_le_rpow (by linarith) hε.le
  have hP21 : 1 ≤ P2 := one_le_pow₀ (by norm_num)
  have h2P : (2 : ℝ) ^ (m + 1 + 1) = 4 * P2 := by rw [hP2]; ring
  rw [h2P]
  have hAT : 0 ≤ A / T₀ := by positivity
  have hDk : 0 ≤ D ^ (m + 1) := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hTD : 0 ≤ T * D ^ (m + 1) := by positivity
  have hTA : 0 ≤ T * (A / T₀) := by positivity
  have hkey : T₀ ^ m * B ^ (m + 1) = A / T₀ := by
    rw [← hk]; field_simp; ring
  have hfin : ∀ Y : ℝ, 0 ≤ Y → R ≤ 2 * C₁ * Te * Y → Y ≤ 2 * P2 * S →
      R ≤ (2 + 4 * P2 * C₁) * S * Te := by
    intro Y hY hR hYS
    have := mul_le_mul_of_nonneg_left hYS (by positivity : 0 ≤ 2 * C₁ * Te)
    have h3 : 0 ≤ 2 * S * Te := by positivity
    nlinarith
  rcases lt_or_ge T₀ 1 with h1 | h1
  · -- tiny T₀: the trivial count
    have hAA : A ≤ A / T₀ := by rw [le_div_iff₀ hT₀]; nlinarith
    have hTS : T ≤ S := by nlinarith
    have : S ≤ S * Te := le_mul_of_one_le_right hS0 hTe1
    have : 0 ≤ 4 * P2 * C₁ * S * Te := by positivity
    nlinarith
  rcases le_or_gt T T₀ with h2 | h2
  · -- T ≤ T₀: apply directly
    have hR := hpiece T hT le_rfl
    have hTT : T / T = 1 := div_self (by linarith)
    rw [hTT] at hR
    have hpow : (T * B) ^ (m + 1) ≤ T * (A / T₀) := by
      rw [← hkey]
      have : T ^ m ≤ T₀ ^ m := pow_le_pow_left₀ (by linarith) h2 m
      calc (T * B) ^ (m + 1) = T * (T ^ m * B ^ (m + 1)) := by ring
        _ ≤ T * (T₀ ^ m * B ^ (m + 1)) := by gcongr
    apply hfin (A + T * D ^ (m + 1) + (T * B) ^ (m + 1)) (by positivity)
    · linarith
    · nlinarith
  · -- 1 ≤ T₀ < T: pieces of length max T₀ 2
    set L := max T₀ 2 with hL
    have hL2 : 2 ≤ L := le_max_right _ _
    have hLT : L ≤ T := max_le h2.le hT
    have hT₀L : T₀ ≤ L := le_max_left _ _
    have hL2T : L ≤ 2 * T₀ := max_le (by linarith) (by linarith)
    have hR := hpiece L hL2 hLT
    have hLpos : 0 < L := by linarith
    have e1 : T / L * (A + L * D ^ (m + 1) + (L * B) ^ (m + 1)) =
        T * (A / L) + T * D ^ (m + 1) + T * (L ^ m * B ^ (m + 1)) := by
      field_simp; ring
    have b1 : A / L ≤ A / T₀ := div_le_div_of_nonneg_left (by linarith) hT₀ hT₀L
    have b2 : L ^ m * B ^ (m + 1) ≤ P2 * (A / T₀) := by
      rw [← hkey]
      have : L ^ m ≤ (2 * T₀) ^ m := pow_le_pow_left₀ (by linarith) hL2T m
      calc L ^ m * B ^ (m + 1) ≤ (2 * T₀) ^ m * B ^ (m + 1) := by gcongr
        _ = _ := by rw [hP2]; ring
    have hY : T / L * (A + L * D ^ (m + 1) + (L * B) ^ (m + 1)) ≤ 2 * P2 * S := by
      rw [e1]
      have c1 : T * (A / L) ≤ T * (A / T₀) := mul_le_mul_of_nonneg_left b1 (by linarith)
      have c2 : T * (L ^ m * B ^ (m + 1)) ≤ T * (P2 * (A / T₀)) :=
        mul_le_mul_of_nonneg_left b2 (by linarith)
      have c3 : T * (P2 * (A / T₀)) = P2 * (T * (A / T₀)) := by ring
      have c4 : 0 ≤ (P2 - 1) * (T * (A / T₀)) := mul_nonneg (by linarith) hTA
      have c5 : 0 ≤ (2 * P2 - 1) * (T * D ^ (m + 1)) := mul_nonneg (by linarith) hTD
      have c6 : 0 ≤ 2 * P2 * A := by positivity
      rw [hS]
      nlinarith
    apply hfin _ (by positivity) _ hY
    calc R ≤ 2 * (T / L) * (C₁ * (A + L * D ^ (m + 1) + (L * B) ^ (m + 1)) * Te) := hR
      _ = _ := by ring

/-! ## The target -/
/-- The published statement `GuthMaynard.card_le_of_large_values_jutila`, verbatim. -/
theorem card_le_of_large_values_jutila (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re) → (∀ r q, |(s r).im - (s q).im| ≤ T) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im|) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-s r)‖) →
      let G : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
      (R : ℝ) ≤ C * (G * N / V ^ 2 +
        T * G ^ (3 - 1 / (k : ℝ)) * (N : ℝ) ^ (1 - 1 / (k : ℝ)) * V ^ (-6 + 2 / (k : ℝ)) +
        T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ k) * T ^ ε := by
  obtain ⟨C₀, hC₀⟩ := GuthMaynard.CitedLV.Jut.jutila12 ε hε k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨2 + 2 ^ (m + 1 + 1) * max C₀ 0, ?_⟩
  intro T hT N hN a V hV R s hre hdiam hsep hF G
  have hGdef : G = ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := rfl
  clear_value G
  set C₁ := max C₀ 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp only [CharP.cast_eq_zero]
    have : 0 ≤ T * G ^ (3 - 1 / ((m + 1 : ℕ) : ℝ)) * (N : ℝ) ^ (1 - 1 / ((m + 1 : ℕ) : ℝ)) *
        V ^ (-6 + 2 / ((m + 1 : ℕ) : ℝ)) := by
      have := Real.rpow_nonneg hG0 (3 - 1 / ((m + 1 : ℕ) : ℝ))
      have := Real.rpow_nonneg hNpos.le (1 - 1 / ((m + 1 : ℕ) : ℝ))
      have := Real.rpow_nonneg hV.le (-6 + 2 / ((m + 1 : ℕ) : ℝ))
      have : 0 ≤ T := by linarith
      positivity
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ T) ε
    positivity
  -- Cauchy–Schwarz: V² ≤ G N
  have hVG : V ^ 2 ≤ G * N := by
    have h1 : V ≤ ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ := by
      refine (hF ⟨0, hR⟩).trans ((norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_))
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (GuthMaynard.CitedLV.PartH.norm_natCast_cpow_neg_le n
          (by have := (mem_Ioc.1 hn).1; omega) _ (hre _))
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.Ioc N (2 * N)) (f := fun n => ‖a n‖)
    have hc : ((Finset.Ioc N (2 * N)).card : ℝ) = N := by
      rw [Nat.card_Ioc]; push_cast [show 2 * N - N = N by omega]; ring
    rw [hc] at h2
    rw [hGdef]
    nlinarith [pow_le_pow_left₀ hV.le h1 2]
  have hGpos : 0 < G := by
    by_contra h
    have : G = 0 := le_antisymm (not_lt.1 h) hG0
    rw [this] at hVG
    nlinarith
  set A := G * N / V ^ 2 with hAdef
  set B := G ^ 2 / V ^ 4 with hBdef
  set D := G ^ 4 * (N : ℝ) ^ 2 / V ^ 8 with hDdef
  have hA : 1 ≤ A := by rw [hAdef, le_div_iff₀ (by positivity)]; linarith
  have hB : 0 < B := by positivity
  have hD : 0 ≤ D := by positivity
  set T₀ := A ^ (1 / ((m + 1 : ℕ) : ℝ)) / B with hT₀def
  have hT₀ : 0 < T₀ := by positivity
  have hk' : T₀ ^ (m + 1) * B ^ (m + 1) = A := T0_pow A B (by linarith) hB m
  have hRT : (R : ℝ) ≤ T + 1 := by
    have := GuthMaynard.CitedLV.PartH.card_le_of_separated (univ : Finset (Fin R))
      (fun r => (s r).im) T (by linarith) (fun r _ q _ h => hsep r q h)
      (fun r _ q _ => hdiam r q)
    simpa using this
  have hpiece : ∀ L, 2 ≤ L → L ≤ T →
      (R : ℝ) ≤ 2 * (T / L) * (C₁ * (A + L * D ^ (m + 1) + (L * B) ^ (m + 1)) * T ^ ε) := by
    intro L hL2 hLT
    apply fiber_count (fun r => (s r).im) T L (by linarith) hLT hdiam
    intro P hP
    have hJ := jut_finset ε (m + 1) C₀ hC₀ L hL2 N hN a V hV s hre hsep hF P hP
    rw [← hGdef] at hJ
    have e : L * G ^ 2 / V ^ 4 = L * B := by rw [hBdef]; ring
    rw [e] at hJ
    have hY : 0 ≤ A + L * D ^ (m + 1) + (L * B) ^ (m + 1) := by
      have : 0 ≤ L := by linarith
      positivity
    have hLe : L ^ ε ≤ T ^ ε := Real.rpow_le_rpow (by linarith) hLT hε.le
    have hLe0 : 0 ≤ L ^ ε := Real.rpow_nonneg (by linarith) ε
    calc (P.card : ℝ) ≤ C₀ * (A + L * D ^ (m + 1) + (L * B) ^ (m + 1)) * L ^ ε := hJ
      _ ≤ C₁ * (A + L * D ^ (m + 1) + (L * B) ^ (m + 1)) * L ^ ε := by
          gcongr; exact le_max_left _ _
      _ ≤ _ := by gcongr
  have hmain := abstract_bound ε hε m C₁ hC₁ T hT A B D T₀ hA hB hD hT₀ hk' R hRT hpiece
  have hmid : T * G ^ (3 - 1 / ((m + 1 : ℕ) : ℝ)) * (N : ℝ) ^ (1 - 1 / ((m + 1 : ℕ) : ℝ)) *
      V ^ (-6 + 2 / ((m + 1 : ℕ) : ℝ)) = T * (A / T₀) := by
    have h := mid_eq G N V ((m + 1 : ℕ) : ℝ) hGpos hNpos hV
    rw [← hAdef, ← hBdef] at h
    have hA0 : 0 < A ^ (1 / ((m + 1 : ℕ) : ℝ)) := by positivity
    rw [hT₀def, div_div_eq_mul_div, ← h, mul_div_cancel_right₀ _ hA0.ne']
    ring
  rw [hmid]
  exact hmain

end
end GuthMaynard.CitedLV.Jut.PartS
end

section
namespace GuthMaynard.CitedLV.Jut
alias card_le_of_large_values_jutila := GuthMaynard.CitedLV.Jut.PartS.card_le_of_large_values_jutila

end GuthMaynard.CitedLV.Jut
end


theorem solution (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re) → (∀ r q, |(s r).im - (s q).im| ≤ T) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im|) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-s r)‖) →
      let G : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
      (R : ℝ) ≤ C * (G * N / V ^ 2 +
        T * G ^ (3 - 1 / (k : ℝ)) * (N : ℝ) ^ (1 - 1 / (k : ℝ)) * V ^ (-6 + 2 / (k : ℝ)) +
        T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ k) * T ^ ε :=
  GuthMaynard.CitedLV.Jut.card_le_of_large_values_jutila ε hε k hk
