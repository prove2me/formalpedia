-- Prove2me | solution 1 for KWSpectrum.Estimator.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T06:46:30.452087+00:00
-- url     : https://prove2.me/submissions/99a5009a-5f8e-475a-9abc-6c570413d199

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model
import Theorems.Thm_KWSpectrum_Estimator_eq_17
import Theorems.Thm_KWSpectrum_Estimator_eq_21
import Theorems.Thm_KWSpectrum_Estimator_dim_bound
import Theorems.Thm_KWSpectrum_Estimator_eq_2_4_projections

set_option autoImplicit false

/-! d631d197 KWSpectrum.Estimator.main_theorem -- method-of-types reduction library (relay 2).
Pure real / Young-diagram lemmas first; the quantum interface comes later. -/

namespace KWTypes

open Finset

/-- Bhattacharyya bound: `∑ √(s t) ≤ 1 - (s j - t j)^2 / 8` on the simplex. -/
theorem bc_le {d : ℕ} (s t : Fin d → ℝ) (hs : ∀ k, 0 ≤ s k) (ht : ∀ k, 0 ≤ t k)
    (hs1 : ∑ k, s k = 1) (ht1 : ∑ k, t k = 1) (j : Fin d) :
    ∑ k, Real.sqrt (s k * t k) ≤ 1 - (s j - t j) ^ 2 / 8 := by
  have hsq : ∀ k, Real.sqrt (s k * t k) = Real.sqrt (s k) * Real.sqrt (t k) := fun k =>
    Real.sqrt_mul (hs k) _
  have hss : ∀ k, Real.sqrt (s k) ^ 2 = s k := fun k => Real.sq_sqrt (hs k)
  have hts : ∀ k, Real.sqrt (t k) ^ 2 = t k := fun k => Real.sq_sqrt (ht k)
  -- 2 - 2 BC = ∑ (√s - √t)^2
  have hid : ∑ k, (Real.sqrt (s k) - Real.sqrt (t k)) ^ 2 =
      2 - 2 * ∑ k, Real.sqrt (s k * t k) := by
    have : ∀ k, (Real.sqrt (s k) - Real.sqrt (t k)) ^ 2 =
        s k + t k - 2 * Real.sqrt (s k * t k) := by
      intro k; rw [hsq k]; nlinarith [hss k, hts k]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hs1, ht1]
    ring
  have hterm : (Real.sqrt (s j) - Real.sqrt (t j)) ^ 2 ≤
      ∑ k, (Real.sqrt (s k) - Real.sqrt (t k)) ^ 2 :=
    Finset.single_le_sum (f := fun k => (Real.sqrt (s k) - Real.sqrt (t k)) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hsj1 : s j ≤ 1 := by
    rw [← hs1]; exact Finset.single_le_sum (fun k _ => hs k) (Finset.mem_univ j)
  have htj1 : t j ≤ 1 := by
    rw [← ht1]; exact Finset.single_le_sum (fun k _ => ht k) (Finset.mem_univ j)
  have hrs : Real.sqrt (s j) ≤ 1 := Real.sqrt_le_one.mpr hsj1
  have hrt : Real.sqrt (t j) ≤ 1 := Real.sqrt_le_one.mpr htj1
  have h0s := Real.sqrt_nonneg (s j)
  have h0t := Real.sqrt_nonneg (t j)
  have hfac : (s j - t j) ^ 2 =
      (Real.sqrt (s j) - Real.sqrt (t j)) ^ 2 * (Real.sqrt (s j) + Real.sqrt (t j)) ^ 2 := by
    have e : (Real.sqrt (s j) - Real.sqrt (t j)) * (Real.sqrt (s j) + Real.sqrt (t j)) =
        s j - t j := by linear_combination hss j - hts j
    rw [← e]; ring
  have hle4 : (Real.sqrt (s j) + Real.sqrt (t j)) ^ 2 ≤ 4 := by nlinarith
  have hA : (s j - t j) ^ 2 ≤ 4 * (Real.sqrt (s j) - Real.sqrt (t j)) ^ 2 := by
    rw [hfac]
    have := sq_nonneg (Real.sqrt (s j) - Real.sqrt (t j))
    nlinarith
  linarith

/-- Method-of-types AM-GM: for `t = n / N` (a type), `∏ s^n ≤ ∏ t^n · (∑ √(s t))^(2N)`. -/
theorem weight_le {d N : ℕ} (hN : 0 < N) (n : Fin d → ℕ) (hn : ∑ k, n k = N)
    (s : Fin d → ℝ) (hs : ∀ k, 0 ≤ s k) :
    ∏ k, s k ^ n k ≤
      (∏ k, ((n k : ℝ) / N) ^ n k) *
        (∑ k, Real.sqrt (s k * ((n k : ℝ) / N))) ^ (2 * N) := by
  set t : Fin d → ℝ := fun k => (n k : ℝ) / N with ht_def
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : ∀ k, 0 ≤ t k := fun k => div_nonneg (Nat.cast_nonneg _) hNr.le
  have ht1 : ∑ k, t k = 1 := by
    simp only [ht_def, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hNr.ne']; exact_mod_cast hn
  -- z k = √(s k) / √(t k)
  set z : Fin d → ℝ := fun k => Real.sqrt (s k) / Real.sqrt (t k) with hz_def
  have hz0 : ∀ k, 0 ≤ z k := fun k => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ) t z
    (fun k _ => ht0 k) ht1 (fun k _ => hz0 k)
  -- arithmetic side
  have harith : ∑ k, t k * z k ≤ ∑ k, Real.sqrt (s k * t k) := by
    apply Finset.sum_le_sum
    intro k _
    rcases (ht0 k).lt_or_eq with hpos | hzero
    · have hst : Real.sqrt (t k) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      have : t k * z k = Real.sqrt (s k * t k) := by
        simp only [hz_def]
        rw [Real.sqrt_mul (hs k)]
        field_simp
        try rw [Real.sq_sqrt (ht0 k)]
        try ring
      exact this.le
    · rw [← hzero]; simp
  -- geometric side, raised to the 2N
  have hgeom : ∀ k, (z k ^ t k) ^ (2 * N) * t k ^ n k = s k ^ n k := by
    intro k
    rw [← Real.rpow_natCast (z k ^ t k), ← Real.rpow_mul (hz0 k)]
    have hexp : t k * ((2 * N : ℕ) : ℝ) = ((2 * n k : ℕ) : ℝ) := by
      simp only [ht_def]; push_cast; field_simp
    rw [hexp, Real.rpow_natCast]
    rcases (ht0 k).lt_or_eq with hpos | hzero
    · simp only [hz_def]
      rw [pow_mul, div_pow, Real.sq_sqrt (hs k), Real.sq_sqrt (ht0 k), div_pow,
        div_mul_cancel₀]
      exact pow_ne_zero _ hpos.ne'
    · have hn0 : n k = 0 := by
        have : (n k : ℝ) / N = 0 := hzero.symm
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact_mod_cast h
        · exact absurd h hNr.ne'
      simp [hn0]
  have hprod_pow : (∏ k, z k ^ t k) ^ (2 * N) * ∏ k, t k ^ n k = ∏ k, s k ^ n k := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => hgeom k)
  have hG0 : 0 ≤ ∏ k, z k ^ t k :=
    Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (hz0 k) _)
  have hT0 : 0 ≤ ∏ k, t k ^ n k := Finset.prod_nonneg (fun k _ => pow_nonneg (ht0 k) _)
  have hle : (∏ k, z k ^ t k) ^ (2 * N) ≤ (∑ k, Real.sqrt (s k * t k)) ^ (2 * N) :=
    pow_le_pow_left₀ hG0 (hamgm.trans harith) _
  rw [← hprod_pow, mul_comm]
  exact mul_le_mul_of_nonneg_left hle hT0

/-- At most `(N+1)^d` Young diagrams with `N` boxes and at most `d` rows. -/
theorem card_partitions_le (d N : ℕ)
    [Fintype {μ : YoungDiagram // μ.card = N ∧ μ.colLen 0 ≤ d}] :
    Fintype.card {μ : YoungDiagram // μ.card = N ∧ μ.colLen 0 ≤ d} ≤ (N + 1) ^ d := by
  classical
  let F : {μ : YoungDiagram // μ.card = N ∧ μ.colLen 0 ≤ d} → (Fin d → Fin (N + 1)) :=
    fun Y j => ⟨Y.val.rowLen j.val, by
      have h1 : Y.val.rowLen j.val ≤ Y.val.card := by
        rw [YoungDiagram.rowLen_eq_card]
        exact Finset.card_le_card (fun c hc => (YoungDiagram.mem_row_iff.mp hc).1)
      omega⟩
  have hinj : Function.Injective F := by
    intro Y Y' h
    apply Subtype.ext
    have hrow : ∀ i, Y.val.rowLen i = Y'.val.rowLen i := by
      intro i
      by_cases hi : i < d
      · have := congrArg (fun f => (f ⟨i, hi⟩ : ℕ)) h
        simpa [F] using this
      · have hz : ∀ μ : YoungDiagram, μ.colLen 0 ≤ d → μ.rowLen i = 0 := by
          intro μ hμ
          by_contra hne
          have hmem : (i, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
          have := YoungDiagram.mem_iff_lt_colLen.mp hmem
          omega
        rw [hz _ Y.2.2, hz _ Y'.2.2]
    ext ⟨i, j⟩
    show (i, j) ∈ Y.val ↔ (i, j) ∈ Y'.val
    rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, hrow i]
  have := Fintype.card_le_of_injective F hinj
  simpa using this

/-- Row lengths of a diagram with at most `d` rows add up to its size. -/
theorem sum_rowLen (d : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    ∑ j : Fin d, μ.rowLen j.val = μ.cells.card := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i)]
  have hmaps : ∀ c ∈ μ.cells, c.1 ∈ Finset.range d := by
    intro c hc
    have hc' : (c.1, c.2) ∈ μ := hc
    have h1 := YoungDiagram.mem_iff_lt_colLen.mp hc'
    have h2 := μ.colLen_anti 0 c.2 (Nat.zero_le _)
    rw [Finset.mem_range]; omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [YoungDiagram.rowLen_eq_card]
  rfl

/-- Far-from-type bound: if `f ≤ c D s^n` and `D t^n ≤ 1` (with `t = n/N`), then
`f ≤ c (1 - (s j - t j)^2/8)^(2N)`. -/
theorem far_bound {d N : ℕ} (hN : 0 < N) (n : Fin d → ℕ) (hn : ∑ k, n k = N)
    (s : Fin d → ℝ) (hs : ∀ k, 0 ≤ s k) (hs1 : ∑ k, s k = 1)
    (D c f : ℝ) (hD0 : 0 ≤ D) (hc : 0 ≤ c)
    (hup : f ≤ c * D * ∏ k, s k ^ n k) (hD : D * ∏ k, ((n k : ℝ) / N) ^ n k ≤ 1)
    (j : Fin d) :
    f ≤ c * (1 - (s j - (n j : ℝ) / N) ^ 2 / 8) ^ (2 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : ∀ k, 0 ≤ (n k : ℝ) / N := fun k => div_nonneg (Nat.cast_nonneg _) hNr.le
  have ht1 : ∑ k, (n k : ℝ) / N = 1 := by
    rw [← Finset.sum_div, div_eq_one_iff_eq hNr.ne']; exact_mod_cast hn
  have hw := weight_le hN n hn s hs
  have hbc := bc_le s (fun k => (n k : ℝ) / N) hs ht0 hs1 ht1 j
  have hB0 : 0 ≤ ∑ k, Real.sqrt (s k * ((n k : ℝ) / N)) :=
    Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _)
  have hpow : (∑ k, Real.sqrt (s k * ((n k : ℝ) / N))) ^ (2 * N) ≤
      (1 - (s j - (n j : ℝ) / N) ^ 2 / 8) ^ (2 * N) := pow_le_pow_left₀ hB0 hbc _
  have hBp : 0 ≤ (∑ k, Real.sqrt (s k * ((n k : ℝ) / N))) ^ (2 * N) := pow_nonneg hB0 _
  have hT0 : 0 ≤ ∏ k, ((n k : ℝ) / N) ^ n k := Finset.prod_nonneg (fun k _ => pow_nonneg (ht0 k) _)
  calc f ≤ c * D * ∏ k, s k ^ n k := hup
    _ ≤ c * D * ((∏ k, ((n k : ℝ) / N) ^ n k) *
          (∑ k, Real.sqrt (s k * ((n k : ℝ) / N))) ^ (2 * N)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hc hD0)
    _ = c * ((D * ∏ k, ((n k : ℝ) / N) ^ n k) *
          (∑ k, Real.sqrt (s k * ((n k : ℝ) / N))) ^ (2 * N)) := by ring
    _ ≤ c * (1 * (∑ k, Real.sqrt (s k * ((n k : ℝ) / N))) ^ (2 * N)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact mul_le_mul_of_nonneg_right hD hBp
    _ ≤ c * (1 - (s j - (n j : ℝ) / N) ^ 2 / 8) ^ (2 * N) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hc

end KWTypes

namespace KWSpectrum.Estimator.Red

open QAlgorithms QAlgorithms.Schur KWSpectrum.Estimator

/-- Child statement eq_17 (as a hypothesis type). -/
def Eq17 : Prop := ∀ {d N : ℕ} (Y : Partition d N) (ρ : Matrix (Fin d) (Fin d) ℂ),
    (piKron N ρ * isotypicProjector Y).trace =
      LinearMap.trace ℂ (schurModule Y) (polynomialRepresentation Y ρ) *
        (Module.finrank ℂ (spechtSpace Y) : ℂ)

/-- Child statement eq_21. -/
def Eq21 : Prop := ∀ {d N : ℕ} (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ)
    (_hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (_hanti : Antitone r)
    (_hnn : ∀ j, 0 ≤ r j),
    let χ : ℂ := LinearMap.trace ℂ (schurModule Y)
      (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U))
    χ.im = 0 ∧
    ∏ i : Fin d, r i ^ Y.val.rowLen i.val ≤ χ.re ∧
    χ.re ≤ (Module.finrank ℂ (schurModule Y) : ℝ) * ∏ i : Fin d, r i ^ Y.val.rowLen i.val

/-- Child statement dim_bound. -/
def DimBound : Prop := ∀ {d N : ℕ} (Y : Partition d N),
    Module.finrank ℂ (schurModule Y) ≤ (N + 1) ^ (d * (d - 1) / 2)

/-- The completeness conjunct of eq_2_4_projections. -/
def Complete : Prop := ∀ {d N : ℕ} (_Y : Partition d N),
    (∑ Y' : Partition d N, isotypicProjector Y') = 1

/-- Spectral weight `r^Y`. -/
noncomputable def wt {d N : ℕ} (r : Fin d → ℝ) (Y : Partition d N) : ℝ :=
  ∏ i : Fin d, r i ^ Y.val.rowLen i.val

/-- Specht dimension as a real. -/
noncomputable def dimS {d N : ℕ} (Y : Partition d N) : ℝ :=
  (Module.finrank ℂ (spechtSpace Y) : ℝ)

theorem frame_bounds (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) {d N : ℕ} (Y : Partition d N)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) :
    dimS Y * wt r Y ≤ frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ∧
    frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ≤
      ((N + 1 : ℕ) : ℝ) ^ (d * (d - 1) / 2) * dimS Y * wt r Y := by
  obtain ⟨hanti, hnn, -⟩ := hr
  have h := h21 Y U hU r hanti hnn
  simp only at h
  obtain ⟨-, hlo, hhi⟩ := h
  have hfp : frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y =
      dimS Y * (LinearMap.trace ℂ (schurModule Y) (polynomialRepresentation Y
        (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U))).re := by
    unfold frameProb effectProb
    rw [Matrix.trace_mul_comm, h17 Y]
    simp only [dimS, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    ring
  have hD0 : 0 ≤ dimS Y := Nat.cast_nonneg _
  have hw0 : 0 ≤ wt r Y := Finset.prod_nonneg (fun i _ => pow_nonneg (hnn i) _)
  have hdimY : (Module.finrank ℂ (schurModule Y) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ (d * (d - 1) / 2) := by
    exact_mod_cast hdim Y
  rw [hfp]
  refine ⟨mul_le_mul_of_nonneg_left hlo hD0, ?_⟩
  calc dimS Y * _ ≤ dimS Y * ((Module.finrank ℂ (schurModule Y) : ℝ) * wt r Y) :=
        mul_le_mul_of_nonneg_left hhi hD0
    _ ≤ dimS Y * (((N + 1 : ℕ) : ℝ) ^ (d * (d - 1) / 2) * wt r Y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdimY hw0) hD0
    _ = _ := by ring

theorem trace_piKron {d : ℕ} (N : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (piKron N ρ).trace = ρ.trace ^ N := by
  unfold piKron Matrix.trace
  simp only [Matrix.diag, Matrix.of_apply]
  rw [← Fin.prod_const N (∑ a, ρ a a), Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]

theorem frame_sum (hc : Complete) {d N : ℕ} (hpart : Nonempty (Partition d N))
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) :
    ∑ Y : Partition d N, frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y = 1 := by
  obtain ⟨Y0⟩ := hpart
  have hsum : ∑ Y : Partition d N, frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y =
      ((∑ Y : Partition d N, isotypicProjector Y) *
        piKron N (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U)).trace.re := by
    simp only [frameProb, effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rw [hsum, hc Y0, one_mul, trace_piKron]
  have htr : (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U).trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mul,
      Matrix.trace_diagonal]
    have := hr.2.2
    exact_mod_cast this
  rw [htr, one_pow, Complex.one_re]

theorem youngFrac_mem {d N : ℕ} (hN : 0 < N) (Y : Partition d N) : youngFrac Y ∈ SpectrumSet d := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simp only [youngFrac]
    apply div_le_div_of_nonneg_right _ hNr.le
    exact_mod_cast Y.val.rowLen_anti i.val j.val hij
  · intro j; exact div_nonneg (Nat.cast_nonneg _) hNr.le
  · simp only [youngFrac]
    rw [← Finset.sum_div, div_eq_one_iff_eq hNr.ne']
    have h := KWTypes.sum_rowLen d Y.val Y.2.2
    have hc : Y.val.cells.card = N := Y.2.1
    rw [hc] at h
    exact_mod_cast h

theorem frameProb_nonneg (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) {d N : ℕ} (Y : Partition d N)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) :
    0 ≤ frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y :=
  le_trans (mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => pow_nonneg (hr.2.1 i) _)))
    (frame_bounds h17 h21 hdim Y U hU r hr).1

theorem frameProb_le_one (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d N : ℕ}
    (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) :
    frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ≤ 1 := by
  rw [← frame_sum hc ⟨Y⟩ U hU r hr]
  exact Finset.single_le_sum (f := fun Y' => frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) *
    star U) Y') (fun Y' _ => frameProb_nonneg h17 h21 hdim Y' U hU r hr) (Finset.mem_univ Y)

/-- Specht dimension upper bound `D(Y) (Y/N)^Y ≤ 1`, from `frameProb ≤ 1` at `ρ = diag(Y/N)`. -/
theorem dimS_wt_le_one (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d N : ℕ}
    (hN : 0 < N) (Y : Partition d N) : dimS Y * wt (youngFrac Y) Y ≤ 1 := by
  have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := one_mem _
  exact (frame_bounds h17 h21 hdim Y 1 h1 _ (youngFrac_mem hN Y)).1.trans
    (frameProb_le_one h17 h21 hdim hc Y 1 h1 _ (youngFrac_mem hN Y))

end KWSpectrum.Estimator.Red

namespace KWCore

open Filter Topology
open scoped ENNReal

theorem lr_le {a : ℝ≥0∞} {N : ℕ} (hN : 0 < N) {x : ℝ}
    (h : a ≤ ENNReal.ofReal (Real.exp (N * x))) :
    (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log a ≤ (x : EReal) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ENNReal.log a ≤ ((N * x : ℝ) : EReal) := by
    have := ENNReal.log_monotone h
    rwa [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at this
  calc (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log a
      ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) * ((N * x : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.2 (inv_nonneg.2 hNr.le))
    _ = (x : EReal) := by
        rw [← EReal.coe_mul, show (N : ℝ)⁻¹ * (N * x) = x by field_simp]

theorem lr_ge {a : ℝ≥0∞} {N : ℕ} (hN : 0 < N) {x : ℝ}
    (h : ENNReal.ofReal (Real.exp (N * x)) ≤ a) :
    (x : EReal) ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log a := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((N * x : ℝ) : EReal) ≤ ENNReal.log a := by
    have := ENNReal.log_monotone h
    rwa [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at this
  calc (x : EReal) = (((N : ℝ)⁻¹ : ℝ) : EReal) * ((N * x : ℝ) : EReal) := by
        rw [← EReal.coe_mul, show (N : ℝ)⁻¹ * (N * x) = x by field_simp]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.2 (inv_nonneg.2 hNr.le))

theorem log_succ_div_tendsto :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / N) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  refine h.congr (fun N => ?_)
  simp only [Function.comp_apply, pow_one, one_mul, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

theorem klog_eventually_lt (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (k : ℝ) * (Real.log ((N : ℝ) + 1) / N) < ε := by
  have hl := log_succ_div_tendsto.const_mul (k : ℝ)
  rw [mul_zero] at hl
  exact hl.eventually (gt_mem_nhds hε)

theorem poly_geom_tendsto (k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ k * q ^ N) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
    (show |q| < 1 by rwa [abs_of_nonneg hq0])).const_mul (2 ^ k)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (by positivity)
    (pow_nonneg hq0 N)) ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc ((N : ℝ) + 1) ^ k * q ^ N ≤ (2 * N) ^ k * q ^ N :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) k)
          (pow_nonneg hq0 N)
    _ = 2 ^ k * ((N : ℝ) ^ k * q ^ N) := by rw [mul_pow]; ring

theorem exp_poly_eq {N : ℕ} (hN : 0 < N) (k : ℕ) (m : ℝ) :
    Real.exp (N * ((k : ℝ) * (Real.log ((N : ℝ) + 1) / N) - m)) =
      ((N : ℝ) + 1) ^ k * Real.exp (-(N * m)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) * ((k : ℝ) * (Real.log ((N : ℝ) + 1) / N) - m) =
      Real.log (((N : ℝ) + 1) ^ k) + -(N * m) := by
    rw [Real.log_pow]; field_simp; ring
  rw [e, Real.exp_add, Real.exp_log (by positivity)]

theorem limsup_le_of_bound (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ)
    (h : ∀ᶠ N : ℕ in atTop, a N ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ k * Real.exp (-(N * m)))) :
    limsup (fun N : ℕ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (a N)) atTop ≤
      ((-m : ℝ) : EReal) := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  induction c using EReal.rec with
  | bot => exact absurd hc not_lt_bot
  | top => exact le_top
  | coe c =>
    have hc' : -m < c := by exact_mod_cast hc
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [h, klog_eventually_lt k (show 0 < c + m by linarith),
      eventually_ge_atTop 1] with N hN hlt hN1
    refine (lr_le hN1 (x := (k : ℝ) * (Real.log ((N : ℝ) + 1) / N) - m) ?_).trans ?_
    · rw [exp_poly_eq hN1]; exact hN
    · exact_mod_cast (show (k : ℝ) * (Real.log ((N : ℝ) + 1) / N) - m ≤ c by linarith)

theorem le_liminf_of_bound (a : ℕ → ℝ≥0∞) (k : ℕ) (L : ℝ)
    (h : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-(N * (L + ε))) / ((N : ℝ) + 1) ^ k) ≤ a N) :
    ((-L : ℝ) : EReal) ≤
      liminf (fun N : ℕ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (a N)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  induction c using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hc not_top_lt
  | coe c =>
    have hc' : c < -L := by exact_mod_cast hc
    set ε := (-L - c) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [h ε hε, klog_eventually_lt k hε, eventually_ge_atTop 1] with N hN hlt hN1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    refine le_trans ?_ (lr_ge hN1 (x := -(L + ε) - (k : ℝ) * (Real.log ((N : ℝ) + 1) / N)) ?_)
    · exact_mod_cast (show c ≤ -(L + ε) - (k : ℝ) * (Real.log ((N : ℝ) + 1) / N) by
        rw [hεdef] at hlt ⊢; linarith)
    · refine le_trans (le_of_eq ?_) hN
      congr 1
      have e : (N : ℝ) * (-(L + ε) - (k : ℝ) * (Real.log ((N : ℝ) + 1) / N)) =
          -(N * (L + ε)) - Real.log (((N : ℝ) + 1) ^ k) := by
        rw [Real.log_pow]; field_simp
      rw [e, Real.exp_sub, Real.exp_log (by positivity)]

theorem wt_ratio {d : ℕ} (r t : Fin d → ℝ) (n : Fin d → ℕ)
    (hpos : ∀ j, n j ≠ 0 → 0 < t j ∧ 0 < r j) :
    ∏ j, r j ^ n j =
      (∏ j, t j ^ n j) * Real.exp (-∑ j, (n j : ℝ) * Real.log (t j / r j)) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : n j = 0
  · simp [hj]
  · obtain ⟨ht, hr⟩ := hpos j hj
    have e : -((n j : ℝ) * Real.log (t j / r j)) =
        (n j : ℝ) * (Real.log (r j) - Real.log (t j)) := by
      rw [Real.log_div ht.ne' hr.ne']; ring
    have ht' := ht.ne'
    rw [e, Real.exp_nat_mul, Real.exp_sub, Real.exp_log hr, Real.exp_log ht, div_pow]
    field_simp

end KWCore

namespace KWSpectrum.Estimator.Red

open QAlgorithms QAlgorithms.Schur KWSpectrum.Estimator Filter Topology
open scoped ENNReal

open Classical in
theorem outcomeProb_eq {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) (Δ : Set (Fin d → ℝ)) :
    outcomeProb ρ N Δ =
      ENNReal.ofReal (∑ Y : Partition d N with youngFrac Y ∈ Δ, frameProb ρ Y) := by
  unfold outcomeProb estimatorEffect frameProb effectProb
  congr 1
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem mem_le_one {d : ℕ} {s : Fin d → ℝ} (hs : s ∈ SpectrumSet d) (j : Fin d) : s j ≤ 1 := by
  rw [← hs.2.2]; exact Finset.single_le_sum (fun k _ => hs.2.1 k) (Finset.mem_univ j)

theorem rowLen_sum {d N : ℕ} (Y : Partition d N) : ∑ j : Fin d, Y.val.rowLen j.val = N :=
  (KWTypes.sum_rowLen d Y.val Y.2.2).trans Y.2.1

noncomputable def cN (d N : ℕ) : ℝ := ((N + 1 : ℕ) : ℝ) ^ (d * (d - 1) / 2)

theorem cN_pos (d N : ℕ) : 0 < cN d N := by unfold cN; positivity

theorem card_le (d N : ℕ) : (Fintype.card (Partition d N) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ d := by
  exact_mod_cast KWTypes.card_partitions_le d N

theorem far_frame (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d N : ℕ}
    (hN : 0 < N) (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (j : Fin d) :
    frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ≤
      cN d N * (1 - (r j - youngFrac Y j) ^ 2 / 8) ^ (2 * N) :=
  KWTypes.far_bound hN (fun k => Y.val.rowLen k.val) (rowLen_sum Y) r hr.2.1 hr.2.2
    (dimS Y) (cN d N) _ (Nat.cast_nonneg _) (cN_pos d N).le
    (frame_bounds h17 h21 hdim Y U hU r hr).2 (dimS_wt_le_one h17 h21 hdim hc hN Y) j

theorem far_mass_le (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d N : ℕ}
    (hN : 0 < N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ Y : Partition d N with ∃ j, ε ≤ |r j - youngFrac Y j|,
        frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ≤
      ((N + 1 : ℕ) : ℝ) ^ d * cN d N * ((1 - ε ^ 2 / 8) ^ 2) ^ N := by
  have hq : 0 ≤ cN d N * ((1 - ε ^ 2 / 8) ^ 2) ^ N :=
    mul_nonneg (cN_pos d N).le (pow_nonneg (sq_nonneg _) _)
  calc _ ≤ ∑ Y : Partition d N with ∃ j, ε ≤ |r j - youngFrac Y j|,
          cN d N * ((1 - ε ^ 2 / 8) ^ 2) ^ N := by
        refine Finset.sum_le_sum fun Y hY => ?_
        obtain ⟨j, hj⟩ := (Finset.mem_filter.1 hY).2
        refine (far_frame h17 h21 hdim hc hN Y U hU r hr j).trans ?_
        rw [← pow_mul]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) (cN_pos d N).le
        · have h1 := mem_le_one hr j
          have h2 := mem_le_one (youngFrac_mem hN Y) j
          have h3 := hr.2.1 j
          have h4 := (youngFrac_mem hN Y).2.1 j
          nlinarith
        · have : ε ^ 2 ≤ (r j - youngFrac Y j) ^ 2 := by
            rw [← sq_abs (r j - _)]; exact pow_le_pow_left₀ hε.le hj 2
          linarith
    _ ≤ ∑ _Y : Partition d N, cN d N * ((1 - ε ^ 2 / 8) ^ 2) ^ N :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hq)
    _ = (Fintype.card (Partition d N) : ℝ) * (cN d N * ((1 - ε ^ 2 / 8) ^ 2) ^ N) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ d * (cN d N * ((1 - ε ^ 2 / 8) ^ 2) ^ N) :=
        mul_le_mul_of_nonneg_right (card_le d N) hq
    _ = _ := by ring

theorem far_mass_tendsto (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun N : ℕ => ∑ Y : Partition d N with ∃ j, ε ≤ |r j - youngFrac Y j|,
        frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y) atTop (𝓝 0) := by
  have hx : 0 < ε ^ 2 / 8 := by positivity
  have hx1 : ε ^ 2 / 8 < 1 := by nlinarith
  have hq0 : 0 ≤ (1 - ε ^ 2 / 8) ^ 2 := sq_nonneg _
  have hq1 : (1 - ε ^ 2 / 8) ^ 2 < 1 := by nlinarith
  have hlim := (KWCore.poly_geom_tendsto (d + d * (d - 1) / 2) hq0 hq1).congr
    (fun N : ℕ => show ((N : ℝ) + 1) ^ (d + d * (d - 1) / 2) * ((1 - ε ^ 2 / 8) ^ 2) ^ N =
      ((N + 1 : ℕ) : ℝ) ^ d * cN d N * ((1 - ε ^ 2 / 8) ^ 2) ^ N by
        unfold cN; push_cast; ring)
  refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun Y _ =>
    frameProb_nonneg h17 h21 hdim Y U hU r hr) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact far_mass_le h17 h21 hdim hc hN U hU r hr hε

theorem frame_le_rate (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d N : ℕ}
    (hN : 0 < N) (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (m : ℝ)
    (hm : (m : EReal) ≤ rate r (youngFrac Y)) :
    frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ≤
      cN d N * Real.exp (-(N * m)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ≤
      cN d N * dimS Y * wt r Y := (frame_bounds h17 h21 hdim Y U hU r hr).2
  have hD := dimS_wt_le_one h17 h21 hdim hc hN Y
  have hc0 := cN_pos d N
  by_cases h : ∃ j, 0 < youngFrac Y j ∧ r j = 0
  · obtain ⟨j, hj, hrj⟩ := h
    have hn : Y.val.rowLen j.val ≠ 0 := by
      intro h0; simp [youngFrac, h0] at hj
    have hw : wt r Y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hrj, zero_pow hn])
    rw [hw, mul_zero] at hb
    exact hb.trans (mul_pos hc0 (Real.exp_pos _)).le
  · have hrate : rate r (youngFrac Y) =
        ((∑ j, youngFrac Y j * Real.log (youngFrac Y j / r j) : ℝ) : EReal) := by
      unfold rate; rw [if_neg h]
    rw [hrate] at hm
    have hm' : m ≤ ∑ j, youngFrac Y j * Real.log (youngFrac Y j / r j) := by exact_mod_cast hm
    have hw := KWCore.wt_ratio r (youngFrac Y) (fun k => Y.val.rowLen k.val) (fun j hj => by
      have ht : 0 < youngFrac Y j := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hj) hNr
      exact ⟨ht, lt_of_le_of_ne (hr.2.1 j) (fun h0 => h ⟨j, ht, h0.symm⟩)⟩)
    beta_reduce at hw
    have hsum : ∑ j, ((Y.val.rowLen j.val : ℕ) : ℝ) * Real.log (youngFrac Y j / r j) =
        N * ∑ j, youngFrac Y j * Real.log (youngFrac Y j / r j) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      simp only [youngFrac]; field_simp
    calc frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y
        ≤ cN d N * dimS Y * wt r Y := hb
      _ = cN d N * (dimS Y * wt (youngFrac Y) Y) *
            Real.exp (-(N * ∑ j, youngFrac Y j * Real.log (youngFrac Y j / r j))) := by
          unfold wt; rw [hw, ← hsum]; ring
      _ ≤ cN d N * 1 * Real.exp (-(N * m)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hD hc0.le)
            (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hm' hNr.le)))
            (Real.exp_pos _).le (by linarith)
      _ = _ := by ring

open Classical in
theorem outcome_le (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d N : ℕ}
    (hN : 0 < N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    (Δ : Set (Fin d → ℝ)) (m : ℝ) (hm : ∀ s ∈ Δ, (m : EReal) ≤ rate r s) :
    outcomeProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) N Δ ≤
      ENNReal.ofReal (((N : ℝ) + 1) ^ (d + d * (d - 1) / 2) * Real.exp (-(N * m))) := by
  rw [outcomeProb_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq : 0 ≤ cN d N * Real.exp (-(N * m)) := (mul_pos (cN_pos d N) (Real.exp_pos _)).le
  calc _ ≤ ∑ Y : Partition d N with youngFrac Y ∈ Δ, cN d N * Real.exp (-(N * m)) :=
        Finset.sum_le_sum fun Y hY => frame_le_rate h17 h21 hdim hc hN Y U hU r hr m
          (hm _ (Finset.mem_filter.1 hY).2)
    _ ≤ ∑ _Y : Partition d N, cN d N * Real.exp (-(N * m)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hq)
    _ = (Fintype.card (Partition d N) : ℝ) * (cN d N * Real.exp (-(N * m))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ d * (cN d N * Real.exp (-(N * m))) :=
        mul_le_mul_of_nonneg_right (card_le d N) hq
    _ = _ := by unfold cN; push_cast; ring

end KWSpectrum.Estimator.Red

namespace KWSpectrum.Estimator.Red

open QAlgorithms QAlgorithms.Schur KWSpectrum.Estimator Filter Topology
open scoped ENNReal

/-- The one-row Young diagram with `N` boxes. -/
def rowDiagram (N : ℕ) : YoungDiagram where
  cells := (Finset.range N).map ⟨fun j => (0, j), fun a b h => (Prod.mk.inj h).2⟩
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.mem_coe, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk] at ha ⊢
    obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨b.2, lt_of_le_of_lt hba.2 hj, Prod.ext (Nat.le_zero.1 hba.1).symm rfl⟩

theorem partition_nonempty {d N : ℕ} (hd : 1 ≤ d) : Nonempty (Partition d N) := by
  refine ⟨⟨rowDiagram N, ?_, ?_⟩⟩
  · show (rowDiagram N).cells.card = N
    simp [rowDiagram]
  · refine le_trans ?_ hd
    by_contra h
    push_neg at h
    have hm := (YoungDiagram.mem_iff_lt_colLen (μ := rowDiagram N) (i := 1) (j := 0)).2 h
    change (1, 0) ∈ (Finset.range N).map
      ⟨fun j => ((0 : ℕ), j), fun a b h => (Prod.mk.inj h).2⟩ at hm
    rw [Finset.mem_map] at hm
    obtain ⟨a, _, ha⟩ := hm
    exact absurd (show (0 : ℕ) = 1 from congrArg Prod.fst ha) (by decide)

theorem near_exists (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (s : Fin d → ℝ) (hs : s ∈ SpectrumSet d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∃ Y : Partition d N, (∀ j, |s j - youngFrac Y j| < ε) ∧
      (∀ j, Y.val.rowLen j.val ≠ 0 → 0 < s j) ∧
      1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
        frameProb (1 * Matrix.diagonal (fun j => (s j : ℂ)) * star (1 : Matrix (Fin d) (Fin d) ℂ)) Y := by
  have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := one_mem _
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; have := hs.2.2; simp at this
    · exact h0
  have hfar := (far_mass_tendsto h17 h21 hdim hc 1 h1 s hs hε hε1).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hfar, eventually_ge_atTop 1] with N hN hN1
  set ρs := 1 * Matrix.diagonal (fun j => (s j : ℂ)) * star (1 : Matrix (Fin d) (Fin d) ℂ)
    with hρs
  have htot : ∑ Y : Partition d N, frameProb ρs Y = 1 :=
    frame_sum hc (partition_nonempty hd) 1 h1 s hs
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun Y : Partition d N => ∃ j, ε ≤ |s j - youngFrac Y j|) (fun Y => frameProb ρs Y)
  beta_reduce at hsplit
  by_contra hcon
  push_neg at hcon
  have hpos : (0 : ℝ) < 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d) := by positivity
  have hnear : ∑ Y : Partition d N with ¬ ∃ j, ε ≤ |s j - youngFrac Y j|, frameProb ρs Y ≤ 1 / 2 := by
    calc _ ≤ ∑ _Y : Partition d N with ¬ ∃ j, ε ≤ |s j - youngFrac _Y j|,
            1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d) := by
          refine Finset.sum_le_sum fun Y hY => ?_
          have hY' : ∀ j, |s j - youngFrac Y j| < ε := by
            have := (Finset.mem_filter.1 hY).2
            push_neg at this
            exact this
          by_cases hsupp : ∀ j, Y.val.rowLen j.val ≠ 0 → 0 < s j
          · exact (hcon Y hY' hsupp).le
          · push_neg at hsupp
            obtain ⟨j, hj, hsj⟩ := hsupp
            have hs0 : s j = 0 := le_antisymm hsj (hs.2.1 j)
            have hw : wt s Y = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hs0, zero_pow hj])
            have hb := (frame_bounds h17 h21 hdim Y 1 h1 s hs).2
            rw [hw, mul_zero] at hb
            exact hb.trans hpos.le
      _ ≤ ∑ _Y : Partition d N, 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => hpos.le)
      _ = (Fintype.card (Partition d N) : ℝ) * (1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((N + 1 : ℕ) : ℝ) ^ d * (1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d)) :=
          mul_le_mul_of_nonneg_right (card_le d N) hpos.le
      _ = 1 / 2 := by field_simp
  linarith [hsplit, htot, hN, hnear]

open Classical in
theorem outcome_ge (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    (Δ : Set (Fin d → ℝ)) (s : Fin d → ℝ) (hsΔ : s ∈ relInterior Δ)
    (hfin : ¬ ∃ j, 0 < s j ∧ r j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-(N * ((∑ j, s j * Real.log (s j / r j)) + ε))) /
        ((N : ℝ) + 1) ^ (d + d * (d - 1) / 2 + 1)) ≤
      outcomeProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) N Δ := by
  obtain ⟨x, hx, hxs⟩ := hsΔ
  have hs : s ∈ SpectrumSet d := hxs ▸ x.2
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hC : 0 < ∑ j, |Real.log (s j / r j)| + 1 := by positivity
  obtain ⟨η, hη, hη1, hηδ, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η < δ ∧
      η * (∑ j, |Real.log (s j / r j)| + 1) ≤ ε := by
    refine ⟨min (δ / 2) (min 1 (ε / (∑ j, |Real.log (s j / r j)| + 1))),
      lt_min (by linarith) (lt_min one_pos (div_pos hε hC)),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_left _ _).trans_lt (by linarith), ?_⟩
    calc _ ≤ ε / (∑ j, |Real.log (s j / r j)| + 1) * (∑ j, |Real.log (s j / r j)| + 1) :=
          mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hC.le
      _ = ε := div_mul_cancel₀ ε hC.ne'
  filter_upwards [near_exists h17 h21 hdim hc s hs hη hη1, eventually_ge_atTop 1] with N hY hN1
  obtain ⟨Y, hnear, hsupp, hfs⟩ := hY
  have hN : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := one_mem _
  have htΔ : youngFrac Y ∈ Δ := by
    have hmem : (⟨youngFrac Y, youngFrac_mem hN Y⟩ : SpectrumSet d) ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, dist_pi_lt_iff hδ]
      intro j
      have := hnear j
      rw [← hxs] at this
      rw [Real.dist_eq, abs_sub_comm]
      exact this.trans hηδ
    exact hball hmem
  have hbr := (frame_bounds h17 h21 hdim Y U hU r hr).1
  have hbs := (frame_bounds h17 h21 hdim Y 1 h1 s hs).2
  have hw := KWCore.wt_ratio r s (fun k => Y.val.rowLen k.val) (fun j hj =>
      ⟨hsupp j hj, lt_of_le_of_ne (hr.2.1 j) (fun h0 => hfin ⟨j, hsupp j hj, h0.symm⟩)⟩)
  beta_reduce at hw
  have hexp : ∑ j, ((Y.val.rowLen j.val : ℕ) : ℝ) * Real.log (s j / r j) ≤
      N * ((∑ j, s j * Real.log (s j / r j)) + ε) := by
    have e1 : ∑ j, ((Y.val.rowLen j.val : ℕ) : ℝ) * Real.log (s j / r j) =
        N * ∑ j, youngFrac Y j * Real.log (s j / r j) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      simp only [youngFrac]; field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ hNr.le
    have e2 : ∑ j, youngFrac Y j * Real.log (s j / r j) = ∑ j, s j * Real.log (s j / r j) +
        ∑ j, (youngFrac Y j - s j) * Real.log (s j / r j) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    have e3 : ∑ j, (youngFrac Y j - s j) * Real.log (s j / r j) ≤
        η * ∑ j, |Real.log (s j / r j)| := by
      rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _ => ?_
      calc (youngFrac Y j - s j) * Real.log (s j / r j)
          ≤ |(youngFrac Y j - s j) * Real.log (s j / r j)| := le_abs_self _
        _ = |youngFrac Y j - s j| * |Real.log (s j / r j)| := abs_mul _ _
        _ ≤ η * |Real.log (s j / r j)| :=
          mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact (hnear j).le) (abs_nonneg _)
    have e4 : η * ∑ j, |Real.log (s j / r j)| ≤ η * (∑ j, |Real.log (s j / r j)| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hη.le
    linarith
  rw [outcomeProb_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hfr_le : frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y ≤
      ∑ Y' : Partition d N with youngFrac Y' ∈ Δ,
        frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y' :=
    Finset.single_le_sum (f := fun Y' => frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) *
      star U) Y') (fun Y' _ => frameProb_nonneg h17 h21 hdim Y' U hU r hr)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, htΔ⟩)
  refine le_trans ?_ (hbr.trans hfr_le)
  have hDpos : 0 < 2 * ((N + 1 : ℕ) : ℝ) ^ d * cN d N := mul_pos (by positivity) (cN_pos d N)
  have hDs : 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d * cN d N) ≤ dimS Y * wt s Y := by
    have hfs' := hfs.trans hbs
    unfold cN at hDpos ⊢
    rw [div_le_iff₀ hDpos]
    rw [div_le_iff₀ (by positivity)] at hfs'
    exact hfs'.trans (le_of_eq (by ring))
  have hwr : dimS Y * wt r Y = dimS Y * wt s Y *
      Real.exp (-∑ j, ((Y.val.rowLen j.val : ℕ) : ℝ) * Real.log (s j / r j)) := by
    unfold wt; rw [hw]; ring
  rw [hwr]
  have hpoly : 2 * ((N + 1 : ℕ) : ℝ) ^ d * cN d N ≤ ((N : ℝ) + 1) ^ (d + d * (d - 1) / 2 + 1) := by
    unfold cN; push_cast
    rw [pow_add, pow_add, pow_one]
    have h2 : (2 : ℝ) ≤ (N : ℝ) + 1 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      linarith
    have hA := pow_pos (show (0 : ℝ) < N + 1 by positivity) d
    have hB := pow_pos (show (0 : ℝ) < N + 1 by positivity) (d * (d - 1) / 2)
    nlinarith [mul_nonneg (mul_nonneg hA.le hB.le) (sub_nonneg.2 h2)]
  calc Real.exp (-(N * ((∑ j, s j * Real.log (s j / r j)) + ε))) /
        ((N : ℝ) + 1) ^ (d + d * (d - 1) / 2 + 1)
      ≤ Real.exp (-∑ j, ((Y.val.rowLen j.val : ℕ) : ℝ) * Real.log (s j / r j)) /
          (2 * ((N + 1 : ℕ) : ℝ) ^ d * cN d N) :=
        (div_le_div_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hexp))
          (by positivity)).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hDpos hpoly)
    _ = 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ d * cN d N) *
          Real.exp (-∑ j, ((Y.val.rowLen j.val : ℕ) : ℝ) * Real.log (s j / r j)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hDs (Real.exp_pos _).le

end KWSpectrum.Estimator.Red

namespace KWCore

open Filter Topology

theorem le_neg_of_forall {X Y : EReal}
    (h : ∀ m : ℝ, (m : EReal) < Y → X ≤ ((-m : ℝ) : EReal)) : X ≤ -Y := by
  rw [EReal.le_neg]
  by_contra hlt
  push_neg at hlt
  obtain ⟨m, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have h3 := h m h2
  rw [EReal.coe_neg] at h3
  have h4 : ((m : ℝ) : EReal) ≤ -X := EReal.le_neg_of_le_neg h3
  exact absurd h1 (not_lt.2 h4)

theorem neg_iInf_le {α : Type*} {S : Set α} {g : α → EReal} {X : EReal}
    (h : ∀ s ∈ S, -g s ≤ X) : -(⨅ s ∈ S, g s) ≤ X := by
  rw [EReal.neg_le]
  exact le_iInf₂ fun s hs => EReal.neg_le.1 (h s hs)

theorem avg_bound {ι : Type*} [Fintype ι] (p a : ι → ℝ) (c ε B : ℝ) (far : ι → Prop)
    [DecidablePred far] (hnn : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hB : ∀ i, |a i - c| ≤ 2 * B) (hnear : ∀ i, ¬ far i → |a i - c| ≤ ε / 2) (hB0 : 0 ≤ B)
    (hfar : ∑ i with far i, p i < ε / (2 * (2 * B + 1))) (hε : 0 < ε) :
    |∑ i, a i * p i - c| < ε := by
  have key : ∀ i, |a i - c| * p i ≤ ε / 2 * p i + 2 * B * (if far i then p i else 0) := by
    intro i
    split_ifs with h
    · nlinarith [hnn i, hB i]
    · rw [mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (hnear i h) (hnn i)
  have hexp : (∑ i, a i * p i) - c = ∑ i, (a i - c) * p i := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
  have hF0 : 0 ≤ ∑ i with far i, p i := Finset.sum_nonneg fun i _ => hnn i
  have e : (2 * B + 1) * (ε / (2 * (2 * B + 1))) = ε / 2 := by
    field_simp
  have hF : (2 * B + 1) * (∑ i with far i, p i) < ε / 2 := by
    rw [← e]; exact mul_lt_mul_of_pos_left hfar (by linarith)
  rw [hexp]
  calc |∑ i, (a i - c) * p i| ≤ ∑ i, |(a i - c) * p i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i - c| * p i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hnn i)]
    _ ≤ ∑ i, (ε / 2 * p i + 2 * B * (if far i then p i else 0)) :=
        Finset.sum_le_sum fun i _ => key i
    _ = ε / 2 + 2 * B * ∑ i with far i, p i := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, Finset.sum_filter,
          mul_one]
    _ < ε := by nlinarith

end KWCore

namespace KWSpectrum.Estimator.Red

open QAlgorithms QAlgorithms.Schur KWSpectrum.Estimator Filter Topology
open scoped ENNReal

theorem subset_relClosure {d : ℕ} {Δ : Set (Fin d → ℝ)} (hΔ : Δ ⊆ SpectrumSet d) :
    Δ ⊆ relClosure Δ := fun s hs => ⟨⟨s, hΔ hs⟩, subset_closure hs, rfl⟩

theorem relInterior_subset {d : ℕ} {Δ : Set (Fin d → ℝ)} : relInterior Δ ⊆ Δ := by
  rintro _ ⟨x, hx, rfl⟩
  exact interior_subset (s := (Subtype.val ⁻¹' Δ : Set (SpectrumSet d))) hx

theorem isCompact_spectrumSet (d : ℕ) : IsCompact (SpectrumSet d) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have e : SpectrumSet d = (⋂ i : Fin d, ⋂ j : Fin d, {s : Fin d → ℝ | i ≤ j → s j ≤ s i}) ∩
        ((⋂ j, {s : Fin d → ℝ | 0 ≤ s j}) ∩ {s | ∑ j, s j = 1}) := by
      ext s
      simp only [SpectrumSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun i j hij => h1 hij, h2, h3⟩,
        fun ⟨h1, h2, h3⟩ => ⟨fun i j hij => h1 i j hij, h2, h3⟩⟩
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
        (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const))
    by_cases h : i ≤ j
    · simp only [h, true_implies]
      exact isClosed_le (continuous_apply j) (continuous_apply i)
    · simp only [h, false_implies, Set.setOf_true]
      exact isClosed_univ
  · refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := 1)).subset fun s hs => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hs.2.1 j)]
    exact mem_le_one hs j

theorem part_c_upper (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (Δ : Set (Fin d → ℝ)) (hΔ : Δ ⊆ SpectrumSet d) :
    limsup (logRate (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Δ) atTop ≤
      -(⨅ s ∈ relClosure Δ, rate r s) := by
  apply KWCore.le_neg_of_forall
  intro m hm
  refine KWCore.limsup_le_of_bound
    (fun N => outcomeProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) N Δ)
    (d + d * (d - 1) / 2) m ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  refine outcome_le h17 h21 hdim hc hN U hU r hr Δ m fun s hs => ?_
  exact hm.le.trans (iInf₂_le s (subset_relClosure hΔ hs))

theorem part_c_lower (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (Δ : Set (Fin d → ℝ)) :
    -(⨅ s ∈ relInterior Δ, rate r s) ≤
      liminf (logRate (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Δ) atTop := by
  apply KWCore.neg_iInf_le
  intro s hs
  by_cases hfin : ∃ j, 0 < s j ∧ r j = 0
  · rw [rate, if_pos hfin, EReal.neg_top]
    exact bot_le
  · rw [rate, if_neg hfin, ← EReal.coe_neg]
    exact KWCore.le_liminf_of_bound
      (fun N => outcomeProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) N Δ)
      (d + d * (d - 1) / 2 + 1) _ (fun ε hε => outcome_ge h17 h21 hdim hc U hU r hr Δ s hs hfin ε hε)

theorem det_pos {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    (hdet : (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U).det ≠ 0) : ∀ j, 0 < r j := by
  intro j
  rcases (hr.2.1 j).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hdet
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [← h])]
    simp

theorem rate_eq_of_pos {d : ℕ} {r : Fin d → ℝ} (hpos : ∀ j, 0 < r j) (s : Fin d → ℝ) :
    rate r s = ((∑ j, (s j * Real.log (s j) - s j * Real.log (r j)) : ℝ) : EReal) := by
  have hn : ¬ ∃ j, 0 < s j ∧ r j = 0 := fun ⟨j, _, hj⟩ => (hpos j).ne' hj
  rw [rate, if_neg hn]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hs : s j = 0
  · simp [hs]
  · rw [Real.log_div hs (hpos j).ne', mul_sub]

theorem rate_continuous {d : ℕ} {r : Fin d → ℝ} (hpos : ∀ j, 0 < r j) :
    Continuous (fun s : Fin d → ℝ => rate r s) := by
  have e : (fun s : Fin d → ℝ => rate r s) =
      fun s => ((∑ j, (s j * Real.log (s j) - s j * Real.log (r j)) : ℝ) : EReal) :=
    funext (rate_eq_of_pos hpos)
  rw [e]
  refine continuous_coe_real_ereal.comp ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Real.continuous_mul_log.comp (continuous_apply j)).sub
    ((continuous_apply j).mul continuous_const)

theorem inf_relInt_le {d : ℕ} {r : Fin d → ℝ} (hpos : ∀ j, 0 < r j) (Δ : Set (Fin d → ℝ))
    (hsb : HasSmallBoundary Δ) :
    (⨅ s ∈ relInterior Δ, rate r s) ≤ ⨅ s ∈ relClosure Δ, rate r s := by
  refine le_iInf₂ fun t ht => ?_
  obtain ⟨x, hx, rfl⟩ := ht
  have hG : Continuous (fun y : SpectrumSet d => rate r y.val) :=
    (rate_continuous hpos).comp continuous_subtype_val
  have hcl : IsClosed {y : SpectrumSet d | (⨅ s ∈ relInterior Δ, rate r s) ≤ rate r y.val} :=
    isClosed_le continuous_const hG
  have hsub : interior (Subtype.val ⁻¹' Δ : Set (SpectrumSet d)) ⊆
      {y : SpectrumSet d | (⨅ s ∈ relInterior Δ, rate r s) ≤ rate r y.val} :=
    fun y hy => by
      exact iInf₂_le (f := fun s (_ : s ∈ relInterior Δ) => rate r s) y.val
        (show y.val ∈ relInterior Δ from ⟨y, hy, rfl⟩)
  exact (hcl.closure_subset_iff.2 hsub) (hsb hx)

theorem part_b (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    (hdet : (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U).det ≠ 0)
    (Δ : Set (Fin d → ℝ)) (hΔ : Δ ⊆ SpectrumSet d) (hsb : HasSmallBoundary Δ) :
    Tendsto (logRate (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Δ) atTop
      (𝓝 (-(⨅ s ∈ Δ, rate r s))) := by
  have hpos := det_pos U r hr hdet
  have hle1 : (⨅ s ∈ relClosure Δ, rate r s) ≤ ⨅ s ∈ Δ, rate r s :=
    le_iInf₂ fun s hs => iInf₂_le s (subset_relClosure hΔ hs)
  have hle2 : (⨅ s ∈ Δ, rate r s) ≤ ⨅ s ∈ relInterior Δ, rate r s :=
    le_iInf₂ fun s hs => iInf₂_le s (relInterior_subset hs)
  have hi := inf_relInt_le hpos Δ hsb
  have e1 : (⨅ s ∈ relInterior Δ, rate r s) = ⨅ s ∈ Δ, rate r s :=
    le_antisymm (hi.trans hle1) hle2
  have e2 : (⨅ s ∈ relClosure Δ, rate r s) = ⨅ s ∈ Δ, rate r s :=
    le_antisymm hle1 (hle2.trans hi)
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · rw [← e1]; exact part_c_lower h17 h21 hdim hc U hU r hr Δ
  · rw [← e2]; exact part_c_upper h17 h21 hdim hc U hU r hr Δ hΔ

theorem part_a (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (SpectrumSet d)) :
    Tendsto (fun N : ℕ => ∑ Y : Partition d N,
      f (youngFrac Y) * frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y)
      atTop (𝓝 (f r)) := by
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      exfalso
      have h3 := hr.2.2
      simp at h3
    · exact h
  obtain ⟨B, hB⟩ := (isCompact_spectrumSet d).exists_bound_of_continuousOn hf
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB r hr)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hf r hr) (ε / 2) (by positivity)
  have hδ' : 0 < min δ 1 := lt_min hδ one_pos
  have hfar := far_mass_tendsto h17 h21 hdim hc U hU r hr hδ' (min_le_right _ _)
  have hev := hfar.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * (2 * B + 1)) by positivity))
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  rw [Real.dist_eq]
  refine KWCore.avg_bound
    (fun Y => frameProb (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U) Y)
    (fun Y => f (youngFrac Y)) (f r) ε B (fun Y : Partition d N => ∃ j, min δ 1 ≤ |r j - youngFrac Y j|)
    (fun Y => frameProb_nonneg h17 h21 hdim Y U hU r hr)
    (frame_sum hc (partition_nonempty hd) U hU r hr) ?_ ?_ hB0 hN hε
  · intro Y
    have h1 := hB _ (youngFrac_mem hN0 Y)
    have h2 := hB r hr
    rw [Real.norm_eq_abs] at h1 h2
    calc |f (youngFrac Y) - f r| ≤ |f (youngFrac Y)| + |f r| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  · intro Y h
    push_neg at h
    have hdist : dist (youngFrac Y) r < δ := by
      rw [dist_pi_lt_iff hδ]
      intro j
      rw [Real.dist_eq, abs_sub_comm]
      exact (h j).trans_le (min_le_left _ _)
    have h3 := hδf (youngFrac_mem hN0 Y) hdist
    rw [Real.dist_eq] at h3
    exact h3.le

theorem main_of_children (h17 : Eq17) (h21 : Eq21) (hdim : DimBound) (hc : Complete) {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ) (_hρ : IsDensityMatrix ρ)
    (r : Fin d → ℝ) (hr : IsSpectrumOf ρ r) :
    (∀ f : (Fin d → ℝ) → ℝ, ContinuousOn f (SpectrumSet d) →
      Tendsto (fun N : ℕ => ∑ Y : Partition d N, f (youngFrac Y) * frameProb ρ Y)
        atTop (𝓝 (f r))) ∧
    (ρ.det ≠ 0 → ∀ Δ : Set (Fin d → ℝ), Δ ⊆ SpectrumSet d → HasSmallBoundary Δ →
      Tendsto (logRate ρ Δ) atTop (𝓝 (-(⨅ s ∈ Δ, rate r s)))) ∧
    (∀ Δ : Set (Fin d → ℝ), Δ ⊆ SpectrumSet d →
      -(⨅ s ∈ relInterior Δ, rate r s) ≤ liminf (logRate ρ Δ) atTop ∧
      limsup (logRate ρ Δ) atTop ≤ -(⨅ s ∈ relClosure Δ, rate r s)) := by
  obtain ⟨hrS, U, hU, rfl⟩ := hr
  exact ⟨fun f hf => part_a h17 h21 hdim hc U hU r hrS f hf,
    fun hdet Δ hΔ hsb => part_b h17 h21 hdim hc U hU r hrS hdet Δ hΔ hsb,
    fun Δ hΔ => ⟨part_c_lower h17 h21 hdim hc U hU r hrS Δ,
      part_c_upper h17 h21 hdim hc U hU r hrS Δ hΔ⟩⟩

end KWSpectrum.Estimator.Red

open KWSpectrum.Estimator QAlgorithms QAlgorithms.Schur Filter Topology in
theorem solution {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ)
    (r : Fin d → ℝ) (hr : IsSpectrumOf ρ r) :
    (∀ f : (Fin d → ℝ) → ℝ, ContinuousOn f (SpectrumSet d) →
      Tendsto (fun N : ℕ => ∑ Y : Partition d N, f (youngFrac Y) * frameProb ρ Y)
        atTop (𝓝 (f r))) ∧
    (ρ.det ≠ 0 → ∀ Δ : Set (Fin d → ℝ), Δ ⊆ SpectrumSet d → HasSmallBoundary Δ →
      Tendsto (logRate ρ Δ) atTop (𝓝 (-(⨅ s ∈ Δ, rate r s)))) ∧
    (∀ Δ : Set (Fin d → ℝ), Δ ⊆ SpectrumSet d →
      -(⨅ s ∈ relInterior Δ, rate r s) ≤ liminf (logRate ρ Δ) atTop ∧
      limsup (logRate ρ Δ) atTop ≤ -(⨅ s ∈ relClosure Δ, rate r s)) := by
  exact KWSpectrum.Estimator.Red.main_of_children
    (fun Y ρ' => KWSpectrum.Estimator.eq_17 Y ρ')
    (fun Y U hU r' ha hn => KWSpectrum.Estimator.eq_21 Y U hU r' ha hn)
    (fun Y => KWSpectrum.Estimator.dim_bound Y)
    (fun Y => (KWSpectrum.Estimator.eq_2_4_projections Y).2.2.2.2.1) ρ hρ r hr
