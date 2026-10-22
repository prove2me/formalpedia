-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_truncated_log_matrix_surjective_of_distinct_centers
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:30:01.656764+00:00
-- url     : https://prove2.me/submissions/c1699665-d7c3-4b68-8555-77adf6768b13

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open OAI.PiExponent.InterpolationMatrix

theorem solution :
    ¬ (∀ {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
        (r : Fin m → Complex) (T : Fin m → Nat)
        (_hcenters : Function.Injective
          (fun j : Fin K => fun i : Fin m => (j.val : Complex) * r i)),
        Function.Surjective
          (truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin) := by
  intro hAll
  -- Tiny height H = 1/2 with unit weights: unique zero column, at least two rows.
  let m : ℕ := 1
  let K : ℕ := 2
  let w0 : ℝ := 1
  let v0 : ℝ := 1
  let theta : ℝ := 1
  let w : Fin m → ℝ := fun _ => 1
  let H : ℝ := (1 : ℝ) / 2
  let r : Fin m → ℂ := fun _ => 1
  let T : Fin m → ℕ := fun _ => 1
  have hcenters : Function.Injective
      (fun j : Fin K => fun i : Fin m => (j.val : Complex) * r i) := by
    intro j₁ j₂ hj
    have := congrArg (fun f => f (0 : Fin 1)) hj
    simp [r] at this
    exact Fin.ext (Nat.cast_injective this)
  have hsurj :
      Function.Surjective (truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin :=
    hAll (m := m) K w0 v0 theta w H r T hcenters
  have hwcol (i : Fin (m + 1)) : columnWeights w0 w i = 1 := by
    fin_cases i <;> rfl
  have hwrow (i : Fin (m + 1)) : rowWeights v0 theta w i = 1 := by
    have heq : rowWeights v0 theta w i = columnWeights w0 w i := by
      fin_cases i
      · rfl
      · -- index 1 = succ 0: row weight is w 0 / theta
        simp only [rowWeights, columnWeights]
        change (w (⟨0, by omega⟩ : Fin 1) / theta) = w (⟨0, by omega⟩ : Fin 1)
        simp [w, theta]
    rw [heq, hwcol i]
  have hfl_col (i : Fin (m + 1)) : ⌊H / columnWeights w0 w i⌋₊ = 0 := by
    rw [hwcol i]; norm_num [H]
  have hfl_row (i : Fin (m + 1)) : ⌊H / rowWeights v0 theta w i⌋₊ = 0 := by
    rw [hwrow i]; norm_num [H]
  have hCol0 : ∀ c : Column w0 w H, (c : Fin (m + 1) → ℕ) = fun _ => 0 := by
    intro c
    have hc : c.1 ∈ realWeightedSimplex (columnWeights w0 w) H := c.property
    have hc' : (∀ i : Fin (m + 1), c.1 i ≤ ⌊H / columnWeights w0 w i⌋₊) ∧
        ∑ i, columnWeights w0 w i * (c.1 i : ℝ) ≤ H := by
      simpa [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
        Finset.mem_range, Nat.lt_succ_iff] using hc
    refine funext fun i => Nat.eq_zero_of_le_zero ?_
    have := hc'.1 i
    simpa [hfl_col i] using this
  have h0mem : (fun _ : Fin (m + 1) => (0 : ℕ)) ∈
      realWeightedSimplex (columnWeights w0 w) H := by
    have : (∀ i : Fin (m + 1), (0 : ℕ) ≤ ⌊H / columnWeights w0 w i⌋₊) ∧
        ∑ i, columnWeights w0 w i * ((fun _ : Fin (m + 1) => (0 : ℕ)) i : ℝ) ≤ H := by
      constructor
      · intro i; exact Nat.zero_le _
      · simp only [hwcol]; norm_num [H]
    simpa [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_range, Nat.lt_succ_iff] using this
  haveI : Unique (Column w0 w H) :=
    { default := ⟨fun _ => 0, h0mem⟩
      uniq := fun c => Subtype.ext (hCol0 c) }
  have hcardCol : Fintype.card (Column w0 w H) = 1 := Fintype.card_unique
  have h0row : (fun _ : Fin (m + 1) => (0 : ℕ)) ∈
      strictWeightedSimplex (rowWeights v0 theta w) H := by
    have hreal : (fun _ : Fin (m + 1) => (0 : ℕ)) ∈
        realWeightedSimplex (rowWeights v0 theta w) H := by
      have : (∀ i : Fin (m + 1), (0 : ℕ) ≤ ⌊H / rowWeights v0 theta w i⌋₊) ∧
          ∑ i, rowWeights v0 theta w i *
            ((fun _ : Fin (m + 1) => (0 : ℕ)) i : ℝ) ≤ H := by
        constructor
        · intro i; exact Nat.zero_le _
        · simp only [hwrow]; norm_num [H]
      simpa [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
        Finset.mem_range, Nat.lt_succ_iff] using this
    have hstrict : ∑ i, rowWeights v0 theta w i *
        ((fun _ : Fin (m + 1) => (0 : ℕ)) i : ℝ) < H := by
      simp only [hwrow]; norm_num [H]
    exact Finset.mem_filter.mpr ⟨hreal, hstrict⟩
  have hcardRow : 2 ≤ Fintype.card (Row K v0 theta w H) := by
    let emb : Fin 2 → Row K v0 theta w H := fun j => (j, ⟨fun _ => 0, h0row⟩)
    have hinj : Function.Injective emb := fun a b h => by
      simpa [emb] using congrArg Prod.fst h
    simpa using Fintype.card_le_of_injective emb hinj
  have hle : Module.finrank ℂ (Row K v0 theta w H → ℂ) ≤
      Module.finrank ℂ (Column w0 w H → ℂ) :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  have hR : Module.finrank ℂ (Row K v0 theta w H → ℂ) =
      Fintype.card (Row K v0 theta w H) :=
    Module.finrank_fintype_fun_eq_card (R := ℂ) (η := Row K v0 theta w H)
  have hC : Module.finrank ℂ (Column w0 w H → ℂ) =
      Fintype.card (Column w0 w H) :=
    Module.finrank_fintype_fun_eq_card (R := ℂ) (η := Column w0 w H)
  rw [hR, hC, hcardCol] at hle
  linarith
