-- Prove2me | solution 1 for KissingNumber.kissingNumber_attained
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:35:39.84503+00:00
-- url     : https://prove2.me/submissions/f630f82a-75a7-4581-a565-a1812b1416fd

import Definitions.Def_KissingNumber
set_option autoImplicit false
open KissingNumber
open scoped InnerProductSpace

/-- Grid cell of a point, at mesh `1 / (d + 1)`. -/
private noncomputable def cell {d : ℕ} (x : Ambient d) : Fin d → ℤ :=
  fun i => ⌊x i * ((d : ℝ) + 1)⌋

private lemma cell_mem {d : ℕ} (x : Ambient d) (hx : ‖x‖ = 1) :
    cell x ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1)) := by
  rw [Fintype.mem_piFinset]
  intro i
  have hi : |x i| ≤ 1 := by
    have := PiLp.norm_apply_le x i
    rw [hx, Real.norm_eq_abs] at this
    exact this
  have hM : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  rw [abs_le] at hi
  rw [Finset.mem_Icc]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    nlinarith
  · apply Int.floor_le_iff.mpr
    push_cast
    nlinarith

private lemma cell_injOn {d : ℕ} (C : KissingConfig d) : Set.InjOn cell (C.points : Set (Ambient d)) := by
  intro x hx y hy hxy
  by_contra hne
  have hin := C.inner_le x hx y hy hne
  have hnx := C.unit_norm x hx
  have hny := C.unit_norm y hy
  have h1 : (1 : ℝ) ≤ ‖x - y‖ ^ 2 := by
    rw [norm_sub_sq_real, hnx, hny]; linarith
  have hM : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hcoord : ∀ i, (x i - y i) ^ 2 ≤ 1 / ((d : ℝ) + 1) ^ 2 := by
    intro i
    have he : ⌊x i * ((d : ℝ) + 1)⌋ = ⌊y i * ((d : ℝ) + 1)⌋ := congrFun hxy i
    have hlt := Int.abs_sub_lt_one_of_floor_eq_floor he
    rw [← sub_mul, abs_mul, abs_of_pos hM] at hlt
    have hab : |x i - y i| ≤ 1 / ((d : ℝ) + 1) := by
      rw [le_div_iff₀ hM]; exact hlt.le
    calc (x i - y i) ^ 2 = |x i - y i| ^ 2 := (sq_abs _).symm
      _ ≤ (1 / ((d : ℝ) + 1)) ^ 2 := by gcongr
      _ = 1 / ((d : ℝ) + 1) ^ 2 := by rw [one_div_pow]
  have h2 : ‖x - y‖ ^ 2 ≤ (d : ℝ) / ((d : ℝ) + 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(x - y) i‖ ^ 2 = ∑ i, (x i - y i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]; rfl
      _ ≤ ∑ _i : Fin d, 1 / ((d : ℝ) + 1) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) / ((d : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h3 : (d : ℝ) / ((d : ℝ) + 1) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  linarith

private lemma card_le {d : ℕ} (C : KissingConfig d) : C.points.card ≤ (2 * (d + 1) + 1) ^ d := by
  have h := Finset.card_le_card_of_injOn cell (fun x hx => cell_mem x (C.unit_norm x hx))
    (cell_injOn C)
  rw [Fintype.card_piFinset] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc] at h
  have e : ((d : ℤ) + 1 + 1 - -((d : ℤ) + 1)).toNat = 2 * (d + 1) + 1 := by omega
  rw [e] at h
  exact h

theorem solution (d : ℕ) : ∃ C : KissingConfig d, (C.points.card : ℕ∞) = kissingNumber d := by
  let f : KissingConfig d → ℕ := fun C => C.points.card
  have hbdd : BddAbove (Set.range f) := ⟨(2 * (d + 1) + 1) ^ d, by
    rintro _ ⟨C, rfl⟩; exact card_le C⟩
  have hne : (Set.range f).Nonempty :=
    ⟨f ⟨∅, by simp, by simp⟩, ⟨_, rfl⟩⟩
  obtain ⟨C, hC⟩ := Nat.sSup_mem hne hbdd
  refine ⟨C, le_antisymm (le_iSup (fun C : KissingConfig d => (C.points.card : ℕ∞)) C) ?_⟩
  refine iSup_le fun D => ?_
  have : f D ≤ f C := by rw [hC]; exact le_csSup hbdd ⟨D, rfl⟩
  exact_mod_cast this
