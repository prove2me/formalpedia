-- Prove2me | solution 1 for LatticeHamSim.StrictLR.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:41:18.751329+00:00
-- url     : https://prove2.me/submissions/05acb8d0-57ec-493d-b29c-7b6128bb4606

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace Aux_LHS_28s

open LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

lemma comm_disjoint (A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z Y : Finset Λ)
    (hA : SupportedOn Z A) (hB : SupportedOn Y B) (hd : Disjoint Z Y) : A * B = B * A := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hZY : ∀ x, x ∈ Z → x ∉ Y := fun x hx hy => Finset.disjoint_left.mp hd hx hy
  ext σ ρ
  simp only [Matrix.mul_apply, ha, hb]
  set τ1 : Λ → Fin q := fun x => if x ∈ Z then ρ x else σ x with hτ1
  set τ2 : Λ → Fin q := fun x => if x ∈ Y then ρ x else σ x with hτ2
  rw [Finset.sum_eq_single τ1, Finset.sum_eq_single τ2]
  · by_cases hC : ∀ x, x ∉ Y → x ∉ Z → σ x = ρ x
    · have p1 : ∀ x, x ∉ Z → σ x = τ1 x := fun x hx => by simp [τ1, hx]
      have p2 : ∀ x, x ∉ Y → τ1 x = ρ x := fun x hx => by
        by_cases hz : x ∈ Z
        · simp [τ1, hz]
        · simp only [τ1, hz, if_false]; exact hC x hx hz
      have p3 : ∀ x, x ∉ Y → σ x = τ2 x := fun x hx => by simp [τ2, hx]
      have p4 : ∀ x, x ∉ Z → τ2 x = ρ x := fun x hx => by
        by_cases hy : x ∈ Y
        · simp [τ2, hy]
        · simp only [τ2, hy, if_false]; exact hC x hy hx
      rw [if_pos p1, if_pos p2, if_pos p3, if_pos p4]
      have e1 : (fun x : Z => τ1 x) = (fun x : Z => ρ x) := by
        funext x; simp [τ1, x.2]
      have e2 : (fun x : Y => τ1 x) = (fun x : Y => σ x) := by
        funext x
        have hx : (x : Λ) ∉ Z := fun h => hZY x h x.2
        simp only [τ1, hx, if_false]
      have e3 : (fun x : Y => τ2 x) = (fun x : Y => ρ x) := by
        funext x; simp [τ2, x.2]
      have e4 : (fun x : Z => τ2 x) = (fun x : Z => σ x) := by
        funext x; simp [τ2, hZY x x.2]
      rw [e1, e2, e3, e4, mul_comm]
    · push_neg at hC
      obtain ⟨x, hxY, hxZ, hne⟩ := hC
      have n1 : ¬ ∀ x, x ∉ Y → τ1 x = ρ x := fun h => hne (by
        have := h x hxY; simpa [τ1, hxZ] using this)
      have n2 : ¬ ∀ x, x ∉ Z → τ2 x = ρ x := fun h => hne (by
        have := h x hxZ; simpa [τ2, hxY] using this)
      rw [if_neg n1, if_neg n2, mul_zero, mul_zero]
  · intro τ _ hne
    by_cases h1 : ∀ x, x ∉ Y → σ x = τ x
    · by_cases h2 : ∀ x, x ∉ Z → τ x = ρ x
      · exfalso; apply hne; funext x
        by_cases hx : x ∈ Y
        · simp only [τ2, hx, if_true]
          exact h2 x (fun hz => hZY x hz hx)
        · simp only [τ2, hx, if_false]; exact (h1 x hx).symm
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro τ _ hne
    by_cases h1 : ∀ x, x ∉ Z → σ x = τ x
    · by_cases h2 : ∀ x, x ∉ Y → τ x = ρ x
      · exfalso; apply hne; funext x
        by_cases hx : x ∈ Z
        · simp only [τ1, hx, if_true]
          exact h2 x (hZY x hx)
        · simp only [τ1, hx, if_false]; exact (h1 x hx).symm
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma comm_bound (P B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖P * B - B * P‖ ≤ 2 * ‖P‖ * ‖B‖ := by
  calc ‖P * B - B * P‖ ≤ ‖P * B‖ + ‖B * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖B‖ + ‖B‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖B‖ := by ring

lemma evolve_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve (H h) t O‖ = ‖O‖ := by
  have hsa : star (H h) = H h := by
    unfold H
    rw [star_sum]
    exact Finset.sum_congr rfl (fun X _ => hherm X)
  have key : ∀ s : ℝ, NormedSpace.exp ((Complex.I * (s : ℂ)) • H h) ∈
      unitary (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
    intro s
    have hs : ((s : ℂ) • H h) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have := (selfAdjoint.expUnitary ⟨(s : ℂ) • H h, hs⟩).prop
    simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
    exact this
  unfold evolve
  have hU := key t
  have hV := key (-t)
  rw [show (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring]
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma evolve_zero (J O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) : evolve J 0 O = O := by
  simp [evolve]

end Aux_LHS_28s


namespace Aux_LHS_28s_top
open LatticeHamSim.CommLR Aux_LHS_28s in
theorem old_eq_28 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (Y : Finset Λ) (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (Z : Finset Λ) (t : ℝ) :
    CB h B Z 0 ≤ 2 * ‖B‖ * indicator (meets Z Y) ∧
    CB h B Z t ≤ 2 * ‖B‖ ∧
    DB h B Z 0 ≤ 2 * ‖B‖ * ‖h Z‖ * indicator (meets Z Y) ∧
    DB h B Z t ≤ 2 * ‖B‖ * ‖h Z‖ := by
  have hCB : ∀ s : ℝ, CB h B Z s ≤ 2 * ‖B‖ := by
    intro s
    apply Real.sSup_le _ (by positivity)
    rintro r ⟨A, -, hA1, rfl⟩
    refine le_trans (comm_bound _ _) ?_
    rw [evolve_norm h hherm]
    nlinarith [norm_nonneg A, norm_nonneg B]
  have hDB : ∀ s : ℝ, DB h B Z s ≤ 2 * ‖B‖ * ‖h Z‖ := by
    intro s
    unfold DB
    refine le_trans (comm_bound _ _) ?_
    rw [evolve_norm h hherm]
    nlinarith [norm_nonneg (h Z), norm_nonneg B]
  refine ⟨?_, hCB t, ?_, hDB t⟩
  · unfold indicator
    split_ifs with hm
    · rw [mul_one]; exact hCB 0
    · rw [mul_zero]
      have hd : Disjoint Z Y := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact Finset.not_nonempty_iff_eq_empty.mp hm
      apply Real.sSup_le _ le_rfl
      rintro r ⟨A, hA, -, rfl⟩
      rw [evolve_zero, comm_disjoint A B Z Y hA hB hd, sub_self, norm_zero]
  · unfold indicator
    split_ifs with hm
    · rw [mul_one]; exact hDB 0
    · rw [mul_zero]
      have hd : Disjoint Z Y := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact Finset.not_nonempty_iff_eq_empty.mp hm
      unfold DB
      rw [evolve_zero, comm_disjoint (h Z) B Z Y (hsupp Z) hB hd, sub_self, norm_zero]

end Aux_LHS_28s_top

open LatticeHamSim.CommLR in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Y : Finset Λ) (hB : LatticeHamSim.CommLR.SupportedOn Y B)
    (Z : Finset Λ) (t : ℝ) :
    LatticeHamSim.CommLR.CB h B Z 0 ≤ 2 * ‖B‖ * (if LatticeHamSim.CommLR.meets Z Y then 1 else 0) ∧
    LatticeHamSim.CommLR.CB h B Z t ≤ 2 * ‖B‖ ∧
    LatticeHamSim.CommLR.DB h B Z 0 ≤ 2 * ‖B‖ * ‖h Z‖ * (if LatticeHamSim.CommLR.meets Z Y then 1 else 0) ∧
    LatticeHamSim.CommLR.DB h B Z t ≤ 2 * ‖B‖ * ‖h Z‖ := by
  have hind : LatticeHamSim.CommLR.indicator (LatticeHamSim.CommLR.meets Z Y) =
      (if LatticeHamSim.CommLR.meets Z Y then 1 else 0) := by
    by_cases hm : LatticeHamSim.CommLR.meets Z Y
    · rw [if_pos hm]; unfold LatticeHamSim.CommLR.indicator; rw [if_pos hm]
    · rw [if_neg hm]; unfold LatticeHamSim.CommLR.indicator; rw [if_neg hm]
  have := Aux_LHS_28s_top.old_eq_28 h hherm hsupp Y B hB Z t
  rw [hind] at this
  exact this
