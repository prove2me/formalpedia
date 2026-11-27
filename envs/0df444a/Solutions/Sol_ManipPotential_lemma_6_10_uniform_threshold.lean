-- Prove2me | solution 1 for ManipPotential.lemma_6_10_uniform_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:58:59.345584+00:00
-- url     : https://prove2.me/submissions/1495cdff-4dc6-41e7-946f-b8d5baff9f44

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_cycL

open ManipPotential

namespace LT610

lemma eq_of_weakly_ell {m : ℕ} [NeZero m] (j c : Fin m)
    (h : Ranking.WeaklyPrefers (ell j) c j) : c = j := by
  unfold Ranking.WeaklyPrefers at h
  simp only [ell, Equiv.subLeft_apply, sub_self] at h
  have h2 : j - c = 0 := by
    rw [Fin.le_def] at h
    ext
    simp only [Fin.val_zero] at h ⊢
    omega
  exact (sub_eq_zero.mp h2).symm

lemma unitVec_smul_nonneg {m : ℕ} (r : Ranking m) (c : ℚ) (hc : 0 ≤ c) :
    0 ≤ c • (unitVec r : Ranking m → ℚ) :=
  smul_nonneg hc (Pi.single_nonneg.2 zero_le_one)

lemma replace {m : ℕ} [NeZero m] (K : ℕ) (g : (Ranking m → ℚ) → Fin m) (hg : BoundedMP K g)
    (j : Fin m) (d : Ranking m → ℚ) (hd : ∀ r, 0 < d r) :
    ∀ (S : Finset (Ranking m)) (Z : Ranking m → ℚ), 0 ≤ Z →
      g (Z + ∑ r ∈ S, d r • unitVec r) = j →
      g (Z + (((K:ℚ)+1) * ∑ r ∈ S, d r) • unitVec (ell j)) = j := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro Z _ h; simpa using h
  | insert a S ha ih =>
    intro Z hZ h
    rw [Finset.sum_insert ha] at h
    have h1 := ih (Z + d a • unitVec a)
      (add_nonneg hZ (unitVec_smul_nonneg a _ (hd a).le)) (by rw [add_assoc]; exact h)
    set B := Z + (((K:ℚ)+1) * ∑ r ∈ S, d r) • unitVec (ell j) with hB
    have hB0 : 0 ≤ B := add_nonneg hZ (unitVec_smul_nonneg _ _ (by
      have : 0 ≤ ∑ r ∈ S, d r := Finset.sum_nonneg (fun r _ => (hd r).le)
      positivity))
    have key := hg B hB0 (ell j) a (((K:ℚ)+1) * d a) (d a) (by have := hd a; positivity)
      (hd a) le_rfl
    have e1 : B + d a • unitVec a =
        Z + d a • unitVec a + (((K:ℚ)+1) * ∑ r ∈ S, d r) • unitVec (ell j) := by
      rw [hB]; abel
    rw [e1, h1] at key
    have e2 : B + (((K:ℚ)+1) * d a) • unitVec (ell j) =
        Z + (((K:ℚ)+1) * (d a + ∑ r ∈ S, d r)) • unitVec (ell j) := by
      rw [hB, mul_add, add_smul]; abel
    rw [Finset.sum_insert ha, ← e2]
    exact eq_of_weakly_ell j _ key

end LT610

open LT610 in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g)
    (P : Ranking m → ℝ) (hP : IsCommonJunction g P) (ε : ℝ) (hε : 0 < ε)
    (hεP : ε < (1 / 2) * Finset.univ.inf' Finset.univ_nonempty P)
    (Z : Ranking m → ℚ) (hZ : ∀ r, 0 < Z r)
    (hZP : ‖(fun r => (Z r : ℝ)) - (P - (fun _ => ε))‖ < ε / 4) :
    ∃ u₀ : ℚ, 0 ≤ u₀ ∧
      (u₀ : ℝ) < 2 * ((K : ℝ) + 1) * (m.factorial : ℝ) * ε ∧
      ∀ (j : Fin m) (u : ℚ), u₀ < u → g (Z + u • unitVec (ell j)) = j := by
  classical
  obtain ⟨_, hBMP, hCP⟩ := hg
  have hW : ∀ j : Fin m, ∃ W : Ranking m → ℚ, g W = j ∧
      ∀ r, |(W r : ℝ) - P r| < ε / 4 := by
    intro j
    have hPj := (hP j).2
    rw [Metric.mem_closure_iff] at hPj
    obtain ⟨b, ⟨_, q, hq, hgq⟩, hdist⟩ := hPj (ε / 4) (by linarith)
    refine ⟨q, hgq, fun r => ?_⟩
    have := (dist_le_pi_dist P b r).trans_lt hdist
    subst hq
    rw [Real.dist_eq] at this
    rw [abs_sub_comm]; simpa using this
  choose W hWg hWd using hW
  let d : Fin m → Ranking m → ℚ := fun j r => W j r - Z r
  have hZr : ∀ r, |(Z r : ℝ) - (P r - ε)| < ε / 4 := fun r => by
    have := (norm_le_pi_norm ((fun r => (Z r : ℝ)) - (P - (fun _ => ε))) r).trans_lt hZP
    simpa [Real.norm_eq_abs] using this
  have hd_lo : ∀ j r, ε / 2 < (d j r : ℝ) := by
    intro j r
    have h1 := hWd j r; have h2 := hZr r
    rw [abs_lt] at h1 h2
    simp only [d]; push_cast; linarith
  have hd_hi : ∀ j r, (d j r : ℝ) < 3 * ε / 2 := by
    intro j r
    have h1 := hWd j r; have h2 := hZr r
    rw [abs_lt] at h1 h2
    simp only [d]; push_cast; linarith
  have hd_pos : ∀ j r, 0 < d j r := fun j r => by
    have := hd_lo j r
    exact_mod_cast (show (0:ℝ) < d j r by linarith)
  let u : Fin m → ℚ := fun j => ((K:ℚ) + 1) * ∑ r, d j r
  have hu : ∀ j, g (Z + u j • unitVec (ell j)) = j := by
    intro j
    apply replace K g hBMP j (d j) (hd_pos j) Finset.univ Z (fun r => (hZ r).le)
    have : Z + ∑ r, d j r • unitVec r = W j := by
      funext r; simp [d, Finset.sum_apply, unitVec, Pi.single_apply]
    rw [this]; exact hWg j
  have hu_pos : ∀ j, 0 < u j := by
    intro j
    have : 0 < ∑ r, d j r := Finset.sum_pos (fun r _ => hd_pos j r) Finset.univ_nonempty
    simp only [u]; positivity
  have hu_lt : ∀ j, (u j : ℝ) < 2 * ((K : ℝ) + 1) * (m.factorial : ℝ) * ε := by
    intro j
    have hsum : ∑ r, (d j r : ℝ) < (m.factorial : ℝ) * (3 * ε / 2) := by
      calc ∑ r, (d j r : ℝ) < ∑ _r : Ranking m, 3 * ε / 2 :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun r _ => hd_hi j r)
        _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
    simp only [u]; push_cast
    have hK : (0:ℝ) < (K:ℝ) + 1 := by positivity
    have h0 : 0 ≤ ((K:ℝ) + 1) * (m.factorial : ℝ) * ε := by positivity
    calc ((K:ℝ) + 1) * ∑ r, (d j r : ℝ) < ((K:ℝ) + 1) * ((m.factorial : ℝ) * (3 * ε / 2)) :=
          mul_lt_mul_of_pos_left hsum hK
      _ ≤ _ := by nlinarith [h0]
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty u
  refine ⟨Finset.univ.sup' Finset.univ_nonempty u, ?_, ?_, ?_⟩
  · rw [hj0]; exact (hu_pos j0).le
  · rw [hj0]; exact hu_lt j0
  · intro j v hv
    have hle : u j ≤ Finset.univ.sup' Finset.univ_nonempty u :=
      Finset.le_sup' u (Finset.mem_univ j)
    have hpos : 0 < v - u j := by linarith
    have hP0 : 0 ≤ Z + u j • unitVec (ell j) :=
      add_nonneg (fun r => (hZ r).le) (unitVec_smul_nonneg _ _ (hu_pos j).le)
    have hPr : 0 < (Z + u j • (unitVec (ell j) : Ranking m → ℚ)) (ell j) := by
      simp only [Pi.add_apply, Pi.smul_apply, unitVec, Pi.single_eq_same, smul_eq_mul, mul_one]
      linarith [hZ (ell j), hu_pos j]
    have key := hCP _ hP0 (ell j) (v - u j) hpos hPr
    rw [hu j, add_assoc, ← add_smul, add_sub_cancel] at key
    exact eq_of_weakly_ell j _ key
