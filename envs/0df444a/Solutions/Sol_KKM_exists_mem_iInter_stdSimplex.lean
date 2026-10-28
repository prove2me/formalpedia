-- Prove2me | solution 1 for KKM.exists_mem_iInter_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:08:13.84821+00:00
-- url     : https://prove2.me/submissions/008861c6-6a43-4890-91e0-4dccbd271f10

import Mathlib
import Theorems.Thm_AGT_brouwer_fixed_point

-- carved verbatim out of submission 818ed08f-1f44-45cc-90a9-3239f8bb6e07, lines 785-868

section

open Fin.NatCast in
theorem solution (n : ℕ) (A : Fin (n+1) → Set (Fin (n+1) → ℝ)) (hA : ∀ i, IsOpen (A i))
    (hcov : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), ∃ i, x ∈ A i)
    (hC : ∀ i, Convex ℝ (stdSimplex ℝ (Fin (n+1)) \ A i))
    (hv : ∀ i j, i ≠ j → (Pi.single i 1 : Fin (n+1) → ℝ) ∉ A j) :
    ∃ x ∈ stdSimplex ℝ (Fin (n+1)), ∀ i, x ∈ A i := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨i, hi⟩ := hcov _ (single_mem_stdSimplex ℝ (0 : Fin 1))
    exact ⟨_, single_mem_stdSimplex ℝ (0 : Fin 1), fun j => by
      have hj : j = i := Fin.ext (by have := j.2; have := i.2; omega)
      rw [hj]; exact hi⟩
  have : Nontrivial (Fin (n+1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- distance functions
  have hne : ∀ i, ((A i)ᶜ).Nonempty := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨_, hv j i hj⟩
  let φ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ := fun i x => Metric.infDist x (A i)ᶜ
  have hφc : ∀ i, Continuous (φ i) := fun i => Metric.continuous_infDist_pt _
  have hφpos : ∀ i x, 0 < φ i x ↔ x ∈ A i := by
    intro i x
    have := (hA i).isClosed_compl.notMem_iff_infDist_pos (hne i) (x := x)
    simp only [Set.mem_compl_iff, not_not] at this
    exact this.symm
  have hφnn : ∀ i x, 0 ≤ φ i x := fun i x => Metric.infDist_nonneg
  let S : (Fin (n+1) → ℝ) → ℝ := fun x => ∑ i, φ i x
  have hSpos : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), 0 < S x := by
    intro x hx
    obtain ⟨i, hi⟩ := hcov x hx
    exact lt_of_lt_of_le ((hφpos i x).2 hi)
      (Finset.single_le_sum (fun j _ => hφnn j x) (Finset.mem_univ i))
  let sh : Equiv.Perm (Fin (n+1)) := Equiv.subRight (1 : Fin (n+1))
  let T : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) := fun x i => φ (sh i) x / S x
  have hT : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), T x ∈ stdSimplex ℝ (Fin (n+1)) := by
    intro x hx
    refine ⟨fun i => div_nonneg (hφnn _ _) (hSpos x hx).le, ?_⟩
    simp only [T]
    rw [← Finset.sum_div]
    have : ∑ i, φ (sh i) x = S x := Equiv.sum_comp sh (fun j => φ j x)
    rw [this, div_self (hSpos x hx).ne']
  have hTc : ContinuousOn T (stdSimplex ℝ (Fin (n+1))) := by
    refine continuousOn_pi.2 fun i => ?_
    refine ContinuousOn.div (hφc _).continuousOn ?_ (fun x hx => (hSpos x hx).ne')
    exact (continuous_finsetSum _ fun j _ => hφc j).continuousOn
  obtain ⟨x, hx, hfix⟩ := AGT.brouwer_fixed_point (convex_stdSimplex ℝ (Fin (n+1)))
    (isCompact_stdSimplex ℝ (Fin (n+1))) ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩ T hTc hT
  -- face inclusion
  have hface : ∀ j, x j = 0 → x ∉ A j := by
    intro j hj hxA
    have hmem : x ∈ stdSimplex ℝ (Fin (n+1)) \ A j := by
      have hsum : ∑ k ∈ Finset.univ.erase j, x k = 1 := by
        rw [Finset.sum_erase _ hj]; exact hx.2
      have := (hC j).sum_mem (t := Finset.univ.erase j) (w := x) (z := fun k => (Pi.single k 1 : Fin (n+1) → ℝ))
        (fun k _ => hx.1 k) hsum (fun k hk => ⟨single_mem_stdSimplex ℝ k, hv k j (Finset.ne_of_mem_erase hk)⟩)
      convert this using 1
      funext m
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      simp [Pi.single_apply, hj]
    exact hmem.2 hxA
  -- supports
  have hxi : ∀ i, x i = φ (sh i) x / S x := fun i => (congrFun hfix i).symm
  have hJ : ∀ j, x ∈ A j → x ∈ A (sh j) := by
    intro j hj
    have h1 : x j ≠ 0 := fun h => hface j h hj
    have h2 : 0 < x j := lt_of_le_of_ne (hx.1 j) (Ne.symm h1)
    rw [hxi j] at h2
    have := (div_pos_iff_of_pos_right (hSpos x hx)).1 h2
    exact (hφpos _ _).1 this
  have hall : ∀ k : ℕ, ∀ j, x ∈ A j → x ∈ A (j - (k : Fin (n+1))) := by
    intro k
    induction k with
    | zero => intro j hj; simpa using hj
    | succ k ih =>
      intro j hj
      have := hJ _ (ih j hj)
      have e : sh (j - (k : Fin (n+1))) = j - ((k+1 : ℕ) : Fin (n+1)) := by
        simp [sh, Equiv.subRight_apply, Nat.cast_succ, sub_sub]
      rw [e] at this; exact this
  obtain ⟨i0, hi0⟩ := hcov x hx
  refine ⟨x, hx, fun i => ?_⟩
  have := hall (i0 - i).val i0 hi0
  rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this

end
