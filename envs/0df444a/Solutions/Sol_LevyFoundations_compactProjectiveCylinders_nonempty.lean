-- Prove2me | solution 1 for LevyFoundations.compactProjectiveCylinders_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:58:43.633096+00:00
-- url     : https://prove2.me/submissions/5ef1cf66-2c30-4ec8-97f5-a57f6f950a68

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.Topology.MetricSpace.Polish

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset Filter
open scoped ENNReal Topology

set_option maxHeartbeats 800000
theorem solution
    {ι : Type*} {α : ι → Type*}
    [∀ i, TopologicalSpace (α i)] [∀ i, PolishSpace (α i)]
    (hne : ∀ i, Nonempty (α i))
    (J : ℕ → Finset ι) (hJ_mono : Monotone J)
    (L : ∀ n, Set (∀ j : J n, α j))
    (hL_closed : ∀ n, IsClosed (L n))
    (hL_compact : ∀ n, IsCompact (L n))
    (hL_nonempty : ∀ n, (L n).Nonempty)
    (hL_restrict : ∀ {n m} (hnm : n ≤ m) (x : ∀ j : J m, α j),
      x ∈ L m → Finset.restrict₂ (hJ_mono hnm) x ∈ L n) :
    (⋂ n, cylinder (J n) (L n)).Nonempty := by
  classical
  let Prod := ∀ n : ℕ, ∀ j : J n, α j
  let inL : Set Prod := Set.pi Set.univ (fun n ↦ L n)
  have hProd_compact : IsCompact inL :=
    isCompact_univ_pi (fun n ↦ hL_compact n)
  let R : ℕ → Set Prod := fun n ↦
    inL ∩ ⋂ k : Fin n, {x : Prod |
      Finset.restrict₂ (hJ_mono (Nat.le_succ k)) (x (↑k + 1)) = x ↑k}
  have hR_closed : ∀ n, IsClosed (R n) := by
    intro n
    refine IsClosed.inter ?_ (isClosed_iInter fun k ↦ ?_)
    · exact isClosed_set_pi (fun n _ ↦ hL_closed n)
    · exact isClosed_eq
        ((Finset.continuous_restrict₂ _).comp (continuous_apply ((k : ℕ) + 1)))
        (continuous_apply (k : ℕ))
  have hR_anti : ∀ n, R (n + 1) ⊆ R n := by
    intro n x hx
    refine ⟨hx.1, Set.mem_iInter.2 fun k ↦ ?_⟩
    have hk := Set.mem_iInter.1 hx.2 (k.castSucc)
    simpa [Fin.val_castSucc] using hk
  have hR_nonempty : ∀ n, (R n).Nonempty := by
    intro n
    obtain ⟨yn, hyn⟩ := hL_nonempty n
    let y : Prod := fun k ↦
      if h : k ≤ n then Finset.restrict₂ (hJ_mono h) yn
      else (hL_nonempty k).some
    refine ⟨y, ?_, Set.mem_iInter.2 fun k ↦ ?_⟩
    · intro k _
      simp only [y]
      split_ifs with h
      · exact hL_restrict h yn hyn
      · exact (hL_nonempty k).some_mem
    · simp only [Set.mem_setOf_eq, y]
      have hk : (k : ℕ) < n := k.2
      rw [dif_pos (by omega : (↑k + 1) ≤ n), dif_pos k.2.le]
      ext ⟨j, hj⟩
      simp [Finset.restrict₂]
  have hR_inter : (⋂ n, R n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed R
      hR_anti hR_nonempty
      (hProd_compact.of_isClosed_subset (hR_closed 0) (Set.inter_subset_left))
      hR_closed
  obtain ⟨y, hy⟩ := hR_inter
  have hy_mem : ∀ n, y n ∈ L n := by
    intro n
    exact (Set.mem_iInter.1 hy 0).1 n (Set.mem_univ _)
  have hy_compat : ∀ n,
      Finset.restrict₂ (hJ_mono (Nat.le_succ n)) (y (n + 1)) = y n := by
    intro n
    have h_n1 := Set.mem_iInter.1 hy (n + 1)
    have h_fn := Set.mem_iInter.1 h_n1.2 (⟨n, lt_add_one n⟩ : Fin (n + 1))
    simpa using h_fn
  let f : ∀ i, α i := fun i ↦
    if h : ∃ n, i ∈ J n then y (Nat.find h) ⟨i, Nat.find_spec h⟩
    else (hne i).some
  refine ⟨f, Set.mem_iInter.2 fun n ↦ ?_⟩
  simp only [mem_cylinder]
  suffices h : (J n).restrict f = y n by
    rw [h]
    exact hy_mem n
  ext ⟨j, hj⟩
  simp only [Finset.restrict_def, f]
  have hij : ∃ k, j ∈ J k := ⟨n, hj⟩
  rw [dif_pos hij]
  set m := Nat.find hij with hm_def
  have hm_le : m ≤ n := Nat.find_min' _ hj
  have hy_compat_gen : ∀ (a b : ℕ) (hab : a ≤ b),
      Finset.restrict₂ (hJ_mono hab) (y b) = y a := by
    intro a b hab
    induction b with
    | zero =>
      have : a = 0 := Nat.eq_zero_of_le_zero hab
      subst this
      ext ⟨j', hj'⟩
      simp [Finset.restrict₂]
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hab'
      · ext ⟨j', hj'⟩
        simp [Finset.restrict₂]
      · have hab'' : a ≤ b := Nat.lt_succ_iff.mp hab'
        ext ⟨j', hj'⟩
        have h1 := congr_fun (hy_compat b) ⟨j', hJ_mono hab'' hj'⟩
        have h2 := congr_fun (ih hab'') ⟨j', hj'⟩
        simp [Finset.restrict₂] at h1 h2 ⊢
        rw [← h2, ← h1]
  have h := congr_fun (hy_compat_gen m n hm_le) ⟨j, Nat.find_spec hij⟩
  simp [Finset.restrict₂] at h
  exact h.symm
