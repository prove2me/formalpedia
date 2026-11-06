-- Prove2me | solution 1 for GradDOvS.Submod.lemma_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:20:39.891342+00:00
-- url     : https://prove2.me/submissions/532500bd-fd41-45ea-8a65-6d2527cf130a

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

open GradDOvS.Submod

namespace LVAux

variable {d : ℕ}

lemma mem_nbr (α : Equiv.Perm (Fin d)) (i : ℕ) (e : Fin d) :
    e ∈ nbr α i ↔ ((α.symm e : Fin d) : ℕ) < i := by
  simp [nbr]

lemma nbr_zero (α : Equiv.Perm (Fin d)) : nbr α 0 = ∅ := by
  ext e; simp [mem_nbr]

lemma nbr_full (α : Equiv.Perm (Fin d)) : nbr α d = Finset.univ := by
  ext e; simp [mem_nbr, (α.symm e).isLt]

lemma nbr_succ (α : Equiv.Perm (Fin d)) (n : ℕ) (h : n < d) :
    nbr α (n + 1) = insert (α ⟨n, h⟩) (nbr α n) := by
  ext e
  simp only [mem_nbr, Finset.mem_insert]
  constructor
  · intro h1
    by_cases h' : α.symm e = ⟨n, h⟩
    · left; rw [← h']; simp
    · right
      have : ((α.symm e : Fin d) : ℕ) ≠ n := fun h2 => h' (Fin.ext h2)
      omega
  · rintro (rfl | h2)
    · simp
    · omega

lemma nbr_not_mem (α : Equiv.Perm (Fin d)) (n : ℕ) (h : n < d) : α ⟨n, h⟩ ∉ nbr α n := by
  simp [mem_nbr]

lemma chainGrad_apply (f : Finset (Fin d) → ℝ) (α : Equiv.Perm (Fin d)) (n : ℕ) (h : n < d) :
    chainGrad f α (α ⟨n, h⟩) = f (nbr α (n + 1)) - f (nbr α n) := by
  simp [chainGrad]

lemma lovaszWith_eq (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) (α : Equiv.Perm (Fin d)) :
    lovaszWith f x α = f ∅ + ∑ e, chainGrad f α e * x e := by
  unfold lovaszWith
  rw [nbr_zero]
  congr 1
  rw [← Equiv.sum_comp α (fun e => chainGrad f α e * x e)]
  simp [chainGrad]

lemma tele (f : Finset (Fin d) → ℝ) (α : Equiv.Perm (Fin d)) :
    ∀ n, n ≤ d → ∑ e ∈ nbr α n, chainGrad f α e = f (nbr α n) - f ∅ := by
  intro n
  induction n with
  | zero => intro _; simp [nbr_zero]
  | succ n ih =>
    intro hn
    have hnd : n < d := hn
    rw [nbr_succ α n hnd, Finset.sum_insert (nbr_not_mem α n hnd), ih hnd.le,
      chainGrad_apply f α n hnd, nbr_succ α n hnd]
    ring

lemma base (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : Equiv.Perm (Fin d)) (T : Finset (Fin d)) :
    ∀ n, n ≤ d → ∑ e ∈ T ∩ nbr α n, chainGrad f α e ≤ f (T ∩ nbr α n) - f ∅ := by
  intro n
  induction n with
  | zero => intro _; simp [nbr_zero]
  | succ n ih =>
    intro hn
    have hnd : n < d := hn
    have hs := nbr_succ α n hnd
    have hga := chainGrad_apply f α n hnd
    have hnm := nbr_not_mem α n hnd
    have ih' := ih hnd.le
    by_cases haT : α ⟨n, hnd⟩ ∈ T
    · have h1 : T ∩ nbr α (n + 1) = insert (α ⟨n, hnd⟩) (T ∩ nbr α n) := by
        rw [hs, Finset.inter_insert_of_mem haT]
      have hn' : α ⟨n, hnd⟩ ∉ T ∩ nbr α n := fun h => hnm (Finset.mem_inter.1 h).2
      rw [h1, Finset.sum_insert hn', hga]
      have := hf (nbr α n) (insert (α ⟨n, hnd⟩) (T ∩ nbr α n))
      have hu : nbr α n ∪ insert (α ⟨n, hnd⟩) (T ∩ nbr α n) = nbr α (n + 1) := by
        rw [hs]
        ext e
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_inter]
        tauto
      have hi : nbr α n ∩ insert (α ⟨n, hnd⟩) (T ∩ nbr α n) = T ∩ nbr α n := by
        ext e
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, rfl | h2⟩
          · exact absurd h1 hnm
          · exact h2
        · rintro ⟨h1, h2⟩
          exact ⟨h2, Or.inr ⟨h1, h2⟩⟩
      rw [hu, hi] at this
      linarith
    · have h1 : T ∩ nbr α (n + 1) = T ∩ nbr α n := by
        rw [hs, Finset.inter_insert_of_notMem haT]
      rw [h1]; exact ih'

lemma base' (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : Equiv.Perm (Fin d)) (T : Finset (Fin d)) :
    ∑ e ∈ T, chainGrad f α e ≤ f T - f ∅ := by
  have := base f hf α T d le_rfl
  rwa [nbr_full, Finset.inter_univ] at this

lemma abel (N : ℕ) (dd c : ℕ → ℝ) (hc : ∀ k, k + 1 < N → c (k + 1) ≤ c k)
    (hD : ∀ j, j ≤ N → 0 ≤ ∑ k ∈ Finset.range j, dd k) :
    ∀ n, n + 1 ≤ N →
      (∑ k ∈ Finset.range (n + 1), dd k) * c n ≤ ∑ k ∈ Finset.range (n + 1), dd k * c k := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hc n (by omega)
    have h3 := hD (n + 1) (by omega)
    have h4 := mul_nonneg h3 (sub_nonneg.2 h2)
    rw [Finset.sum_range_succ (fun k => dd k * c k), Finset.sum_range_succ dd]
    nlinarith

noncomputable def seqOf (σ : Equiv.Perm (Fin d)) (G : Fin d → ℝ) (k : ℕ) : ℝ :=
  if h : k < d then G (σ ⟨k, h⟩) else 0

lemma sum_range_seq (σ : Equiv.Perm (Fin d)) (G : Fin d → ℝ) :
    ∀ j, j ≤ d → ∑ k ∈ Finset.range j, seqOf σ G k = ∑ e ∈ nbr σ j, G e := by
  intro j
  induction j with
  | zero => intro _; simp [nbr_zero]
  | succ j ih =>
    intro hj
    have hjd : j < d := hj
    rw [Finset.sum_range_succ, ih hjd.le, nbr_succ σ j hjd,
      Finset.sum_insert (nbr_not_mem σ j hjd)]
    simp [seqOf, hjd, add_comm]

lemma canonPerm_consistent (x : Fin d → ℝ) : IsConsistentPerm x (canonPerm x) := by
  intro i j hij
  have := Tuple.monotone_sort (fun i => -x i) hij
  simp only [Function.comp, canonPerm] at *
  linarith

theorem main (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (x : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) (hσ : IsConsistentPerm x σ)
    (α : Equiv.Perm (Fin d)) : lovaszWith f x α ≤ lovaszWith f x σ := by
  rw [lovaszWith_eq, lovaszWith_eq]
  suffices h : 0 ≤ ∑ e, (chainGrad f σ e - chainGrad f α e) * x e by
    have : ∑ e, (chainGrad f σ e - chainGrad f α e) * x e
        = ∑ e, chainGrad f σ e * x e - ∑ e, chainGrad f α e * x e := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring
    linarith
  set dd := seqOf σ (fun e => chainGrad f σ e - chainGrad f α e) with hdd
  set c := seqOf σ x with hc
  have hsum : ∑ e, (chainGrad f σ e - chainGrad f α e) * x e
      = ∑ k ∈ Finset.range d, dd k * c k := by
    have h1 : ∀ k, dd k * c k = seqOf σ (fun e => (chainGrad f σ e - chainGrad f α e) * x e) k := by
      intro k
      simp only [hdd, hc, seqOf]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun k _ => h1 k), sum_range_seq σ _ d le_rfl, nbr_full]
  have hD : ∀ j, j ≤ d → 0 ≤ ∑ k ∈ Finset.range j, dd k := by
    intro j hj
    rw [hdd, sum_range_seq σ _ j hj, Finset.sum_sub_distrib, tele f σ j hj]
    have := base' f hf α (nbr σ j)
    linarith
  have hDd : ∑ k ∈ Finset.range d, dd k = 0 := by
    rw [hdd, sum_range_seq σ _ d le_rfl, Finset.sum_sub_distrib, tele f σ d le_rfl]
    have := tele f α d le_rfl
    rw [nbr_full α] at this
    rw [nbr_full σ, this]
    ring
  rw [hsum]
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · simp [h0]
  · have hc' : ∀ k, k + 1 < d → c (k + 1) ≤ c k := by
      intro k hk
      have hk' : k < d := by omega
      simp only [hc, seqOf, dif_pos hk, dif_pos hk']
      exact hσ (show (⟨k, hk'⟩ : Fin d) ≤ ⟨k + 1, hk⟩ from Nat.le_succ k)
    have := abel d dd c hc' hD (d - 1) (by omega)
    rw [Nat.sub_add_cancel hpos, hDd] at this
    simpa using this

theorem convex_univ_lovasz (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ConvexOn ℝ Set.univ (lovasz f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  set z : Fin d → ℝ := a • x + b • y with hz
  have hz2 : lovasz f z = a * lovaszWith f x (canonPerm z) + b * lovaszWith f y (canonPerm z) := by
    unfold lovasz
    rw [lovaszWith_eq, lovaszWith_eq, lovaszWith_eq]
    have : ∑ e, chainGrad f (canonPerm z) e * z e
        = a * ∑ e, chainGrad f (canonPerm z) e * x e + b * ∑ e, chainGrad f (canonPerm z) e * y e := by
      simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intros; ring
    rw [this]
    have h3 : f ∅ = a * f ∅ + b * f ∅ := by rw [← add_mul, hab, one_mul]
    linarith
  rw [hz2]
  have h1 := main f hf x (canonPerm x) (canonPerm_consistent x) (canonPerm z)
  have h2 := main f hf y (canonPerm y) (canonPerm_consistent y) (canonPerm z)
  have := mul_le_mul_of_nonneg_left h1 ha
  have := mul_le_mul_of_nonneg_left h2 hb
  show _ ≤ a * lovaszWith f x (canonPerm x) + b * lovaszWith f y (canonPerm y)
  linarith

theorem lovasz_convexOn_box (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ConvexOn ℝ (box d) (lovasz f) :=
  (convex_univ_lovasz f hf).subset (Set.subset_univ _) (convex_Icc 0 1)

end LVAux

theorem solution {d : ℕ} (f : Finset (Fin d) → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ConvexOn ℝ (GradDOvS.Submod.box d) (GradDOvS.Submod.lovasz f) :=
  LVAux.lovasz_convexOn_box f hf
