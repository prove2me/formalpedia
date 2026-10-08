-- Prove2me | solution 1 for IgnallSchrage.MeanCompletion.sval_eq_shat_of_sorted
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:01:26.44523+00:00
-- url     : https://prove2.me/submissions/7ae164c1-4351-4fda-a1e3-b4bd23950b79

import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound
open IgnallSchrage.MeanCompletion

private theorem sorted_min {n : ℕ} (a b : Fin n → ℝ) (J l t : List (Fin n))
    (hl : l ∈ orderings J) (ht : t ∈ orderings J)
    (hs : l.Pairwise (fun i j => b i ≤ b j)) : Sval a b J l ≤ Sval a b J t := by
  classical
  have pl : l.Perm (unscheduledList J) := List.mem_permutations.mp (List.mem_toFinset.mp hl)
  have pt : t.Perm (unscheduledList J) := List.mem_permutations.mp (List.mem_toFinset.mp ht)
  have p : t.Perm l := pt.trans pl.symm
  have nl : l.Nodup := pl.nodup_iff.mpr ((List.nodup_finRange n).filter _)
  have nt : t.Nodup := p.nodup_iff.mpr nl
  let e : Fin t.length ≃ Fin l.length :=
    (nt.getEquiv t).trans ((Equiv.subtypeEquivRight (fun z => p.mem_iff)).trans (nl.getEquiv l).symm)
  let c : Fin l.length ≃ Fin t.length := finCongr p.length_eq.symm
  let σ : Equiv.Perm (Fin l.length) := c.trans e
  have he (q : Fin l.length) : l.get (σ q) = t.get (c q) := by
    have hh := (nl.getEquiv l).apply_symm_apply
      ((Equiv.subtypeEquivRight (fun z => p.mem_iff)) ((nt.getEquiv t) (c q)))
    exact congrArg Subtype.val hh
  have hav : Antivary (fun q : Fin l.length => (l.length : ℝ) - (q : ℝ))
      (fun q => b (l.get q)) := by
    intro i j hij
    have hij' : i ≤ j := by
      by_contra hn
      have hji : j ≤ i := le_of_lt (lt_of_not_ge hn)
      have := hs.rel_get_of_le hji
      dsimp only at hij
      linarith
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij'
    dsimp only
    linarith
  have hr := hav.sum_mul_le_sum_mul_comp_perm (σ := σ)
  let K := max (lastCompletion a b J) ((J.map a).sum + minUnscheduledA a J)
  have hcost : Sval a b J t =
      ∑ q : Fin l.length, (K + ((l.length : ℝ) - (q : ℝ)) * b (l.get (σ q))) := by
    unfold Sval
    rw [← c.sum_comp]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [he, c, finCongr_apply, Fin.val_cast, p.length_eq]
    rfl
  rw [hcost]
  unfold Sval
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hh := add_le_add (le_refl (l.length • K)) hr
  simpa only [K, List.get_eq_getElem, Fin.getElem_fin] using hh

theorem solution {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (l : List (Fin n)) (hl : l ∈ orderings J) (hsort : l.Pairwise (fun i j => b i ≤ b j)) :
    Sval a b J l = Shat a b J := by
  apply le_antisymm
  · exact Finset.le_inf' (orderings_nonempty J) (Sval a b J) (fun t ht => sorted_min a b J l t hl ht hsort)
  · exact Finset.inf'_le (Sval a b J) hl

#print axioms solution
