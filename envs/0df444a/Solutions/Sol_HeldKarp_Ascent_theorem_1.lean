-- Prove2me | solution 1 for HeldKarp.Ascent.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:46:05.820703+00:00
-- url     : https://prove2.me/submissions/9be87c0a-a606-429f-9089-00d4542c25f6

import Mathlib.Tactic
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
open HeldKarp.Ascent
open scoped BigOperators
noncomputable section

private theorem weights_bdd {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) :
    BddBelow {x : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧ x = lagrWeight c π G} := by
  classical
  apply (Set.finite_range (lagrWeight c π)).bddBelow.mono
  rintro x ⟨G, hG, rfl⟩
  exact ⟨G, rfl⟩

private theorem bound_le_lagr {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsOneTree G) : oneTreeBound c π ≤ lagrWeight c π G :=
  csInf_le (weights_bdd c π) ⟨G, hG, rfl⟩

private theorem min_lagr_eq {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) : oneTreeBound c π = lagrWeight c π G := by
  apply le_antisymm (bound_le_lagr c π G hG.1)
  unfold oneTreeBound
  refine le_csInf ?_ ?_
  · exact ⟨lagrWeight c π G, G, hG.1, rfl⟩
  · rintro x ⟨G', hG', rfl⟩
    exact hG.2 G' hG'

private theorem ascent_ineq {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (πbar π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) :
    oneTreeBound c πbar - oneTreeBound c π ≤ ∑ i, (πbar i - π i) * degExcess G i := by
  have hb := bound_le_lagr c πbar G hG.1
  rw [min_lagr_eq c π G hG]
  unfold lagrWeight at hb ⊢
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  linarith

open Filter Topology
theorem _root_.solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (tbar : ℝ)
    (htbar : 0 < tbar) (π : ℕ → Fin n → ℝ) (T : ℕ → SimpleGraph (Fin n))
    (hT : ∀ m, IsMinOneTree c (π m) (T m))
    (hstep : ∀ m, π (m + 1) = π m + tbar • degExcess (T m)) :
    ∀ πstar : Fin n → ℝ, ∀ δ : ℝ, 0 < δ → ∃ m : ℕ,
      oneTreeBound c πstar
          - tbar / 2 * limsup (fun m => ∑ i, (degExcess (T m) i) ^ 2) atTop - δ
        < oneTreeBound c (π m) := by
  classical
  intro ps δ hδ
  by_contra hno
  push_neg at hno
  let v (m : ℕ) := ∑ i, (degExcess (T m) i)^2
  let D (m : ℕ) := ∑ i, (ps i - π m i)^2
  let L := limsup v atTop
  have hbdd : BddAbove (Set.range v) := by
    apply (Set.finite_range (fun G : SimpleGraph (Fin n) => ∑ i, (degExcess G i)^2)).bddAbove.mono
    rintro z ⟨m, rfl⟩
    exact ⟨T m, rfl⟩
  have hv : ∀ᶠ m in atTop, v m < L + δ/tbar :=
    eventually_lt_add_pos_of_limsup_le hbdd.isBoundedUnder_of_range le_rfl (div_pos hδ htbar)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hv
  have hdec (m : ℕ) (hm : N ≤ m) : D (m+1) ≤ D m - tbar*δ := by
    have ha := ascent_ineq c ps (π m) (T m) (hT m)
    have hw := hno m
    have hv' := hN m hm
    have heq : D (m+1) = D m - 2*tbar*(∑ i, (ps i-π m i)*degExcess (T m) i) + tbar^2*v m := by
      dsimp only [D, v]
      rw [hstep m]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    change oneTreeBound c (π m) ≤ oneTreeBound c ps - tbar/2*L - δ at hw
    have hc : (δ/tbar)*tbar = δ := div_mul_cancel₀ _ htbar.ne'
    have hh := mul_lt_mul_of_pos_left hv' (sq_pos_of_pos htbar)
    have hh' := mul_le_mul_of_nonneg_left ha htbar.le
    nlinarith
  have hiter (k : ℕ) : D (N+k) ≤ D N - (k : ℝ)*(tbar*δ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hdec (N+k) (by omega)
      rw [Nat.cast_succ]
      have he : N+(k+1) = (N+k)+1 := by omega
      rw [he]
      nlinarith
  obtain ⟨k, hk⟩ := exists_nat_gt (D N / (tbar*δ))
  have hk' := (div_lt_iff₀ (mul_pos htbar hδ)).mp hk
  have hi := hiter k
  have hpos : 0 ≤ D (N+k) := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith
