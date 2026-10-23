-- Prove2me | solution 1 for KaelblingPOMDP.Witness.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T04:20:06.34081+00:00
-- url     : https://prove2.me/submissions/d11ccaa2-af83-46ba-914e-db81ce6054ba

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

set_option autoImplicit false

universe u

open Classical in
/-- Perturbation lemma: among the maximizers at a belief `b` of a finite family of linear functions
on the simplex, one is strictly best (against all functions with a different coefficient vector)
at some belief `b'`. Induction on the number of maximizers; each step moves `b` slightly towards a
vertex `e_{s0}` on which two maximizers disagree. -/
theorem kw_perturb_useful {S : Type*} {ι : Type*} [Fintype S] (W : Finset ι) (g : ι → S → ℝ)
    (hW : W.Nonempty) :
    ∀ (n : ℕ) (b : S → ℝ), b ∈ stdSimplex ℝ S →
      (W.filter (fun i => ∀ j ∈ W, ∑ s, b s * g j s ≤ ∑ s, b s * g i s)).card ≤ n →
      ∃ q ∈ W, (∀ p ∈ W, ∑ s, b s * g p s ≤ ∑ s, b s * g q s) ∧
        ∃ b' ∈ stdSimplex ℝ S, ∀ p ∈ W, g p ≠ g q → ∑ s, b' s * g p s < ∑ s, b' s * g q s := by
  intro n
  induction n with
  | zero =>
    intro b _ hc
    obtain ⟨q, hq, hmax⟩ := W.exists_max_image (fun i => ∑ s, b s * g i s) hW
    have hmem : q ∈ W.filter (fun i => ∀ j ∈ W, ∑ s, b s * g j s ≤ ∑ s, b s * g i s) :=
      Finset.mem_filter.mpr ⟨hq, hmax⟩
    have := Finset.card_pos.mpr ⟨q, hmem⟩
    omega
  | succ n ih =>
    intro b hb hc
    set Arg := W.filter (fun i => ∀ j ∈ W, ∑ s, b s * g j s ≤ ∑ s, b s * g i s) with hArg
    by_cases hall : ∀ i ∈ Arg, ∀ j ∈ Arg, g i = g j
    · obtain ⟨q, hq, hmax⟩ := W.exists_max_image (fun i => ∑ s, b s * g i s) hW
      have hqA : q ∈ Arg := Finset.mem_filter.mpr ⟨hq, hmax⟩
      refine ⟨q, hq, hmax, b, hb, fun p hp hne => ?_⟩
      by_contra hle
      push_neg at hle
      have hpA : p ∈ Arg := Finset.mem_filter.mpr ⟨hp, fun j hj => (hmax j hj).trans hle⟩
      exact hne (hall p hpA q hqA)
    · push_neg at hall
      obtain ⟨i, hi, j, hj, hij⟩ := hall
      obtain ⟨s0, hs0⟩ := Function.ne_iff.mp hij
      obtain ⟨i0, hi0, j0, hj0, hlt⟩ : ∃ i0 ∈ Arg, ∃ j0 ∈ Arg, g i0 s0 < g j0 s0 := by
        rcases lt_or_gt_of_ne hs0 with h | h
        · exact ⟨i, hi, j, hj, h⟩
        · exact ⟨j, hj, i, hi, h⟩
      have hj0W := (Finset.mem_filter.mp hj0).1
      have hj0max := (Finset.mem_filter.mp hj0).2
      have hi0W := (Finset.mem_filter.mp hi0).1
      have hi0max := (Finset.mem_filter.mp hi0).2
      have hev : ∀ᶠ ε in nhds (0:ℝ), ∀ p ∈ W, p ∉ Arg →
          (1 - ε) * (∑ s, b s * g p s) + ε * g p s0 <
            (1 - ε) * (∑ s, b s * g j0 s) + ε * g j0 s0 := by
        rw [Filter.eventually_all_finset]
        intro p hp
        by_cases hpA : p ∈ Arg
        · exact Filter.Eventually.of_forall (fun _ h => absurd hpA h)
        · have hlt' : ∑ s, b s * g p s < ∑ s, b s * g j0 s := by
            by_contra hcon
            push_neg at hcon
            exact hpA (Finset.mem_filter.mpr ⟨hp, fun k hk => (hj0max k hk).trans hcon⟩)
          have hc1 : Continuous (fun ε : ℝ => (1 - ε) * (∑ s, b s * g p s) + ε * g p s0) := by
            fun_prop
          have hc2 : Continuous (fun ε : ℝ => (1 - ε) * (∑ s, b s * g j0 s) + ε * g j0 s0) := by
            fun_prop
          have h3 := (hc1.tendsto 0).eventually_lt (hc2.tendsto 0) (by simpa using hlt')
          filter_upwards [h3] with ε hε _ using hε
      obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.mp hev
      set ε : ℝ := min (δ / 2) (1 / 2) with hεdef
      have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
      have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hεδ : dist ε 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hPε := hP hεδ
      set b' : S → ℝ := fun s => (1 - ε) * b s + ε * (if s = s0 then 1 else 0) with hb'
      have hdot : ∀ x : S → ℝ, ∑ s, b' s * x s = (1 - ε) * (∑ s, b s * x s) + ε * x s0 := by
        intro x
        simp only [hb', add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ite_mul,
          one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hb'S : b' ∈ stdSimplex ℝ S := by
        refine ⟨fun s => ?_, ?_⟩
        · have := hb.1 s
          simp only [hb']
          split_ifs <;> nlinarith
        · have := hdot (fun _ => 1)
          simp only [mul_one] at this
          rw [this, hb.2]
          ring
      have hsub : W.filter (fun i => ∀ j ∈ W, ∑ s, b' s * g j s ≤ ∑ s, b' s * g i s) ⊆ Arg := by
        intro p hp
        obtain ⟨hpW, hpmax⟩ := Finset.mem_filter.mp hp
        by_contra hpA
        have h1 := hPε p hpW hpA
        have h2 := hpmax j0 hj0W
        rw [hdot, hdot] at h2
        linarith
      have hi0n : i0 ∉ W.filter (fun i => ∀ j ∈ W, ∑ s, b' s * g j s ≤ ∑ s, b' s * g i s) := by
        intro hi0'
        have h2 := (Finset.mem_filter.mp hi0').2 j0 hj0W
        rw [hdot, hdot] at h2
        have he : ∑ s, b s * g i0 s = ∑ s, b s * g j0 s :=
          le_antisymm (hj0max i0 hi0W) (hi0max j0 hj0W)
        rw [he] at h2
        nlinarith
      have hcard := Finset.card_lt_card ⟨hsub, fun h => hi0n (h hi0)⟩
      obtain ⟨q, hq, hqmax, b'', hb'', hq''⟩ := ih b' hb'S (Nat.lt_succ_iff.mp (lt_of_lt_of_le hcard hc))
      refine ⟨q, hq, ?_, b'', hb'', hq''⟩
      have hqA : q ∈ Arg := hsub (Finset.mem_filter.mpr ⟨hq, hqmax⟩)
      exact (Finset.mem_filter.mp hqA).2

open KaelblingPOMDP.Witness in
/-- Value difference of two trees with the same root action, split by observation. -/
theorem kw_diff {S A Ω : Type u} [Fintype S] [Fintype Ω] (M : POMDP S A Ω) {n : ℕ}
    (p q : PolicyTree A Ω (n + 1)) (h : q.1 = p.1) (b : S → ℝ) :
    valueAt M q b - valueAt M p b = ∑ o, ∑ s, b s * (M.γ * ∑ s', M.T s p.1 s' *
      (M.O s' p.1 o * (value M (q.2 o) s' - value M (p.2 o) s'))) := by
  have key : ∀ s, value M q s - value M p s = M.γ * ∑ s', M.T s p.1 s' *
      ∑ o, M.O s' p.1 o * (value M (q.2 o) s' - value M (p.2 o) s') := by
    intro s
    simp only [value]
    rw [h]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  unfold valueAt
  rw [← Finset.sum_sub_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← mul_sub, key s]
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

open KaelblingPOMDP.Witness Classical in
theorem kw_mem_Qset {S A Ω : Type u} [Fintype S] [Fintype Ω] [DecidableEq Ω] [Fintype A]
    (M : POMDP S A Ω) (a : A) (n : ℕ) (q : PolicyTree A Ω (n + 1)) :
    q ∈ Qset M a n ↔ q ∈ candidates M a n ∧ Useful M (candidates M a n) q := by
  unfold Qset usefulSet
  rw [Finset.mem_filter]

open KaelblingPOMDP.Witness Classical in
theorem kw_mem_cand {S A Ω : Type u} [Fintype S] [Fintype Ω] [DecidableEq Ω] [Fintype A]
    (M : POMDP S A Ω) (a : A) (n : ℕ) (p : PolicyTree A Ω (n + 1)) :
    p ∈ candidates M a n ↔ p.1 = a ∧ ∀ o, p.2 o ∈ usefulTrees M n := by
  unfold candidates
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

open KaelblingPOMDP.Witness Finset in
theorem solution {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (a : A) (n : ℕ)
    (U : Finset (PolicyTree A Ω (n + 1))) (hU : U.Nonempty) (hUQ : U ⊆ Qset M a n) :
    (∃ q ∈ Qset M a n, ∀ p ∈ U, value M p ≠ value M q) ↔
      ∃ p ∈ U, ∃ o : Ω, ∃ p' ∈ usefulTrees M n, ∃ b ∈ stdSimplex ℝ S,
        ∀ q ∈ U, valueAt M q b < valueAt M (p.replace o p') b := by
  constructor
  · rintro ⟨q, hqQ, hqU⟩
    rw [kw_mem_Qset] at hqQ
    obtain ⟨hqC, hqUse⟩ := hqQ
    unfold Useful at hqUse
    obtain ⟨-, b, hb, hbq⟩ := hqUse
    obtain ⟨p, hpU, hpmax⟩ := U.exists_max_image (fun p => valueAt M p b) hU
    have hpC := ((kw_mem_Qset M a n p).mp (hUQ hpU)).1
    have hlt : valueAt M p b < valueAt M q b := hbq p hpC (hqU p hpU)
    rw [kw_mem_cand] at hqC hpC
    have hd := kw_diff M p q (hqC.1.trans hpC.1.symm) b
    obtain ⟨o, ho⟩ : ∃ o, 0 < ∑ s, b s * (M.γ * ∑ s', M.T s p.1 s' *
        (M.O s' p.1 o * (value M (q.2 o) s' - value M (p.2 o) s'))) := by
      by_contra hcon
      push_neg at hcon
      have := Finset.sum_nonpos (fun o (_ : o ∈ (Finset.univ : Finset Ω)) => hcon o)
      linarith
    refine ⟨p, hpU, o, q.2 o, hqC.2 o, b, hb, fun q' hq' => ?_⟩
    have hd2 := kw_diff M p (p.replace o (q.2 o)) rfl b
    have hsum : (∑ o', ∑ s, b s * (M.γ * ∑ s', M.T s p.1 s' *
        (M.O s' p.1 o' * (value M ((p.replace o (q.2 o)).2 o') s' - value M (p.2 o') s')))) =
        ∑ s, b s * (M.γ * ∑ s', M.T s p.1 s' *
        (M.O s' p.1 o * (value M (q.2 o) s' - value M (p.2 o) s'))) := by
      rw [Finset.sum_eq_single o]
      · simp [PolicyTree.replace]
      · intro o' _ hne
        simp [PolicyTree.replace, hne]
      · intro h
        exact absurd (Finset.mem_univ o) h
    have hq'p : valueAt M q' b ≤ valueAt M p b := hpmax q' hq'
    linarith
  · rintro ⟨p, hpU, o, p', hp', b, hb, hbeat⟩
    have hpC := ((kw_mem_Qset M a n p).mp (hUQ hpU)).1
    have hpnC : p.replace o p' ∈ candidates M a n := by
      rw [kw_mem_cand] at hpC ⊢
      refine ⟨hpC.1, fun o' => ?_⟩
      show Function.update p.2 o p' o' ∈ usefulTrees M n
      rw [Function.update_apply]
      split_ifs with h
      · exact hp'
      · exact hpC.2 o'
    obtain ⟨q, hqC, hqmax, b', hb', hq'⟩ :=
      kw_perturb_useful (candidates M a n) (fun t => value M t) ⟨_, hpnC⟩ _ b hb le_rfl
    refine ⟨q, (kw_mem_Qset M a n q).mpr ⟨hqC, ?_⟩, fun p0 hp0 heq => ?_⟩
    · unfold Useful
      exact ⟨hqC, b', hb', fun q' hq'' hne => hq' q' hq'' hne⟩
    · have h1 : valueAt M (p.replace o p') b ≤ valueAt M q b := hqmax _ hpnC
      have h2 := hbeat p0 hp0
      have h3 : valueAt M p0 b = valueAt M q b := by
        unfold valueAt
        rw [heq]
      linarith
