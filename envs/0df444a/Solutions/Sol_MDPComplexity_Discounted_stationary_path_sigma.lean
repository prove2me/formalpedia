-- Prove2me | solution 1 for MDPComplexity.Discounted.stationary_path_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:26:10.445648+00:00
-- url     : https://prove2.me/submissions/714c6a9d-8b62-4085-9f7d-06830a76471e

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

open MDPComplexity.Discounted

theorem sps_mod_succ (x p : ℕ) (hp : 0 < p) :
    (x + 1) % p = if x % p + 1 < p then x % p + 1 else 0 := by
  have h1 := Nat.mod_lt x hp
  rw [Nat.add_mod]
  split_ifs with h
  · have : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt h]
  · have he : x % p + 1 = p := by omega
    rcases Nat.lt_or_ge 1 p with h2 | h2
    · rw [Nat.mod_eq_of_lt h2, he, Nat.mod_self]
    · have : p = 1 := by omega
      subst this; simp [Nat.mod_one]

section
variable {S : Type} [Fintype S] [DecidableEq S] {M : DetMDP S} {s₀ : S}

theorem sps_idx0 (P : M.Sigma s₀) : P.arcIdx 0 = 0 := by
  unfold DetMDP.Sigma.arcIdx
  split_ifs with h
  · rfl
  · have : P.j = 0 := by omega
    simp [this]

theorem sps_idx_lt (P : M.Sigma s₀) (t : ℕ) : P.arcIdx t < P.N := by
  have := P.j_lt
  unfold DetMDP.Sigma.arcIdx
  split_ifs with h
  · omega
  · have := Nat.mod_lt (t - P.j) (show 0 < P.N - P.j by omega)
    omega

theorem sps_idx_of_lt (P : M.Sigma s₀) (t : ℕ) (ht : t < P.N) : P.arcIdx t = t := by
  unfold DetMDP.Sigma.arcIdx
  split_ifs with h
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem sps_idx_succ (P : M.Sigma s₀) (t : ℕ) :
    P.arcIdx (t + 1) = if P.arcIdx t + 1 < P.N then P.arcIdx t + 1 else P.j := by
  have hj := P.j_lt
  have hp : 0 < P.N - P.j := by omega
  unfold DetMDP.Sigma.arcIdx
  by_cases h1 : t + 1 < P.j
  · have h2 : t < P.j := by omega
    simp only [if_pos h1, if_pos h2]
    rw [if_pos (by omega)]
  · by_cases h2 : t < P.j
    · have e : t + 1 = P.j := by omega
      simp only [if_neg h1, if_pos h2]
      rw [if_pos (by omega)]
      rw [e, Nat.sub_self, Nat.zero_mod]; omega
    · simp only [if_neg h1, if_neg h2]
      have e : t + 1 - P.j = (t - P.j) + 1 := by omega
      rw [e, sps_mod_succ _ _ hp]
      split_ifs with h3 h4 h4
      · omega
      · omega
      · omega
      · omega
end

def spsTr {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) {s s' : S} (e : s = s')
    (x : M.D s) : M.D s' := e ▸ x

theorem spsTr_next {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) {s s' : S}
    (e : s = s') (x : M.D s) : M.next s' (spsTr M e x) = M.next s x := by subst e; rfl

theorem spsTr_c {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) {s s' : S}
    (e : s = s') (x : M.D s) : M.c s' (spsTr M e x) = M.c s x := by subst e; rfl

noncomputable def spsDelta {S : Type} [Fintype S] [DecidableEq S] {M : DetMDP S} {s₀ : S}
    (P : M.Sigma s₀) : M.Policy := fun s _ =>
  if h : ∃ a, a < P.N ∧ P.w a = s then spsTr M h.choose_spec.2 (P.e h.choose)
  else Classical.arbitrary _

theorem spsDelta_spec {S : Type} [Fintype S] [DecidableEq S] {M : DetMDP S} {s₀ : S}
    (P : M.Sigma s₀) (k : ℕ) (hk : k < P.N) (t : ℕ) :
    M.next (P.w k) (spsDelta P (P.w k) t) = M.next (P.w k) (P.e k) ∧
      M.c (P.w k) (spsDelta P (P.w k) t) = M.c (P.w k) (P.e k) := by
  have h : ∃ a, a < P.N ∧ P.w a = P.w k := ⟨k, hk, rfl⟩
  have ha : h.choose = k := P.distinct _ h.choose_spec.1 _ hk h.choose_spec.2
  unfold spsDelta
  rw [dif_pos h, spsTr_next, spsTr_c]
  exact ⟨congrArg (fun a => M.next (P.w a) (P.e a)) ha, congrArg (fun a => M.c (P.w a) (P.e a)) ha⟩

theorem sps_path_succ {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S)
    (δ : M.Policy) (t : ℕ) :
    M.path s₀ δ (t + 1) = M.next (M.path s₀ δ t) (δ (M.path s₀ δ t) t) := rfl

theorem solution {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S) :
    (∀ δ : M.Policy, M.IsStationary δ →
      ∃ P : M.Sigma s₀, (∀ t ≤ P.N, P.w t = M.path s₀ δ t) ∧
        ∀ β : ℝ, 0 < β ∧ β < 1 → M.discCost β s₀ δ = P.cost β) ∧
    (∀ P : M.Sigma s₀, ∃ δ : M.Policy, M.IsStationary δ ∧
        (∀ t ≤ P.N, M.path s₀ δ t = P.w t) ∧
        ∀ β : ℝ, 0 < β ∧ β < 1 → M.discCost β s₀ δ = P.cost β) := by
  classical
  constructor
  · intro δ hst
    set p := M.path s₀ δ with hpdef
    have hps : ∀ t, p (t + 1) = M.next (p t) (δ (p t) 0) := by
      intro t; rw [hpdef, sps_path_succ, hst]
    obtain ⟨x, y, hxy, hfxy⟩ := Finite.exists_ne_map_eq_of_infinite p
    have hQ : ∃ b, ∃ a < b, p a = p b := by
      rcases Nat.lt_or_gt_of_ne hxy with h | h
      · exact ⟨y, x, h, hfxy⟩
      · exact ⟨x, y, h, hfxy.symm⟩
    obtain ⟨j, hjN, hjp⟩ := Nat.find_spec hQ
    have hmin : ∀ b < Nat.find hQ, ¬ ∃ a < b, p a = p b := fun b hb => Nat.find_min hQ hb
    let P : M.Sigma s₀ :=
      { N := Nat.find hQ
        j := j
        w := p
        e := fun t => δ (p t) 0
        start := rfl
        step := fun t _ => (hps t).symm
        distinct := by
          intro a ha b hb hab
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · exact hmin b hb ⟨a, h, hab⟩
          · exact hmin a ha ⟨b, h, hab.symm⟩
        j_lt := hjN
        closes := hjp.symm }
    have hidx : ∀ t, p t = p (P.arcIdx t) := by
      intro t
      induction t with
      | zero => rw [sps_idx0]
      | succ t ih =>
        rw [sps_idx_succ, hps t, ih]
        have hk := sps_idx_lt P t
        split_ifs with h
        · exact (hps _).symm
        · have e : P.arcIdx t + 1 = P.N := by omega
          rw [← hps, e]
          exact hjp.symm
    refine ⟨P, fun t _ => rfl, fun β _ => ?_⟩
    unfold DetMDP.discCost DetMDP.Sigma.cost
    apply tsum_congr
    intro t
    congr 1
    unfold DetMDP.stageCost DetMDP.Sigma.arcCost
    rw [← hpdef, hst]
    exact congrArg (fun s => M.c s (δ s 0)) (hidx t)
  · intro P
    refine ⟨spsDelta P, fun s t => rfl, ?_⟩
    have hidx : ∀ t, M.path s₀ (spsDelta P) t = P.w (P.arcIdx t) := by
      intro t
      induction t with
      | zero => rw [sps_idx0, P.start]; rfl
      | succ t ih =>
        have hk := sps_idx_lt P t
        rw [sps_path_succ, ih, (spsDelta_spec P _ hk t).1, P.step _ hk, sps_idx_succ]
        split_ifs with h
        · rfl
        · have e : P.arcIdx t + 1 = P.N := by omega
          rw [e, P.closes]
    refine ⟨fun t ht => ?_, fun β _ => ?_⟩
    · rw [hidx]
      rcases Nat.lt_or_ge t P.N with h | h
      · rw [sps_idx_of_lt P t h]
      · have e : t = P.N := by omega
        subst e
        have hj := P.j_lt
        have : P.arcIdx P.N = P.j := by
          unfold DetMDP.Sigma.arcIdx
          rw [if_neg (by omega), Nat.mod_self]; omega
        rw [this, P.closes]
    · unfold DetMDP.discCost DetMDP.Sigma.cost
      apply tsum_congr
      intro t
      congr 1
      unfold DetMDP.stageCost DetMDP.Sigma.arcCost
      rw [hidx]
      exact (spsDelta_spec P _ (sps_idx_lt P t) t).2
