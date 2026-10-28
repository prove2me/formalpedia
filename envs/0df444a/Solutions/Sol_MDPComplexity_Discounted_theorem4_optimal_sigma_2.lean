-- Prove2me | solution 2 for MDPComplexity.Discounted.theorem4_optimal_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:06.645972+00:00
-- url     : https://prove2.me/submissions/950f3cef-7c17-46a4-b731-134e5b155e60

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model
import Theorems.Thm_MDPComplexity_Discounted_B_cheapest_walk
import Theorems.Thm_MDPComplexity_Discounted_exists_stationary_optimal

-- carved verbatim out of submission bee178fe-6437-4cac-939e-0aee9e8b8c66, lines 488-633

section
open MDPComplexity.Discounted Tropical
variable {S : Type} [Fintype S] [DecidableEq S]

def bwTr (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) : M.D s' := e ▸ x

theorem bwTr_next (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.next s' (bwTr M e x) = M.next s x := by subst e; rfl

theorem bwTr_c (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.c s' (bwTr M e x) = M.c s x := by subst e; rfl

end

section
open MDPComplexity.Discounted Tropical
open MDPComplexity.Discounted Finset Filter
variable {S : Type} [Fintype S] [DecidableEq S]

def lidx (j N t : ℕ) : ℕ := if t < j then t else j + (t - j) % (N - j)

theorem lidx_lt {j N : ℕ} (h : j < N) (t : ℕ) : lidx j N t < N := by
  unfold lidx; split_ifs with h1
  · omega
  · have := Nat.mod_lt (t - j) (show 0 < N - j by omega); omega

theorem lidx_zero (j N : ℕ) : lidx j N 0 = 0 := by
  unfold lidx; split_ifs with h
  · rfl
  · have : j = 0 := by omega
    subst this; simp

theorem lidx_succ {j N : ℕ} (h : j < N) (t : ℕ) :
    lidx j N (t+1) = if lidx j N t + 1 = N then j else lidx j N t + 1 := by
  by_cases h1 : t + 1 < j
  · simp only [lidx, if_pos h1, if_pos (show t < j by omega)]
    rw [if_neg (by omega)]
  · by_cases h2 : t < j
    · have e : t + 1 = j := by omega
      unfold lidx; rw [if_neg h1, if_pos h2]
      rw [e, Nat.sub_self, Nat.zero_mod, Nat.add_zero]
      split_ifs <;> rfl
    · unfold lidx; rw [if_neg h1, if_neg h2]
      have hL : 0 < N - j := by omega
      set L := N - j with hLd
      set m := (t - j) % L with hm
      have hmL : m < L := Nat.mod_lt _ hL
      have hdec := Nat.mod_add_div (t - j) L
      have e : t + 1 - j = (m + 1) + L * ((t - j) / L) := by rw [← hm] at hdec; omega
      rw [e, Nat.add_mul_mod_self_left]
      by_cases hc : m + 1 = L
      · rw [hc, Nat.mod_self, if_pos (by omega)]; rfl
      · rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]; rfl

theorem lser (β : ℝ) (hβ : 0 < β ∧ β < 1) (a : ℕ → ℝ) (j N : ℕ) (hj : j < N) :
    ∑' t, β ^ t * a (lidx j N t) = ∑ t ∈ range j, β ^ t * a t +
      β ^ j / (1 - β ^ (N - j)) * ∑ t ∈ range (N - j), β ^ t * a (j + t) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  set L := N - j with hLdef
  have hL : 0 < L := by omega
  haveI : NeZero L := ⟨hL.ne'⟩
  set C : ℝ := ∑ r ∈ range N, |a r| with hC
  have hidx : ∀ t, lidx j N t < N := lidx_lt hj
  have hbound : ∀ r, r < N → |a r| ≤ C := by
    intro r hr
    exact Finset.single_le_sum (f := fun r => |a r|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 hr)
  have hgeo : Summable (fun t : ℕ => β ^ t * C) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_right C
  have hsumm : ∀ g : ℕ → ℕ, (∀ t, g t < N) → Summable (fun t : ℕ => β ^ t * a (g t)) := by
    intro g hg
    refine Summable.of_norm_bounded hgeo ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hbound _ (hg t)) (pow_pos hβ0 t).le
  have hf := hsumm _ hidx
  rw [← hf.sum_add_tsum_nat_add j]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    simp [lidx, ht]
  · have hshift : ∀ u, lidx j N (u + j) = j + u % L := by
      intro u
      unfold lidx
      rw [if_neg (by omega)]
      congr 2; omega
    simp only [hshift, pow_add]
    have hg2 : ∀ u, j + u % L < N := by
      intro u; have := Nat.mod_lt u hL; omega
    have e1 : (fun u => β ^ u * β ^ j * a (j + u % L)) =
        fun u => β ^ j * (β ^ u * a (j + u % L)) := by
      funext u; ring
    rw [e1, tsum_mul_left]
    set A := ∑ t ∈ range L, β ^ t * a (j + t) with hA
    have hs2 := hsumm (fun u => j + u % L) hg2
    have hre : ∑' u, β ^ u * a (j + u % L) = ∑' q : ℕ, (β ^ L) ^ q * A := by
      rw [← (Nat.divModEquiv L).symm.tsum_eq]
      have hs3 : Summable (fun p : ℕ × Fin L =>
          β ^ ((Nat.divModEquiv L).symm p) * a (j + ((Nat.divModEquiv L).symm p) % L)) :=
        (Nat.divModEquiv L).symm.summable_iff.2 hs2
      rw [hs3.tsum_prod' (fun q => (hasSum_fintype _).summable)]
      congr 1
      funext q
      rw [tsum_fintype, hA, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [Nat.divModEquiv_symm_apply]
      have : (q * L + (r : ℕ)) % L = r := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
      rw [this, show β ^ (q * L + (r : ℕ)) = (β ^ L) ^ q * β ^ (r : ℕ) by
        rw [pow_add, mul_comm q L, pow_mul]]
      ring
    rw [hre, tsum_mul_right, tsum_geometric_of_lt_one (pow_nonneg hβ0.le _)
      (pow_lt_one₀ hβ0.le hβ1 hL.ne')]
    ring

noncomputable def folPol (M : DetMDP S) (x : ℕ → S) (d : (t : ℕ) → M.D (x t)) : M.Policy :=
  fun s t => if h : x t = s then bwTr M h (d t) else Classical.arbitrary _

theorem folPol_next (M : DetMDP S) (x : ℕ → S) (d : (t : ℕ) → M.D (x t)) (t : ℕ) (s : S)
    (h : x t = s) : M.next s (folPol M x d s t) = M.next (x t) (d t) := by
  subst h
  rw [show folPol M x d (x t) t = bwTr M rfl (d t) from dif_pos rfl, bwTr_next]

theorem folPol_c (M : DetMDP S) (x : ℕ → S) (d : (t : ℕ) → M.D (x t)) (t : ℕ) (s : S)
    (h : x t = s) : M.c s (folPol M x d s t) = M.c (x t) (d t) := by
  subst h
  rw [show folPol M x d (x t) t = bwTr M rfl (d t) from dif_pos rfl, bwTr_c]

theorem folPol_path (M : DetMDP S) (s₀ : S) (x : ℕ → S) (d : (t : ℕ) → M.D (x t))
    (h0 : x 0 = s₀) (hstep : ∀ t, M.next (x t) (d t) = x (t+1)) :
    ∀ t, M.path s₀ (folPol M x d) t = x t := by
  intro t
  induction t with
  | zero => exact h0.symm
  | succ t ih =>
    show M.next (M.path s₀ (folPol M x d) t) (folPol M x d (M.path s₀ (folPol M x d) t) t) = _
    rw [folPol_next M x d t _ ih.symm]
    exact hstep t

theorem las_disc (M : DetMDP S) (s₀ : S) (β : ℝ) (x : ℕ → S) (d : (t : ℕ) → M.D (x t))
    (j N : ℕ) (hj : j < N) (h0 : x 0 = s₀) (hstep : ∀ t < N, M.next (x t) (d t) = x (t+1))
    (hcl : x N = x j) : ∃ δ : M.Policy,
      M.discCost β s₀ δ = ∑' t, β ^ t * M.c (x (lidx j N t)) (d (lidx j N t)) := by
  have hy0 : x (lidx j N 0) = s₀ := by rw [lidx_zero]; exact h0
  have hys : ∀ t, M.next (x (lidx j N t)) (d (lidx j N t)) = x (lidx j N (t+1)) := by
    intro t
    rw [hstep _ (lidx_lt hj t), lidx_succ hj t]
    split_ifs with h
    · rw [h, hcl]
    · rfl
  refine ⟨folPol M (fun t => x (lidx j N t)) (fun t => d (lidx j N t)), ?_⟩
  unfold DetMDP.discCost
  congr 1; funext t
  unfold DetMDP.stageCost
  rw [folPol_c M (fun t => x (lidx j N t)) (fun t => d (lidx j N t)) t _
    (folPol_path M s₀ _ _ hy0 hys t).symm]

def catW (M : DetMDP S) {k l : ℕ} {u v w : S} (W1 : M.Walk k u v) (W2 : M.Walk l v w) :
    ℕ → S := fun t => if t < k then W1.w t else W2.w (t - k)

def catE (M : DetMDP S) {k l : ℕ} {u v w : S} (W1 : M.Walk k u v) (W2 : M.Walk l v w) :
    (t : ℕ) → M.D (catW M W1 W2 t) := fun t =>
  if h : t < k then bwTr M (by unfold catW; rw [if_pos h]) (W1.e t)
  else bwTr M (by unfold catW; rw [if_neg h]) (W2.e (t - k))

theorem catE_n1 (M : DetMDP S) {k l : ℕ} {u v w : S} (W1 : M.Walk k u v) (W2 : M.Walk l v w)
    (t : ℕ) (h : t < k) : M.next (catW M W1 W2 t) (catE M W1 W2 t) = M.next (W1.w t) (W1.e t) := by
  simp only [catE, dif_pos h, bwTr_next]

theorem catE_n2 (M : DetMDP S) {k l : ℕ} {u v w : S} (W1 : M.Walk k u v) (W2 : M.Walk l v w)
    (t : ℕ) (h : ¬ t < k) : M.next (catW M W1 W2 t) (catE M W1 W2 t) =
      M.next (W2.w (t - k)) (W2.e (t - k)) := by
  simp only [catE, dif_neg h, bwTr_next]

theorem catE_c1 (M : DetMDP S) {k l : ℕ} {u v w : S} (W1 : M.Walk k u v) (W2 : M.Walk l v w)
    (t : ℕ) (h : t < k) : M.c (catW M W1 W2 t) (catE M W1 W2 t) = M.c (W1.w t) (W1.e t) := by
  simp only [catE, dif_pos h, bwTr_c]

theorem catE_c2 (M : DetMDP S) {k l : ℕ} {u v w : S} (W1 : M.Walk k u v) (W2 : M.Walk l v w)
    (r : ℕ) : M.c (catW M W1 W2 (k + r)) (catE M W1 W2 (k + r)) = M.c (W2.w r) (W2.e r) := by
  simp only [catE, dif_neg (show ¬ k + r < k by omega), bwTr_c]
  rw [Nat.add_sub_cancel_left]

theorem cat_step (M : DetMDP S) {k l : ℕ} {u v w : S} (W1 : M.Walk k u v) (W2 : M.Walk l v w)
    (t : ℕ) (ht : t < k + l) :
    M.next (catW M W1 W2 t) (catE M W1 W2 t) = catW M W1 W2 (t + 1) := by
  by_cases h : t < k
  · rw [catE_n1 M W1 W2 t h, W1.step t h]
    by_cases h' : t + 1 < k
    · simp only [catW, if_pos h']
    · have e : t + 1 = k := by omega
      simp only [catW, e, Nat.sub_self, W2.start]
      simpa using W1.finish
  · rw [catE_n2 M W1 W2 t h, W2.step _ (by omega)]
    simp only [catW, if_neg (show ¬ t + 1 < k by omega)]
    congr 1; omega

end

section
open MDPComplexity.Discounted Tropical
open MDPComplexity.Discounted Finset Filter

theorem solution {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    IsLeast {x : ℝ | ∃ P : M.Sigma s₀, x = P.cost β} (M.optDisc β s₀) ∧
    IsLeast {x : ℝ | ∃ (u : S) (k l : ℕ) (lam mu : ℝ),
        k ≤ Fintype.card S ∧ 1 ≤ l ∧ l ≤ Fintype.card S ∧
        M.B β k s₀ u = Tropical.trop (lam : WithTop ℝ) ∧
        M.B β l u u = Tropical.trop (mu : WithTop ℝ) ∧
        x = lam + β ^ k * mu / (1 - β ^ l)} (M.optDisc β s₀) := by
  classical
  obtain ⟨δs, hst, hδs⟩ := MDPComplexity.Discounted.exists_stationary_optimal M s₀ β hβ
  haveI : Nonempty M.Policy := ⟨δs⟩
  have hopt : M.optDisc β s₀ = M.discCost β s₀ δs := by
    apply le_antisymm
    · exact ciInf_le ⟨M.discCost β s₀ δs, by rintro _ ⟨δ, rfl⟩; exact hδs δ⟩ δs
    · exact le_ciInf hδs
  have hsig : ∀ P : M.Sigma s₀, M.optDisc β s₀ ≤ P.cost β := by
    intro P
    obtain ⟨δ, hδ⟩ := las_disc M s₀ β P.w P.e P.j P.N P.j_lt P.start P.step P.closes
    rw [hopt]
    calc M.discCost β s₀ δs ≤ M.discCost β s₀ δ := hδs δ
      _ = P.cost β := hδ
  have hlas : ∀ (u : S) (k l : ℕ) (W1 : M.Walk k s₀ u) (W2 : M.Walk l u u), 1 ≤ l →
      M.optDisc β s₀ ≤ W1.cost β + β ^ k * W2.cost β / (1 - β ^ l) := by
    intro u k l W1 W2 hl
    have h0 : catW M W1 W2 0 = s₀ := by
      unfold catW
      split_ifs with h
      · exact W1.start
      · have : k = 0 := by omega
        subst this
        rw [Nat.zero_sub, W2.start, ← W1.finish, W1.start]
    have hcl : catW M W1 W2 (k + l) = catW M W1 W2 k := by
      unfold catW
      rw [if_neg (by omega), if_neg (lt_irrefl k), Nat.add_sub_cancel_left, Nat.sub_self,
        W2.finish, W2.start]
    obtain ⟨δ, hδ⟩ := las_disc M s₀ β (catW M W1 W2) (catE M W1 W2) k (k + l) (by omega) h0
      (cat_step M W1 W2) hcl
    rw [lser β hβ (fun r => M.c (catW M W1 W2 r) (catE M W1 W2 r)) k (k + l) (by omega)] at hδ
    have e1 : ∑ t ∈ range k, β ^ t * M.c (catW M W1 W2 t) (catE M W1 W2 t) = W1.cost β := by
      unfold DetMDP.Walk.cost
      apply Finset.sum_congr rfl
      intro t ht
      rw [catE_c1 M W1 W2 t (Finset.mem_range.1 ht)]
    have e2 : ∑ t ∈ range (k + l - k), β ^ t * M.c (catW M W1 W2 (k + t))
        (catE M W1 W2 (k + t)) = W2.cost β := by
      rw [Nat.add_sub_cancel_left]
      unfold DetMDP.Walk.cost
      apply Finset.sum_congr rfl
      intro t _
      rw [catE_c2]
    try simp only at hδ
    rw [e1, e2, Nat.add_sub_cancel_left] at hδ
    rw [hopt]
    calc M.discCost β s₀ δs ≤ M.discCost β s₀ δ := hδs δ
      _ = _ := by rw [hδ]; ring
  have hB : ∀ (k : ℕ) (a b : S) (W : M.Walk k a b), ∃ lam : ℝ,
      M.B β k a b = Tropical.trop (lam : WithTop ℝ) ∧ lam ≤ W.cost β := by
    intro k a b W
    obtain ⟨x, hx, hl⟩ := (MDPComplexity.Discounted.B_cheapest_walk M β hβ k a b).2 W
    exact ⟨x, hx, hl.2 ⟨W, rfl⟩⟩
  have hW : ∀ (k : ℕ) (a b : S) (lam : ℝ), M.B β k a b = Tropical.trop (lam : WithTop ℝ) →
      ∃ W : M.Walk k a b, W.cost β = lam := by
    intro k a b lam h
    have hne : ¬ IsEmpty (M.Walk k a b) := by
      rw [← (MDPComplexity.Discounted.B_cheapest_walk M β hβ k a b).1, h]
      intro h2
      have := congrArg Tropical.untrop h2
      simp at this
    rw [not_isEmpty_iff] at hne
    obtain ⟨W⟩ := hne
    obtain ⟨x, hx, hl⟩ := (MDPComplexity.Discounted.B_cheapest_walk M β hβ k a b).2 W
    rw [h] at hx
    have hlx : lam = x := by
      have := congrArg Tropical.untrop hx
      simpa using this
    obtain ⟨W', hW'⟩ := hl.1
    exact ⟨W', hW'.trans hlx.symm⟩
  set x : ℕ → S := M.path s₀ δs with hx
  have hQ : ∃ n, ∃ i < n, x n = x i := by
    obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card S + 1) => x i) (by simp)
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with h | h
    · exact ⟨b, a, h, he.symm⟩
    · exact ⟨a, b, h, he⟩
  set N := Nat.find hQ with hN
  obtain ⟨j, hjN, hcl⟩ := Nat.find_spec hQ
  have hdist : ∀ a < N, ∀ b < N, x a = x b → a = b := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exfalso; have := Nat.find_min' hQ ⟨a, h, hab.symm⟩; omega
    · exact h
    · exfalso; have := Nat.find_min' hQ ⟨b, h, hab⟩; omega
  let P : M.Sigma s₀ := ⟨N, j, x, fun t => δs (x t) t, rfl, fun t _ => rfl, hdist, hjN, hcl⟩
  have hNc : N ≤ Fintype.card S := by
    have := Fintype.card_le_of_injective (fun i : Fin N => x i)
      (fun a b h => Fin.ext (hdist a a.isLt b b.isLt h))
    simpa using this
  have hs : ∀ a, x (a+1) = M.next (x a) (δs (x a) 0) := fun a => by
    show M.next (x a) (δs (x a) a) = _
    rw [hst (x a) a]
  have hper : ∀ t, x (lidx j N t) = x t := by
    intro t
    induction t with
    | zero => rw [lidx_zero]
    | succ t ih =>
      rw [lidx_succ hjN t]
      have : x (if lidx j N t + 1 = N then j else lidx j N t + 1) = x (lidx j N t + 1) := by
        split_ifs with h
        · rw [h, hcl]
        · rfl
      rw [this, hs, hs, ih]
  have hPc : P.cost β = M.discCost β s₀ δs := by
    unfold DetMDP.Sigma.cost DetMDP.discCost
    congr 1; funext t
    show β ^ t * M.c (x (lidx j N t)) (δs (x (lidx j N t)) (lidx j N t)) =
      β ^ t * M.c (x t) (δs (x t) t)
    rw [hst (x (lidx j N t)) (lidx j N t), hst (x t) t, hper t]
  refine ⟨⟨⟨P, by rw [hPc, hopt]⟩, ?_⟩, ?_⟩
  · rintro _ ⟨Q, rfl⟩; exact hsig Q
  let W1 : M.Walk j s₀ (x j) := ⟨x, fun t => δs (x t) t, rfl, rfl, fun t _ => rfl⟩
  let W2 : M.Walk (N - j) (x j) (x j) := ⟨fun t => x (j + t), fun t => δs (x (j+t)) (j+t), rfl,
    by show x (j + (N - j)) = x j; rw [Nat.add_sub_cancel' hjN.le]; exact hcl, fun t _ => rfl⟩
  obtain ⟨lam, hlam, hlamle⟩ := hB j s₀ (x j) W1
  obtain ⟨mu, hmu, hmule⟩ := hB (N - j) (x j) (x j) W2
  have hcost : P.cost β = W1.cost β + β ^ j / (1 - β ^ (N - j)) * W2.cost β :=
    lser β hβ (fun r => M.c (x r) (δs (x r) r)) j N hjN
  have hpos : 0 < β ^ j / (1 - β ^ (N - j)) := div_pos (pow_pos hβ.1 _)
    (by have := pow_lt_one₀ hβ.1.le hβ.2 (show N - j ≠ 0 by omega); linarith)
  have hx0le : lam + β ^ j * mu / (1 - β ^ (N - j)) ≤ M.optDisc β s₀ := by
    rw [hopt, ← hPc, hcost]
    have e : β ^ j * mu / (1 - β ^ (N - j)) = β ^ j / (1 - β ^ (N - j)) * mu := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hmule hpos.le]
  have hge : M.optDisc β s₀ ≤ lam + β ^ j * mu / (1 - β ^ (N - j)) := by
    obtain ⟨V1, hV1⟩ := hW _ _ _ lam hlam
    obtain ⟨V2, hV2⟩ := hW _ _ _ mu hmu
    have := hlas (x j) j (N - j) V1 V2 (by omega)
    rwa [hV1, hV2] at this
  refine ⟨⟨x j, j, N - j, lam, mu, by omega, by omega, by omega, hlam, hmu,
    le_antisymm hge hx0le⟩, ?_⟩
  rintro _ ⟨u, k, l, lam', mu', hk, hl1, hl2, hB1, hB2, rfl⟩
  obtain ⟨V1, hV1⟩ := hW k s₀ u lam' hB1
  obtain ⟨V2, hV2⟩ := hW l u u mu' hB2
  have := hlas u k l V1 V2 hl1
  rwa [hV1, hV2] at this

end
