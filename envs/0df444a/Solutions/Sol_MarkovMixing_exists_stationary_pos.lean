-- Prove2me | solution 1 for MarkovMixing.exists_stationary_pos
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T14:56:35.90346+00:00
-- url     : https://prove2.me/submissions/b7d3de4f-fe12-4eee-9f0e-485263effc1e

import Theorems.Thm_MarkovMixing_summable_hitting_tails
import Theorems.Thm_MarkovMixing_stationary_unique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators
open MarkovMixing

set_option maxRecDepth 8000

/-- The chain `P` killed on entering `z`. -/
private def killed {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (z : V) : Matrix V V ℝ :=
  fun a b => if b = z then 0 else P a b

/-- Splitting a trajectory of length `n+1` into its first `n` steps and its final state. -/
private def snocEquivV (V : Type*) (n : ℕ) : ((Fin (n + 1) → V) × V) ≃ (Fin (n + 2) → V) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (fun i => ω i.castSucc, ω (Fin.last (n + 1)))
  left_inv := by rintro ⟨q, v⟩; ext <;> simp
  right_inv := by intro ω; exact Fin.snoc_init_self ω

@[simp] private lemma snocEquivV_castSucc {V : Type*} (n : ℕ)
    (p : (Fin (n + 1) → V) × V) (i : Fin (n + 1)) :
    snocEquivV V n p i.castSucc = p.1 i :=
  Fin.snoc_castSucc (α := fun _ => V) p.2 p.1 i

@[simp] private lemma snocEquivV_last {V : Type*} (n : ℕ) (p : (Fin (n + 1) → V) × V) :
    snocEquivV V n p (Fin.last (n + 1)) = p.2 :=
  Fin.snoc_last (α := fun _ => V) p.2 p.1


/-- The endpoint-refined path sum is an entry of a power of the killed chain. -/
private lemma avoidHit_eq_killed_pow {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (z : V) :
    ∀ (t : ℕ) (a y : V), avoidHitProb P a z y t = ((killed P z) ^ t) a y := by
  classical
  set M := killed P z with hMdef
  have hMval : ∀ a b : V, M a b = if b = z then 0 else P a b := fun a b => rfl
  have hMz : ∀ a : V, M a z = 0 := fun a => by rw [hMval]; simp
  -- (A) the endpoint-refined path sum is a matrix entry of the killed chain
  have hkeyH : ∀ (t : ℕ) (a y : V), avoidHitProb P a z y t = (M ^ t) a y := by
    intro t
    induction t with
    | zero =>
        intro a y
        have hL : avoidHitProb P a z y 0
            = ∑ ω : Fin 1 → V, (if ω 0 = a ∧ ω 0 = y then (1:ℝ) else 0) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          have hcond : (ω 0 = a ∧ (∀ i : Fin 1, i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last 0) = y)
              ↔ (ω 0 = a ∧ ω 0 = y) := by
            constructor
            · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1, fun i hi => absurd (Subsingleton.elim i 0) hi, h2⟩
          by_cases h : ω 0 = a ∧ ω 0 = y
          · rw [if_pos (hcond.mpr h), if_pos h]
            simp [pathWeight]
          · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
        rw [hL, Fintype.sum_equiv (Equiv.funUnique (Fin 1) V)
          (fun ω : Fin 1 → V => if ω 0 = a ∧ ω 0 = y then (1:ℝ) else 0)
          (fun v : V => if v = a ∧ v = y then (1:ℝ) else 0) (fun ω => rfl)]
        rw [pow_zero, Matrix.one_apply]
        by_cases hay : a = y
        · subst hay
          rw [if_pos rfl]
          rw [Finset.sum_eq_single a]
          · rw [if_pos ⟨rfl, rfl⟩]
          · intro b _ hb; rw [if_neg (fun hc => hb hc.1)]
          · intro hc; exact absurd (Finset.mem_univ a) hc
        · rw [if_neg hay]
          refine Finset.sum_eq_zero fun v _ => ?_
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact hay (h1.symm.trans h2)
    | succ n ih =>
        intro a y
        have hunfold : avoidHitProb P a z y (n + 1)
            = ∑ ω : Fin (n + 2) → V,
                (if ω 0 = a ∧ (∀ i : Fin (n + 2), i ≠ 0 → ω i ≠ z) ∧
                    ω (Fin.last (n + 1)) = y then pathWeight P ω else 0) := rfl
        rw [hunfold, ← Equiv.sum_comp (snocEquivV V n)
          (fun ω : Fin (n + 2) → V =>
            if ω 0 = a ∧ (∀ i : Fin (n + 2), i ≠ 0 → ω i ≠ z) ∧
                ω (Fin.last (n + 1)) = y then pathWeight P ω else 0)]
        have hstep : ∀ p : (Fin (n + 1) → V) × V,
            (if (snocEquivV V n p) 0 = a ∧
                (∀ i : Fin (n + 2), i ≠ 0 → (snocEquivV V n p) i ≠ z) ∧
                (snocEquivV V n p) (Fin.last (n + 1)) = y then
              pathWeight P (snocEquivV V n p) else 0)
            = (if (p.1 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → p.1 i ≠ z) ∧ (p.2 ≠ z ∧ p.2 = y) then
                pathWeight P p.1 * P (p.1 (Fin.last n)) p.2 else 0) := by
          intro p
          have hrestrict : ∀ i : Fin (n + 1), (snocEquivV V n p) i.castSucc = p.1 i :=
            fun i => snocEquivV_castSucc n p i
          have hlast : (snocEquivV V n p) (Fin.last (n + 1)) = p.2 := snocEquivV_last n p
          have hzero : (snocEquivV V n p) 0 = p.1 0 := by
            have h := hrestrict 0
            rwa [Fin.castSucc_zero] at h
          have hcond : ((snocEquivV V n p) 0 = a ∧
                (∀ i : Fin (n + 2), i ≠ 0 → (snocEquivV V n p) i ≠ z) ∧
                (snocEquivV V n p) (Fin.last (n + 1)) = y)
              ↔ ((p.1 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → p.1 i ≠ z) ∧ (p.2 ≠ z ∧ p.2 = y)) := by
            constructor
            · rintro ⟨h0, hne, hy⟩
              refine ⟨⟨hzero ▸ h0, fun i hi => ?_⟩, ?_, hlast ▸ hy⟩
              · rw [← hrestrict i]
                refine hne i.castSucc ?_
                intro hc
                exact hi (Fin.ext (by
                  have : (i.castSucc : ℕ) = 0 := by rw [hc]; rfl
                  simpa using this))
              · rw [← hlast]
                refine hne _ ?_
                intro hc
                have : ((Fin.last (n + 1)) : ℕ) = 0 := by rw [hc]; rfl
                simp at this
            · rintro ⟨⟨h0, hne⟩, hlz, hy⟩
              refine ⟨hzero ▸ h0, fun i hi => ?_, hlast ▸ hy⟩
              induction i using Fin.lastCases with
              | last => rw [hlast]; exact hlz
              | cast j =>
                  rw [hrestrict j]
                  refine hne j ?_
                  intro hc
                  exact hi (by subst hc; rw [Fin.castSucc_zero])
          have hweight : pathWeight P (snocEquivV V n p)
              = pathWeight P p.1 * P (p.1 (Fin.last n)) p.2 := by
            have hpw : pathWeight P (snocEquivV V n p)
                = ∏ i : Fin (n + 1),
                    P ((snocEquivV V n p) i.castSucc) ((snocEquivV V n p) i.succ) := rfl
            rw [hpw, Fin.prod_univ_castSucc]
            congr 1
            · refine Finset.prod_congr rfl fun i _ => ?_
              rw [hrestrict i.castSucc]
              congr 1
              exact hrestrict i.succ
            · rw [hrestrict (Fin.last n)]
              congr 1
          by_cases h : (p.1 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → p.1 i ≠ z) ∧ (p.2 ≠ z ∧ p.2 = y)
          · rw [if_pos (hcond.mpr h), if_pos h, hweight]
          · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
        rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
        -- collapse the inner sum over the final state
        have hinner : ∀ ω : Fin (n + 1) → V,
            (∑ v : V, if (ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧ (v ≠ z ∧ v = y) then
                pathWeight P ω * P (ω (Fin.last n)) v else 0)
            = (if ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z then
                pathWeight P ω * M (ω (Fin.last n)) y else 0) := by
          intro ω
          by_cases h : ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z
          · rw [if_pos h]
            by_cases hyz : y = z
            · rw [hyz, hMz, mul_zero]
              refine Finset.sum_eq_zero fun v _ => ?_
              rw [if_neg]
              rintro ⟨-, hvz, hvy⟩
              exact hvz hvy
            · rw [Finset.sum_eq_single y]
              · rw [if_pos ⟨h, hyz, rfl⟩, hMval, if_neg hyz]
              · intro v _ hv
                rw [if_neg]
                rintro ⟨-, -, hvy⟩
                exact hv hvy
              · intro hc; exact absurd (Finset.mem_univ y) hc
          · rw [if_neg h]
            exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
        rw [Finset.sum_congr rfl fun ω _ => hinner ω]
        -- and recognise the result as an entry of `M ^ (n+1)`
        rw [pow_succ]
        have hrhs : (M ^ n * M) a y = ∑ w, (M ^ n) a w * M w y := rfl
        rw [hrhs]
        have hexp : ∀ w : V, (M ^ n) a w * M w y
            = ∑ ω : Fin (n + 1) → V,
                (if (ω 0 = a ∧ (∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last n) = w) then
                  pathWeight P ω * M w y else 0) := by
          intro w
          rw [← ih a w]
          have : avoidHitProb P a z w n
              = ∑ ω : Fin (n + 1) → V,
                  (if (ω 0 = a ∧ (∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧
                      ω (Fin.last n) = w) then pathWeight P ω else 0) := rfl
          rw [this, Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases h : ω 0 = a ∧ (∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last n) = w
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, zero_mul]
        rw [Finset.sum_congr rfl fun w _ => hexp w, Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z
        · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last n))]
          · rw [if_pos ⟨h.1, h.2, rfl⟩]
          · intro w _ hw
            rw [if_neg]
            rintro ⟨-, -, hlw⟩
            exact hw hlw.symm
          · intro hc; exact absurd (Finset.mem_univ _) hc
        · rw [if_neg h]
          exact (Finset.sum_eq_zero fun w _ => by
            rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm
  exact hkeyH

/-- The avoidance tail probability is the corresponding row sum of the killed chain. -/
private lemma avoidTail_eq_rowSum {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (z : V) :
    ∀ (t : ℕ) (a : V), avoidTailProb P a z t = ∑ y, ((killed P z) ^ t) a y := by
  classical
  set M := killed P z with hMdef
  have hkeyH : ∀ (t : ℕ) (a y : V), avoidHitProb P a z y t = (M ^ t) a y :=
    avoidHit_eq_killed_pow P z
  -- (B) the tail probability is the corresponding row sum
  have hkeyT : ∀ (t : ℕ) (a : V), avoidTailProb P a z t = ∑ y, (M ^ t) a y := by
    intro t a
    have hsum : ∑ y, (M ^ t) a y = ∑ y, avoidHitProb P a z y t :=
      Finset.sum_congr rfl fun y _ => (hkeyH t a y).symm
    rw [hsum]
    have hexp : ∀ y : V, avoidHitProb P a z y t
        = ∑ ω : Fin (t + 1) → V,
            (if (ω 0 = a ∧ (∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last t) = y) then
              pathWeight P ω else 0) := fun y => rfl
    rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ω 0 = a ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ z
    · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last t))]
      · rw [if_pos ⟨h.1, h.2, rfl⟩]
      · intro y _ hy
        rw [if_neg]
        rintro ⟨-, -, hly⟩
        exact hy hly.symm
      · intro hc; exact absurd (Finset.mem_univ _) hc
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun y _ => by
        rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm
  exact hkeyT

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) :
    ∃ π : V → ℝ, IsStationary P π ∧ (∀ x : V, 0 < π x) ∧
      ∀ x : V, π x * expReturnTime P x = 1 := by
  classical
  have hpow_nonneg : ∀ (n : ℕ) (u b : V), 0 ≤ (P ^ n) u b := by
    intro n
    induction n with
    | zero => intro u b; by_cases hab : u = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro u b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih u w) (hP.1 w b)
  -- for each base point, the normalized Green measure is a positive stationary distribution
  have core : ∀ a : V, ∃ π : V → ℝ, IsStationary P π ∧ (∀ x : V, 0 < π x) ∧
      π a * expReturnTime P a = 1 := by
    intro a
    set M : Matrix V V ℝ := killed P a with hMdef
    have hMval : ∀ u b : V, M u b = if b = a then 0 else P u b := fun u b => rfl
    have hMa : ∀ u : V, M u a = 0 := fun u => by rw [hMval]; simp
    have hM_nonneg : ∀ u b : V, 0 ≤ M u b := by
      intro u b
      rw [hMval]
      by_cases h : b = a
      · rw [if_pos h]
      · rw [if_neg h]; exact hP.1 u b
    have hMpow_nonneg : ∀ (t : ℕ) (u b : V), 0 ≤ (M ^ t) u b := by
      intro t
      induction t with
      | zero => intro u b; by_cases hab : u = b <;> simp [Matrix.one_apply, hab]
      | succ n ih =>
          intro u b
          rw [pow_succ]
          exact Finset.sum_nonneg fun w _ => mul_nonneg (ih u w) (hM_nonneg w b)
    have hMpow_a : ∀ (t : ℕ) (u : V), 0 < t → (M ^ t) u a = 0 := by
      rintro (_ | n) u ht
      · omega
      · rw [pow_succ]
        refine Finset.sum_eq_zero fun w _ => ?_
        show (M ^ n) u w * M w a = 0
        rw [hMa w, mul_zero]
    -- the killed row sums are the avoidance tails, hence summable
    have hf : ∀ t : ℕ, avoidTailProb P a a t = ∑ y, (M ^ t) a y :=
      fun t => avoidTail_eq_rowSum P a t a
    have hfsum : Summable (fun t : ℕ => ∑ y, (M ^ t) a y) := by
      have h := MarkovMixing.summable_hitting_tails P hP hirr a a
      have hfun : (fun t : ℕ => avoidTailProb P a a t) = fun t : ℕ => ∑ y, (M ^ t) a y :=
        funext hf
      rwa [hfun] at h
    have hAsum : ∀ y : V, Summable (fun t : ℕ => (M ^ t) a y) := by
      intro y
      refine Summable.of_nonneg_of_le (fun t => hMpow_nonneg t a y) (fun t => ?_) hfsum
      exact Finset.single_le_sum (f := fun w => (M ^ t) a w)
        (fun w _ => hMpow_nonneg t a w) (Finset.mem_univ y)
    set G : V → ℝ := fun y => ∑' t : ℕ, (M ^ t) a y with hG
    have hGnonneg : ∀ y : V, 0 ≤ G y := fun y =>
      tsum_nonneg fun t => hMpow_nonneg t a y
    -- the Green function at the base point is one
    have hGa : G a = 1 := by
      have hsingle : ∀ b : ℕ, b ≠ 0 → (M ^ b) a a = 0 := by
        intro b hb
        exact hMpow_a b a (Nat.pos_of_ne_zero hb)
      rw [hG]
      show (∑' t : ℕ, (M ^ t) a a) = 1
      rw [tsum_eq_single 0 hsingle]
      simp [Matrix.one_apply]
    -- the total mass is the expected return time
    have hEeq : ∑ y, G y = expReturnTime P a := by
      rw [hG]
      show (∑ y, ∑' t : ℕ, (M ^ t) a y) = expReturnTime P a
      rw [← Summable.tsum_finsetSum (fun y _ => hAsum y)]
      show (∑' t : ℕ, ∑ y, (M ^ t) a y) = ∑' t : ℕ, avoidTailProb P a a t
      exact tsum_congr fun t => (hf t).symm
    have hEge1 : (1:ℝ) ≤ expReturnTime P a := by
      rw [← hEeq]
      have h0 : ∑ y, (M ^ 0) a y = 1 := by simp [Matrix.one_apply]
      have hle : ∑ y, (M ^ 0) a y ≤ ∑' t : ℕ, ∑ y, (M ^ t) a y := by
        refine hfsum.le_tsum 0 fun j _ => ?_
        exact Finset.sum_nonneg fun y _ => hMpow_nonneg j a y
      rw [h0] at hle
      have hswap : ∑' t : ℕ, ∑ y, (M ^ t) a y = ∑ y, ∑' t : ℕ, (M ^ t) a y :=
        Summable.tsum_finsetSum (fun y _ => hAsum y)
      rw [hswap] at hle
      exact hle
    have hEpos : (0:ℝ) < expReturnTime P a := by linarith
    -- the Green function is stationary for `P`
    have hcolM : ∀ y : V, ∑ x, M y x = 1 - P y a := by
      intro y
      have h1 : ∑ x ∈ Finset.univ.erase a, M y x + M y a = ∑ x, M y x :=
        Finset.sum_erase_add _ _ (Finset.mem_univ a)
      have h2 : ∑ x ∈ Finset.univ.erase a, P y x + P y a = ∑ x, P y x :=
        Finset.sum_erase_add _ _ (Finset.mem_univ a)
      have h3 : ∑ x ∈ Finset.univ.erase a, M y x = ∑ x ∈ Finset.univ.erase a, P y x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxa : x ≠ a := Finset.ne_of_mem_erase hx
        rw [hMval, if_neg hxa]
      rw [hMa y, add_zero] at h1
      rw [hP.2 y] at h2
      rw [← h1, h3]
      linarith
    have hstepsum : ∀ t : ℕ,
        ∑ y, (M ^ t) a y * P y a = (∑ y, (M ^ t) a y) - ∑ y, (M ^ (t + 1)) a y := by
      intro t
      have hnext : ∑ x, (M ^ (t + 1)) a x = ∑ y, (M ^ t) a y * (1 - P y a) := by
        have e : ∀ x : V, (M ^ (t + 1)) a x = ∑ y, (M ^ t) a y * M y x := by
          intro x; rw [pow_succ]; rfl
        rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => by rw [← Finset.mul_sum, hcolM y]
      rw [hnext]
      rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) =>
        (by ring : (M ^ t) a y * (1 - P y a) = (M ^ t) a y - (M ^ t) a y * P y a)]
      rw [Finset.sum_sub_distrib]
      ring
    have hGstat : ∀ x : V, ∑ y, G y * P y x = G x := by
      intro x
      have hswap : ∑ y, G y * P y x = ∑' t : ℕ, ∑ y, (M ^ t) a y * P y x := by
        have h1 : ∀ y : V, G y * P y x = ∑' t : ℕ, (M ^ t) a y * P y x := by
          intro y
          rw [hG]
          exact ((hAsum y).tsum_mul_right (P y x)).symm
        rw [Finset.sum_congr rfl fun y _ => h1 y]
        exact (Summable.tsum_finsetSum (fun y _ => (hAsum y).mul_right (P y x))).symm
      rw [hswap]
      by_cases hxa : x = a
      · rw [hxa]
        have hterm : ∀ t : ℕ, ∑ y, (M ^ t) a y * P y a
            = (∑ y, (M ^ t) a y) - ∑ y, (M ^ (t + 1)) a y := hstepsum
        rw [tsum_congr hterm]
        have hshift : Summable (fun t : ℕ => ∑ y, (M ^ (t + 1)) a y) :=
          (summable_nat_add_iff 1).mpr hfsum
        rw [hfsum.tsum_sub hshift]
        have hsplit : ∑' t : ℕ, ∑ y, (M ^ t) a y
            = (∑ y, (M ^ 0) a y) + ∑' t : ℕ, ∑ y, (M ^ (t + 1)) a y :=
          hfsum.tsum_eq_zero_add
        have h0 : ∑ y, (M ^ 0) a y = 1 := by simp [Matrix.one_apply]
        rw [h0] at hsplit
        rw [hGa]
        linarith
      · have hterm : ∀ t : ℕ, ∑ y, (M ^ t) a y * P y x = (M ^ (t + 1)) a x := by
          intro t
          have e : (M ^ (t + 1)) a x = ∑ y, (M ^ t) a y * M y x := by
            rw [pow_succ]; rfl
          rw [e]
          exact Finset.sum_congr rfl fun y _ => by rw [hMval, if_neg hxa]
        rw [tsum_congr hterm, hG]
        show (∑' t : ℕ, (M ^ (t + 1)) a x) = ∑' t : ℕ, (M ^ t) a x
        have hsplit : ∑' t : ℕ, (M ^ t) a x
            = (M ^ 0) a x + ∑' t : ℕ, (M ^ (t + 1)) a x := (hAsum x).tsum_eq_zero_add
        have h0 : (M ^ 0) a x = 0 := by
          rw [pow_zero, Matrix.one_apply, if_neg (fun hc : a = x => hxa hc.symm)]
        rw [h0, zero_add] at hsplit
        exact hsplit.symm
    -- normalize
    refine ⟨fun y => G y / expReturnTime P a, ⟨⟨fun y => ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · exact div_nonneg (hGnonneg y) hEpos.le
    · show ∑ y, G y / expReturnTime P a = 1
      simp only [div_eq_mul_inv, ← Finset.sum_mul, hEeq]
      exact mul_inv_cancel₀ hEpos.ne'
    · funext x
      show ∑ y, G y / expReturnTime P a * P y x = G x / expReturnTime P a
      have hrw : ∀ y : V, G y / expReturnTime P a * P y x
          = (G y * P y x) / expReturnTime P a := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => hrw y]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [hGstat x]
    · -- strict positivity, propagated by irreducibility
      intro x
      show 0 < G x / expReturnTime P a
      have hstat : IsStationary P (fun y => G y / expReturnTime P a) := by
        refine ⟨⟨fun y => div_nonneg (hGnonneg y) hEpos.le, ?_⟩, ?_⟩
        · show ∑ y, G y / expReturnTime P a = 1
          simp only [div_eq_mul_inv, ← Finset.sum_mul, hEeq]
          exact mul_inv_cancel₀ hEpos.ne'
        · funext w
          show ∑ y, G y / expReturnTime P a * P y w = G w / expReturnTime P a
          have hrw : ∀ y : V, G y / expReturnTime P a * P y w
              = (G y * P y w) / expReturnTime P a := fun y => by ring
          rw [Finset.sum_congr rfl fun y _ => hrw y]
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
          rw [hGstat w]
      have hstat_pow : ∀ n : ℕ,
          Matrix.vecMul (fun y => G y / expReturnTime P a) (P ^ n)
            = fun y => G y / expReturnTime P a := by
        intro n
        induction n with
        | zero => simp
        | succ m ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hstat.2]
      have hbase : 0 < G a / expReturnTime P a := by
        rw [hGa]
        positivity
      obtain ⟨n, hn⟩ := hirr a x
      have hval : G x / expReturnTime P a
          = ∑ w, G w / expReturnTime P a * (P ^ n) w x :=
        (congrFun (hstat_pow n) x).symm
      have hterm : G a / expReturnTime P a * (P ^ n) a x
          ≤ ∑ w, G w / expReturnTime P a * (P ^ n) w x :=
        Finset.single_le_sum (f := fun w => G w / expReturnTime P a * (P ^ n) w x)
          (fun w _ => mul_nonneg (div_nonneg (hGnonneg w) hEpos.le) (hpow_nonneg n w x))
          (Finset.mem_univ a)
      have hpos : 0 < G a / expReturnTime P a * (P ^ n) a x := mul_pos hbase hn
      rw [hval]
      linarith
    · show G a / expReturnTime P a * expReturnTime P a = 1
      rw [hGa, div_mul_cancel₀ _ hEpos.ne']
  -- assemble, using uniqueness to transport the identity to every state
  obtain ⟨π, hstat, hpos, -⟩ := core (Classical.arbitrary V)
  refine ⟨π, hstat, hpos, ?_⟩
  intro x
  obtain ⟨πx, hstatx, -, hidx⟩ := core x
  have heq : πx = π := MarkovMixing.stationary_unique P hP hirr πx π hstatx hstat
  rw [← heq]
  exact hidx
