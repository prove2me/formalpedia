-- Prove2me | solution 1 for MarkovMixing.coupling_bound
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:05:53.908715+00:00
-- url     : https://prove2.me/submissions/bf682e4c-a6e2-490d-8942-0ec3ad26dfe3

import Theorems.Thm_MarkovMixing_tv_coupling
import Theorems.Thm_MarkovMixing_dist_le_distPairs
import Definitions.Def_mm_coupling
import Definitions.Def_mm_network
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open MarkovMixing

set_option maxRecDepth 8000

/-- The chain `Q` killed on entering the set `S`. -/
private def killedSet {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) : Matrix W W ℝ :=
  fun a b => if b ∈ S then 0 else Q a b

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

/-- The set-avoidance path sum with a prescribed endpoint is an entry of a power of
the killed chain. -/
private lemma avoidSetAt_eq_killed_pow {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) :
    ∀ (t : ℕ) (p₀ y : W), p₀ ∉ S →
      avoidSetAtProb Q p₀ S y t = ((killedSet Q S) ^ t) p₀ y := by
  classical
  set K := killedSet Q S with hKdef
  have hKval : ∀ a b : W, K a b = if b ∈ S then 0 else Q a b := fun a b => rfl
  intro t
  induction t with
  | zero =>
      intro p₀ y hp₀
      have hL : avoidSetAtProb Q p₀ S y 0
          = ∑ ω : Fin 1 → W, (if ω 0 = p₀ ∧ ω 0 = y then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hcond : (ω 0 = p₀ ∧ (∀ i : Fin 1, ω i ∉ S) ∧ ω (Fin.last 0) = y)
            ↔ (ω 0 = p₀ ∧ ω 0 = y) := by
          constructor
          · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, fun i => ?_, h2⟩
            rw [Subsingleton.elim i 0, h1]
            exact hp₀
        by_cases h : ω 0 = p₀ ∧ ω 0 = y
        · rw [if_pos (hcond.mpr h), if_pos h]
          simp [pathWeight]
        · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
      rw [hL, Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
        (fun ω : Fin 1 → W => if ω 0 = p₀ ∧ ω 0 = y then (1:ℝ) else 0)
        (fun v : W => if v = p₀ ∧ v = y then (1:ℝ) else 0) (fun ω => rfl)]
      rw [pow_zero, Matrix.one_apply]
      by_cases hpy : p₀ = y
      · subst hpy
        rw [if_pos rfl, Finset.sum_eq_single p₀]
        · rw [if_pos ⟨rfl, rfl⟩]
        · intro b _ hb; rw [if_neg (fun hc => hb hc.1)]
        · intro hc; exact absurd (Finset.mem_univ p₀) hc
      · rw [if_neg hpy]
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hpy (h1.symm.trans h2)
  | succ n ih =>
      intro p₀ y hp₀
      have hunfold : avoidSetAtProb Q p₀ S y (n + 1)
          = ∑ ω : Fin (n + 2) → W,
              (if ω 0 = p₀ ∧ (∀ i : Fin (n + 2), ω i ∉ S) ∧
                  ω (Fin.last (n + 1)) = y then pathWeight Q ω else 0) := rfl
      rw [hunfold, ← Equiv.sum_comp (snocEquivV W n)
        (fun ω : Fin (n + 2) → W =>
          if ω 0 = p₀ ∧ (∀ i : Fin (n + 2), ω i ∉ S) ∧
              ω (Fin.last (n + 1)) = y then pathWeight Q ω else 0)]
      have hstep : ∀ p : (Fin (n + 1) → W) × W,
          (if (snocEquivV W n p) 0 = p₀ ∧
              (∀ i : Fin (n + 2), (snocEquivV W n p) i ∉ S) ∧
              (snocEquivV W n p) (Fin.last (n + 1)) = y then
            pathWeight Q (snocEquivV W n p) else 0)
          = (if (p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y) then
              pathWeight Q p.1 * Q (p.1 (Fin.last n)) p.2 else 0) := by
        intro p
        have hrestrict : ∀ i : Fin (n + 1), (snocEquivV W n p) i.castSucc = p.1 i :=
          fun i => snocEquivV_castSucc n p i
        have hlast : (snocEquivV W n p) (Fin.last (n + 1)) = p.2 := snocEquivV_last n p
        have hzero : (snocEquivV W n p) 0 = p.1 0 := by
          have h := hrestrict 0
          rwa [Fin.castSucc_zero] at h
        have hcond : ((snocEquivV W n p) 0 = p₀ ∧
              (∀ i : Fin (n + 2), (snocEquivV W n p) i ∉ S) ∧
              (snocEquivV W n p) (Fin.last (n + 1)) = y)
            ↔ ((p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y)) := by
          constructor
          · rintro ⟨h0, hne, hy⟩
            refine ⟨⟨hzero ▸ h0, fun i => ?_⟩, ?_, hlast ▸ hy⟩
            · rw [← hrestrict i]; exact hne i.castSucc
            · rw [← hlast]; exact hne _
          · rintro ⟨⟨h0, hne⟩, hlz, hy⟩
            refine ⟨hzero ▸ h0, fun i => ?_, hlast ▸ hy⟩
            induction i using Fin.lastCases with
            | last => rw [hlast]; exact hlz
            | cast j => rw [hrestrict j]; exact hne j
        have hweight : pathWeight Q (snocEquivV W n p)
            = pathWeight Q p.1 * Q (p.1 (Fin.last n)) p.2 := by
          have hpw : pathWeight Q (snocEquivV W n p)
              = ∏ i : Fin (n + 1),
                  Q ((snocEquivV W n p) i.castSucc) ((snocEquivV W n p) i.succ) := rfl
          rw [hpw, Fin.prod_univ_castSucc]
          congr 1
          · refine Finset.prod_congr rfl fun i _ => ?_
            rw [hrestrict i.castSucc]
            congr 1
            exact hrestrict i.succ
          · rw [hrestrict (Fin.last n)]
            congr 1
        by_cases h : (p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y)
        · rw [if_pos (hcond.mpr h), if_pos h, hweight]
        · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
      rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
      have hinner : ∀ ω : Fin (n + 1) → W,
          (∑ v : W, if (ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S) ∧ (v ∉ S ∧ v = y) then
              pathWeight Q ω * Q (ω (Fin.last n)) v else 0)
          = (if ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S then
              pathWeight Q ω * K (ω (Fin.last n)) y else 0) := by
        intro ω
        by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S
        · rw [if_pos h]
          by_cases hyS : y ∈ S
          · rw [hKval, if_pos hyS, mul_zero]
            refine Finset.sum_eq_zero fun v _ => ?_
            rw [if_neg]
            rintro ⟨-, hvS, hvy⟩
            exact hvS (hvy ▸ hyS)
          · rw [Finset.sum_eq_single y]
            · rw [if_pos ⟨h, hyS, rfl⟩, hKval, if_neg hyS]
            · intro v _ hv
              rw [if_neg]
              rintro ⟨-, -, hvy⟩
              exact hv hvy
            · intro hc; exact absurd (Finset.mem_univ y) hc
        · rw [if_neg h]
          exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
      rw [Finset.sum_congr rfl fun ω _ => hinner ω]
      rw [pow_succ]
      have hrhs : (K ^ n * K) p₀ y = ∑ w, (K ^ n) p₀ w * K w y := rfl
      rw [hrhs]
      have hexp : ∀ w : W, (K ^ n) p₀ w * K w y
          = ∑ ω : Fin (n + 1) → W,
              (if (ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧ ω (Fin.last n) = w) then
                pathWeight Q ω * K w y else 0) := by
        intro w
        rw [← ih p₀ w hp₀]
        have hun : avoidSetAtProb Q p₀ S w n
            = ∑ ω : Fin (n + 1) → W,
                (if (ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧
                    ω (Fin.last n) = w) then pathWeight Q ω else 0) := rfl
        rw [hun, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧ ω (Fin.last n) = w
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, zero_mul]
      rw [Finset.sum_congr rfl fun w _ => hexp w, Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S
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

/-- The set-avoidance tail probability is the corresponding row sum. -/
private lemma setAvoidTail_eq_rowSum {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) (t : ℕ) (p₀ : W) (hp₀ : p₀ ∉ S) :
    setAvoidTailProb Q p₀ S t = ∑ y, ((killedSet Q S) ^ t) p₀ y := by
  classical
  have hsum : ∑ y, ((killedSet Q S) ^ t) p₀ y = ∑ y, avoidSetAtProb Q p₀ S y t :=
    Finset.sum_congr rfl fun y _ => (avoidSetAt_eq_killed_pow Q S t p₀ y hp₀).symm
  rw [hsum]
  have hexp : ∀ y : W, avoidSetAtProb Q p₀ S y t
      = ∑ ω : Fin (t + 1) → W,
          (if (ω 0 = p₀ ∧ (∀ i : Fin (t + 1), ω i ∉ S) ∧ ω (Fin.last t) = y) then
            pathWeight Q ω else 0) := fun y => rfl
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (t + 1), ω i ∉ S
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

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (Q : V → V → Matrix (V × V) (V × V) ℝ)
    (hQ : ∀ x y : V, IsMarkovianCoupling P (Q x y)) (t : ℕ) :
    (∀ x y : V, tvDist (rowDist P t x) (rowDist P t y) ≤
      setAvoidTailProb (Q x y) (x, y) (pairDiagonal V) t) ∧
    distStationary P π t ≤
      ⨆ p : V × V, setAvoidTailProb (Q p.1 p.2) p (pairDiagonal V) t := by
  classical
  have hdiag_mem : ∀ p : V × V, p ∈ pairDiagonal V ↔ p.1 = p.2 := by
    intro p
    rw [pairDiagonal, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ p, h⟩⟩
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hProw : ∀ (n : ℕ) (a : V), ∑ b, (P ^ n) a b = 1 := by
    intro n
    induction n with
    | zero => intro a; simp [Matrix.one_apply]
    | succ m ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ m * P) a b = ∑ w, (P ^ m) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  -- the main bound, pair by pair
  have hmain : ∀ x y : V, tvDist (rowDist P t x) (rowDist P t y) ≤
      setAvoidTailProb (Q x y) (x, y) (pairDiagonal V) t := by
    intro x y
    obtain ⟨hQstoch, hQm1, hQm2, hQstay⟩ := hQ x y
    set R : Matrix (V × V) (V × V) ℝ := Q x y with hRdef
    set K : Matrix (V × V) (V × V) ℝ := killedSet R (pairDiagonal V) with hKdef
    have hKval : ∀ a b : V × V, K a b = if b ∈ pairDiagonal V then 0 else R a b :=
      fun a b => rfl
    have hRpow_nonneg : ∀ (n : ℕ) (a b : V × V), 0 ≤ (R ^ n) a b := by
      intro n
      induction n with
      | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
      | succ m ih =>
          intro a b
          rw [pow_succ]
          exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hQstoch.1 w b)
    have hRpow_row : ∀ (n : ℕ) (a : V × V), ∑ b, (R ^ n) a b = 1 := by
      intro n
      induction n with
      | zero => intro a; simp [Matrix.one_apply]
      | succ m ih =>
          intro a
          rw [pow_succ]
          have e : ∀ b : V × V, (R ^ m * R) a b = ∑ w, (R ^ m) a w * R w b := fun b => rfl
          rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
          rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hQstoch.2 w, mul_one]]
          exact ih a
    by_cases hxy : x = y
    · -- the two rows coincide, and the coupling starts on the diagonal
      subst hxy
      have hL : tvDist (rowDist P t x) (rowDist P t x) = 0 := by
        have : (fun A : Finset V =>
            |∑ z ∈ A, (rowDist P t x) z - ∑ z ∈ A, (rowDist P t x) z|) = fun _ => (0:ℝ) := by
          funext A; simp
        show (⨆ A : Finset V,
          |∑ z ∈ A, (rowDist P t x) z - ∑ z ∈ A, (rowDist P t x) z|) = 0
        rw [this]
        exact ciSup_const
      have hR0 : setAvoidTailProb R (x, x) (pairDiagonal V) t = 0 := by
        refine Finset.sum_eq_zero fun ω _ => ?_
        rw [if_neg]
        rintro ⟨h0, hne⟩
        exact hne 0 (by rw [h0]; exact (hdiag_mem (x, x)).mpr rfl)
      rw [hL, hR0]
    · -- the genuinely off-diagonal case
      have hp₀ : ((x, y) : V × V) ∉ pairDiagonal V := by
        rw [hdiag_mem]; exact hxy
      -- the `t`-step pair distribution is a coupling of the two rows
      have hmarg1 : ∀ (n : ℕ) (x' : V),
          ∑ y', (R ^ n) (x, y) (x', y') = (P ^ n) x x' := by
        intro n
        induction n with
        | zero =>
            intro x'
            rw [pow_zero, pow_zero]
            by_cases hx : x = x'
            · subst hx
              rw [Matrix.one_apply, if_pos rfl, Finset.sum_eq_single y]
              · rw [Matrix.one_apply, if_pos rfl]
              · intro b _ hb
                rw [Matrix.one_apply, if_neg (by simp [hb.symm])]
              · intro hc; exact absurd (Finset.mem_univ y) hc
            · rw [Matrix.one_apply, if_neg hx]
              refine Finset.sum_eq_zero fun b _ => ?_
              rw [Matrix.one_apply, if_neg (by simp [hx])]
        | succ m ih =>
            intro x'
            rw [pow_succ, pow_succ]
            have e : ∀ b : V × V, (R ^ m * R) (x, y) b = ∑ w, (R ^ m) (x, y) w * R w b :=
              fun b => rfl
            rw [Finset.sum_congr rfl fun y' _ => e (x', y'), Finset.sum_comm]
            have hin : ∀ w : V × V,
                ∑ y', (R ^ m) (x, y) w * R w (x', y') = (R ^ m) (x, y) w * P w.1 x' := by
              intro w
              rw [← Finset.mul_sum, hQm1 w x']
            rw [Finset.sum_congr rfl fun w _ => hin w, Fintype.sum_prod_type]
            have e2 : ∀ u : V, ∑ v, (R ^ m) (x, y) (u, v) * P u x'
                = (P ^ m) x u * P u x' := by
              intro u
              rw [← Finset.sum_mul, ih u]
            rw [Finset.sum_congr rfl fun u _ => e2 u]
            rfl
      have hmarg2 : ∀ (n : ℕ) (y' : V),
          ∑ x', (R ^ n) (x, y) (x', y') = (P ^ n) y y' := by
        intro n
        induction n with
        | zero =>
            intro y'
            rw [pow_zero, pow_zero]
            by_cases hy : y = y'
            · subst hy
              rw [Matrix.one_apply, if_pos rfl, Finset.sum_eq_single x]
              · rw [Matrix.one_apply, if_pos rfl]
              · intro b _ hb
                rw [Matrix.one_apply, if_neg (by simp [hb.symm])]
              · intro hc; exact absurd (Finset.mem_univ x) hc
            · rw [Matrix.one_apply, if_neg hy]
              refine Finset.sum_eq_zero fun b _ => ?_
              rw [Matrix.one_apply, if_neg (by simp [hy])]
        | succ m ih =>
            intro y'
            rw [pow_succ, pow_succ]
            have e : ∀ b : V × V, (R ^ m * R) (x, y) b = ∑ w, (R ^ m) (x, y) w * R w b :=
              fun b => rfl
            rw [Finset.sum_congr rfl fun x' _ => e (x', y'), Finset.sum_comm]
            have hin : ∀ w : V × V,
                ∑ x', (R ^ m) (x, y) w * R w (x', y') = (R ^ m) (x, y) w * P w.2 y' := by
              intro w
              rw [← Finset.mul_sum, hQm2 w y']
            rw [Finset.sum_congr rfl fun w _ => hin w, Fintype.sum_prod_type, Finset.sum_comm]
            have e2 : ∀ v : V, ∑ u, (R ^ m) (x, y) (u, v) * P v y'
                = (P ^ m) y v * P v y' := by
              intro v
              rw [← Finset.sum_mul, ih v]
            rw [Finset.sum_congr rfl fun v _ => e2 v]
            rfl
      have hcoupling : IsCoupling (rowDist P t x) (rowDist P t y)
          (fun p : V × V => (R ^ t) (x, y) p) := by
        refine ⟨⟨fun p => hRpow_nonneg t (x, y) p, ?_⟩, ?_, ?_⟩
        · exact hRpow_row t (x, y)
        · intro x'; exact hmarg1 t x'
        · intro y'; exact hmarg2 t y'
      have hdistx : IsDist (rowDist P t x) := ⟨fun z => hpow_nonneg t x z, hProw t x⟩
      have hdisty : IsDist (rowDist P t y) := ⟨fun z => hpow_nonneg t y z, hProw t y⟩
      have htv := (MarkovMixing.tv_coupling (rowDist P t x) (rowDist P t y)
        hdistx hdisty).1 (fun p : V × V => (R ^ t) (x, y) p) hcoupling
      -- the stay-together convention removes every trajectory that has met
      have hKdiag : ∀ (n : ℕ) (a p : V × V), p ∈ pairDiagonal V →
          a ∉ pairDiagonal V → (K ^ n) a p = 0 := by
        rintro (_ | m) a p hp ha
        · rw [pow_zero, Matrix.one_apply, if_neg (fun hc => ha (by rw [hc]; exact hp))]
        · rw [pow_succ]
          refine Finset.sum_eq_zero fun w _ => ?_
          show (K ^ m) a w * K w p = 0
          rw [hKval, if_pos hp, mul_zero]
      have hstay : ∀ (n : ℕ) (p : V × V), p ∉ pairDiagonal V →
          (R ^ n) (x, y) p = (K ^ n) (x, y) p := by
        intro n
        induction n with
        | zero => intro p _; rfl
        | succ m ih =>
            intro p hp
            rw [pow_succ, pow_succ]
            have eR : (R ^ m * R) (x, y) p = ∑ w, (R ^ m) (x, y) w * R w p := rfl
            have eK : (K ^ m * K) (x, y) p = ∑ w, (K ^ m) (x, y) w * K w p := rfl
            rw [eR, eK]
            refine Finset.sum_congr rfl fun w _ => ?_
            have hKwp : K w p = R w p := by rw [hKval, if_neg hp]
            rw [hKwp]
            by_cases hw : w ∈ pairDiagonal V
            · have hw1 : w.1 = w.2 := (hdiag_mem w).mp hw
              have hzero : R w p = 0 := by
                have := hQstay w.1 p (fun hc => hp ((hdiag_mem p).mpr hc))
                rw [show w = (w.1, w.1) by rw [Prod.ext_iff]; exact ⟨rfl, hw1.symm⟩]
                exact this
              rw [hzero, mul_zero, mul_zero]
            · rw [ih w hw]
      -- assemble
      have hsum_eq : ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2),
            (R ^ t) (x, y) p
          = setAvoidTailProb R (x, y) (pairDiagonal V) t := by
        rw [setAvoidTail_eq_rowSum R (pairDiagonal V) t (x, y) hp₀]
        have hsplit : ∑ p, (K ^ t) (x, y) p
            = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), (K ^ t) (x, y) p := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : p.1 = p.2
          · rw [if_neg (by simpa using hp)]
            exact hKdiag t (x, y) p ((hdiag_mem p).mpr hp) hp₀
          · rw [if_pos hp]
        rw [hsplit]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_filter] at hp
        exact hstay t p (fun hc => hp.2 ((hdiag_mem p).mp hc))
      rw [← hsum_eq]
      exact htv
  refine ⟨hmain, ?_⟩
  -- the uniform bound follows via `d(t) ≤ d̄(t)`
  have hbdd : BddAbove
      (Set.range fun p : V × V => setAvoidTailProb (Q p.1 p.2) p (pairDiagonal V) t) :=
    Set.Finite.bddAbove
      (Set.range fun p : V × V =>
        setAvoidTailProb (Q p.1 p.2) p (pairDiagonal V) t).toFinite
  have hdbar : distPairs P t
      ≤ ⨆ p : V × V, setAvoidTailProb (Q p.1 p.2) p (pairDiagonal V) t := by
    refine ciSup_le fun p => ?_
    exact le_trans (hmain p.1 p.2) (le_ciSup hbdd p)
  exact le_trans (MarkovMixing.dist_le_distPairs P hP π hπ t).1 hdbar
