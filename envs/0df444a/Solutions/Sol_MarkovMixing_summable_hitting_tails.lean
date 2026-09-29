-- Prove2me | solution 1 for MarkovMixing.summable_hitting_tails
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:45:28.922724+00:00
-- url     : https://prove2.me/submissions/c851297a-c4c1-4769-bcc7-7278e5cf8bc2

import Definitions.Def_mm_path
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Lattice.Fold

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
    snocEquivV V n p i.castSucc = p.1 i := by
  show Fin.snoc (α := fun _ => V) p.1 p.2 i.castSucc = p.1 i
  simp

@[simp] private lemma snocEquivV_last {V : Type*} (n : ℕ) (p : (Fin (n + 1) → V) × V) :
    snocEquivV V n p (Fin.last (n + 1)) = p.2 := by
  show Fin.snoc (α := fun _ => V) p.1 p.2 (Fin.last (n + 1)) = p.2
  simp

/-- Total mass surviving `t` steps of the killed chain, started at `a`. -/
private noncomputable def rowSum {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (t : ℕ) (a : V) : ℝ := ∑ y, (M ^ t) a y

private lemma rowSum_def {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (t : ℕ) (a : V) : rowSum M t a = ∑ y, (M ^ t) a y := rfl

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (x z : V) :
    Summable (fun t : ℕ => avoidTailProb P x z t) := by
  classical
  set M := killed P z with hMdef
  have hMval : ∀ a b : V, M a b = if b = z then 0 else P a b := fun a b => rfl
  have hMz : ∀ a : V, M a z = 0 := fun a => by rw [hMval]; simp
  have hM_le : ∀ a b : V, M a b ≤ P a b := by
    intro a b
    rw [hMval]
    by_cases h : b = z
    · rw [if_pos h]; exact hP.1 a b
    · rw [if_neg h]
  have hM_nonneg : ∀ a b : V, 0 ≤ M a b := by
    intro a b
    rw [hMval]
    by_cases h : b = z
    · rw [if_pos h]
    · rw [if_neg h]; exact hP.1 a b
  have hMpow_nonneg : ∀ (t : ℕ) (a b : V), 0 ≤ (M ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hM_nonneg w b)
  have hPpow_nonneg : ∀ (t : ℕ) (a b : V), 0 ≤ (P ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hMpow_le : ∀ (t : ℕ) (a b : V), (M ^ t) a b ≤ (P ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; exact le_refl _
    | succ n ih =>
        intro a b
        rw [pow_succ, pow_succ]
        exact Finset.sum_le_sum fun w _ =>
          mul_le_mul (ih a w) (hM_le w b) (hM_nonneg w b) (hPpow_nonneg n a w)
  have hMpow_z : ∀ (t : ℕ) (a : V), 0 < t → (M ^ t) a z = 0 := by
    rintro (_ | n) a ht
    · omega
    · rw [pow_succ]
      refine Finset.sum_eq_zero fun w _ => ?_
      show (M ^ n) a w * M w z = 0
      rw [hMz w, mul_zero]
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
  -- (C) row sums of the killed chain
  have hrow_nonneg : ∀ (t : ℕ) (a : V), 0 ≤ rowSum M t a := fun t a => by
    rw [rowSum_def]
    exact Finset.sum_nonneg fun y _ => hMpow_nonneg t a y
  have hProw : ∀ (t : ℕ) (a : V), ∑ y, (P ^ t) a y = 1 := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ n * P) a b = ∑ w, (P ^ n) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  have hrow_add : ∀ (t s : ℕ) (a : V), rowSum M (t + s) a = ∑ w, (M ^ t) a w * rowSum M s w := by
    intro t s a
    have e : ∀ y : V, (M ^ (t + s)) a y = ∑ w, (M ^ t) a w * (M ^ s) w y := by
      intro y; rw [pow_add]; rfl
    rw [rowSum_def, Finset.sum_congr rfl fun y _ => e y, Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => by rw [rowSum_def, ← Finset.mul_sum]
  have hrow1 : ∀ a : V, rowSum M 1 a ≤ 1 := by
    intro a
    have h1 : rowSum M 1 a = ∑ y, M a y := by
      rw [rowSum_def, pow_one]
    rw [h1, ← hP.2 a]
    exact Finset.sum_le_sum fun y _ => hM_le a y
  have hrow_le_one : ∀ (t : ℕ) (a : V), rowSum M t a ≤ 1 := by
    intro t
    induction t with
    | zero => intro a; rw [rowSum_def]; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [hrow_add n 1 a]
        calc ∑ w, (M ^ n) a w * rowSum M 1 w
            ≤ ∑ w, (M ^ n) a w * 1 :=
              Finset.sum_le_sum fun w _ =>
                mul_le_mul_of_nonneg_left (hrow1 w) (hMpow_nonneg n a w)
          _ = rowSum M n a := by simp only [mul_one, rowSum]
          _ ≤ 1 := ih a
  have hrow_mono : ∀ (t s : ℕ) (a : V), rowSum M (t + s) a ≤ rowSum M t a := by
    intro t s a
    rw [hrow_add t s a]
    calc ∑ w, (M ^ t) a w * rowSum M s w
        ≤ ∑ w, (M ^ t) a w * 1 :=
          Finset.sum_le_sum fun w _ =>
            mul_le_mul_of_nonneg_left (hrow_le_one s w) (hMpow_nonneg t a w)
      _ = rowSum M t a := by simp only [mul_one, rowSum]
  -- (D) from every state the killed chain leaks mass within a bounded time
  have hchainP : ∀ (a b : ℕ) (u v w : V), (P ^ a) u v * (P ^ b) v w ≤ (P ^ (a + b)) u w := by
    intro a b u v w
    have hsum : (P ^ (a + b)) u w = ∑ q, (P ^ a) u q * (P ^ b) q w := by rw [pow_add]; rfl
    rw [hsum]
    exact Finset.single_le_sum (f := fun q => (P ^ a) u q * (P ^ b) q w)
      (fun q _ => mul_nonneg (hPpow_nonneg a u q) (hPpow_nonneg b q w)) (Finset.mem_univ v)
  have hreach : ∀ a : V, ∃ t : ℕ, 1 ≤ t ∧ 0 < (P ^ t) a z := by
    intro a
    obtain ⟨t₀, ht₀⟩ := hirr a z
    rcases Nat.eq_zero_or_pos t₀ with rfl | hpos
    · -- then `a = z`, and we build a genuine loop at `z`
      rw [pow_zero, Matrix.one_apply] at ht₀
      by_cases haz : a = z
      · subst haz
        obtain ⟨b, -, hb⟩ : ∃ b ∈ (Finset.univ : Finset V), 0 < P a b := by
          by_contra hcon
          push_neg at hcon
          have hle : ∑ b, P a b ≤ 0 := Finset.sum_nonpos fun b hb => hcon b hb
          rw [hP.2 a] at hle
          linarith
        obtain ⟨s, hs⟩ := hirr b a
        refine ⟨1 + s, by omega, ?_⟩
        have h1 : (P ^ 1) a b * (P ^ s) b a ≤ (P ^ (1 + s)) a a := hchainP 1 s a b a
        have hpb : (0:ℝ) < (P ^ 1) a b := by simpa [pow_one] using hb
        nlinarith [mul_pos hpb hs]
      · rw [if_neg haz] at ht₀; linarith
    · exact ⟨t₀, hpos, ht₀⟩
  choose tt htt1 httpos using hreach
  have hleak : ∀ a : V, rowSum M (tt a) a ≤ 1 - (P ^ (tt a)) a z := by
    intro a
    have hz0 : (M ^ (tt a)) a z = 0 := hMpow_z _ a (by have := htt1 a; omega)
    have hsplitM : rowSum M (tt a) a = ∑ y ∈ Finset.univ.erase z, (M ^ (tt a)) a y := by
      rw [rowSum_def, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ z), hz0, add_zero]
    have hsplitP : ∑ y ∈ Finset.univ.erase z, (P ^ (tt a)) a y = 1 - (P ^ (tt a)) a z := by
      have h := Finset.sum_erase_add Finset.univ (fun y => (P ^ (tt a)) a y) (Finset.mem_univ z)
      rw [hProw (tt a) a] at h
      linarith
    rw [hsplitM, ← hsplitP]
    exact Finset.sum_le_sum fun y _ => hMpow_le (tt a) a y
  set T := Finset.univ.sup tt with hTdef
  have hTge : ∀ a : V, tt a ≤ T := fun a => Finset.le_sup (Finset.mem_univ a)
  have hT1 : 1 ≤ T := le_trans (htt1 x) (hTge x)
  have hrowT_lt : ∀ a : V, rowSum M T a < 1 := by
    intro a
    have hmono : rowSum M T a ≤ rowSum M (tt a) a := by
      have hsplit : T = tt a + (T - tt a) := by have := hTge a; omega
      rw [hsplit]
      exact hrow_mono (tt a) (T - tt a) a
    have := hleak a
    have := httpos a
    linarith
  set c := Finset.univ.sup' ⟨x, Finset.mem_univ x⟩ (fun a => rowSum M T a) with hcdef
  have hc_lt : c < 1 := by
    rw [hcdef]
    exact (Finset.sup'_lt_iff _).mpr fun a _ => hrowT_lt a
  have hc_ge : ∀ a : V, rowSum M T a ≤ c := fun a => Finset.le_sup' _ (Finset.mem_univ a)
  have hc_nonneg : 0 ≤ c := le_trans (hrow_nonneg T x) (hc_ge x)
  -- (E) the tail probabilities contract every `T` steps
  have hcontract : ∀ (t : ℕ) (a : V), rowSum M (t + T) a ≤ c * rowSum M t a := by
    intro t a
    rw [hrow_add t T a, rowSum_def M t a, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => by
      rw [mul_comm c ((M ^ t) a w)]
      exact mul_le_mul_of_nonneg_left (hc_ge w) (hMpow_nonneg t a w)
  -- (F) bounded partial sums give summability
  have hSmono : ∀ m : ℕ, ∑ i ∈ Finset.range m, rowSum M i x
      ≤ ∑ i ∈ Finset.range (m + T), rowSum M i x :=
    fun m => Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega)
      (fun i _ _ => hrow_nonneg i x)
  have hbound : ∀ m : ℕ, ∑ i ∈ Finset.range m, rowSum M i x ≤ (T : ℝ) / (1 - c) := by
    intro m
    have hsplit : ∑ i ∈ Finset.range (T + m), rowSum M i x
        = (∑ i ∈ Finset.range T, rowSum M i x) + ∑ i ∈ Finset.range m, rowSum M (T + i) x :=
      Finset.sum_range_add (fun i => rowSum M i x) T m
    have hfirst : ∑ i ∈ Finset.range T, rowSum M i x ≤ (T : ℝ) := by
      calc ∑ i ∈ Finset.range T, rowSum M i x
          ≤ ∑ _i ∈ Finset.range T, (1:ℝ) :=
            Finset.sum_le_sum fun i _ => hrow_le_one i x
        _ = (T : ℝ) := by simp
    have hsecond : ∑ i ∈ Finset.range m, rowSum M (T + i) x
        ≤ c * ∑ i ∈ Finset.range m, rowSum M i x := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Nat.add_comm T i]
      exact hcontract i x
    have hmono2 : ∑ i ∈ Finset.range m, rowSum M i x
        ≤ ∑ i ∈ Finset.range (T + m), rowSum M i x := by
      rw [Nat.add_comm T m]; exact hSmono m
    have hkeyineq : ∑ i ∈ Finset.range (T + m), rowSum M i x
        ≤ (T : ℝ) + c * ∑ i ∈ Finset.range (T + m), rowSum M i x := by
      have hcm : c * ∑ i ∈ Finset.range m, rowSum M i x
          ≤ c * ∑ i ∈ Finset.range (T + m), rowSum M i x :=
        mul_le_mul_of_nonneg_left hmono2 hc_nonneg
      linarith [hsplit, hfirst, hsecond]
    have h1c : 0 < 1 - c := by linarith
    have hfinal : ∑ i ∈ Finset.range (T + m), rowSum M i x ≤ (T : ℝ) / (1 - c) := by
      rw [le_div_iff₀ h1c]
      nlinarith [hkeyineq]
    linarith [hmono2, hfinal]
  have hsummable : Summable (fun t : ℕ => rowSum M t x) :=
    summable_of_sum_range_le (fun n => hrow_nonneg n x) hbound
  have hfun : (fun t : ℕ => avoidTailProb P x z t) = fun t : ℕ => rowSum M t x := by
    funext t
    rw [rowSum_def]
    exact hkeyT t x
  rw [hfun]
  exact hsummable
