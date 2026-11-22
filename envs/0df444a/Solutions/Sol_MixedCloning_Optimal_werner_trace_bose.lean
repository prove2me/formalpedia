-- Prove2me | solution 1 for MixedCloning.Optimal.werner_trace_bose
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:46:40.304865+00:00
-- url     : https://prove2.me/submissions/7b23f990-1701-4c41-af6c-91ed7dc48c7b

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

section WTB
variable {a : Type} [Fintype a]

/-- `P_p P_q = P_{pq}`. -/
lemma wtb_permMatrix_mul (m : ℕ) (p q : Equiv.Perm (Fin m)) :
    permMatrix (a := a) m p * permMatrix m q = permMatrix m (p * q) := by
  ext i j
  simp only [mul_apply, permMatrix]
  rw [Finset.sum_eq_single (j ∘ q.symm)]
  · rw [if_pos rfl, mul_one]
    rfl
  · intro x _ hx
    rw [if_neg hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `P_p Π = Π`. -/
lemma wtb_perm_mul_symProjector (m : ℕ) (p : Equiv.Perm (Fin m)) :
    permMatrix (a := a) m p * symProjector a m = symProjector a m := by
  unfold symProjector
  rw [Matrix.mul_smul, Matrix.mul_sum]
  simp only [wtb_permMatrix_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft p) (fun q => permMatrix (a := a) m q)

/-- `Π_m² = Π_m`. -/
lemma wtb_symProjector_mul_self (m : ℕ) :
    symProjector a m * symProjector a m = symProjector a m := by
  calc symProjector a m * symProjector a m
      = (((Nat.factorial m : ℂ)⁻¹) • ∑ p : Equiv.Perm (Fin m), permMatrix (a := a) m p) *
          symProjector a m := rfl
    _ = ((Nat.factorial m : ℂ)⁻¹) • ∑ p : Equiv.Perm (Fin m),
          (permMatrix (a := a) m p * symProjector a m) := by
        rw [Matrix.smul_mul, Finset.sum_mul]
    _ = ((Nat.factorial m : ℂ)⁻¹) • ∑ _p : Equiv.Perm (Fin m), symProjector a m := by
        simp only [wtb_perm_mul_symProjector]
    _ = symProjector a m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_smul]

/-- `tr(M P_σ) = Σ_i M_{i, i∘σ⁻¹}`. -/
lemma wtb_trace_mul_perm (m : ℕ) (M : Op (Word a m)) (σ : Equiv.Perm (Fin m)) :
    (M * permMatrix m σ).trace = ∑ i : Word a m, M i (i ∘ σ.symm) := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, permMatrix]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single (i ∘ σ.symm)]
  · rw [if_pos rfl, mul_one]
  · intro x _ hx
    rw [if_neg hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The unnormalised permutation sum `Σ_σ Σ_i M_{i, i∘σ}`. -/
def wtbS (m : ℕ) (M : Op (Word a m)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin m), ∑ i : Word a m, M i (i ∘ σ)

lemma wtb_trace_mul_symProjector (m : ℕ) (M : Op (Word a m)) :
    (M * symProjector a m).trace = ((Nat.factorial m : ℂ))⁻¹ * wtbS m M := by
  unfold symProjector
  rw [Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  congr 1
  simp only [wtb_trace_mul_perm]
  unfold wtbS
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin m))) (fun σ => ∑ i : Word a m, M i (i ∘ σ))

omit [Fintype a] in
lemma wtb_app1_snoc (m : ℕ) (Y : Op (Word a m)) (w : Word a m) (z : a) (j : Word a (m+1)) :
    appendIdentity m 1 Y (Fin.snoc w z) j =
      Y w (Fin.init j) * if z = j (Fin.last m) then 1 else 0 := by
  have h1 : (fun t : Fin m => (Fin.snoc w z : Word a (m+1)) (Fin.castAdd 1 t)) = w := by
    funext t
    exact Fin.snoc_castSucc (α := fun _ => a) (p := w) (x := z) (i := t)
  have h3 : ((fun t : Fin 1 => (Fin.snoc w z : Word a (m+1)) (Fin.natAdd m t)) =
      fun t => j (Fin.natAdd m t)) ↔ z = j (Fin.last m) := by
    have hl : Fin.natAdd m (0 : Fin 1) = Fin.last m := rfl
    constructor
    · intro h
      have := congrFun h 0
      simp only [hl, Fin.snoc_last] at this
      exact this
    · intro h
      funext t
      obtain rfl : t = 0 := Subsingleton.elim _ _
      simp only [hl, Fin.snoc_last]
      exact h
  simp only [appendIdentity]
  rw [h1]
  congr 1
  by_cases h : z = j (Fin.last m)
  · rw [if_pos h, if_pos (h3.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (h3.mp h'))]

lemma wtb_sum_snoc (m : ℕ) (F : Word a (m+1) → ℂ) :
    ∑ i : Word a (m+1), F i = ∑ z : a, ∑ w : Word a m, F (Fin.snoc w z) := by
  calc ∑ i : Word a (m+1), F i = ∑ p : a × Word a m, F (Fin.snoc p.2 p.1) :=
        (Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m+1) => a) F).symm
    _ = ∑ z : a, ∑ w : Word a m, F (Fin.snoc w z) := Fintype.sum_prod_type _

/-- Permutations of `Fin (m+1)` split by the image of the last point (`swap none x * e`). -/
def wtbE (m : ℕ) : Equiv.Perm (Fin (m+1)) ≃ Option (Fin m) × Equiv.Perm (Fin m) :=
  (Equiv.permCongr finSuccEquivLast).trans Equiv.Perm.decomposeOption

lemma wtbE_last (m : ℕ) (x : Option (Fin m)) (e : Equiv.Perm (Fin m)) :
    (wtbE m).symm (x, e) (Fin.last m) = finSuccEquivLast.symm x := by
  simp [wtbE]

lemma wtbE_none_castSucc (m : ℕ) (e : Equiv.Perm (Fin m)) (u : Fin m) :
    (wtbE m).symm (none, e) (Fin.castSucc u) = Fin.castSucc (e u) := by
  simp [wtbE]

lemma wtbE_some_castSucc (m : ℕ) (s : Fin m) (e : Equiv.Perm (Fin m)) (u : Fin m) :
    (wtbE m).symm (some s, e) (Fin.castSucc u) =
      if e u = s then Fin.last m else Fin.castSucc (e u) := by
  by_cases h : e u = s
  · simp [wtbE, h]
  · rw [if_neg h]
    have h' : (some (e u) : Option (Fin m)) ≠ some s := fun h'' => h (Option.some_injective _ h'')
    simp [wtbE, Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none (e u)) h']

lemma wtb_S_none (m : ℕ) (Y : Op (Word a m)) (e : Equiv.Perm (Fin m)) :
    ∑ i : Word a (m+1), appendIdentity m 1 Y i (i ∘ (wtbE m).symm (none, e)) =
      (Fintype.card a : ℂ) * ∑ w : Word a m, Y w (w ∘ e) := by
  rw [wtb_sum_snoc]
  have key : ∀ (z : a) (w : Word a m), appendIdentity m 1 Y (Fin.snoc w z)
      ((Fin.snoc w z : Word a (m+1)) ∘ (wtbE m).symm (none, e)) = Y w (w ∘ e) := by
    intro z w
    rw [wtb_app1_snoc]
    have h1 : Fin.init ((Fin.snoc w z : Word a (m+1)) ∘ (wtbE m).symm (none, e)) = w ∘ e := by
      funext u
      simp only [Fin.init, Function.comp_apply, wtbE_none_castSucc, Fin.snoc_castSucc]
    have h2 : ((Fin.snoc w z : Word a (m+1)) ∘ (wtbE m).symm (none, e)) (Fin.last m) = z := by
      simp only [Function.comp_apply, wtbE_last, finSuccEquivLast_symm_none, Fin.snoc_last]
    rw [h1, h2, if_pos rfl, mul_one]
  simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma wtb_S_some (m : ℕ) (Y : Op (Word a m)) (s : Fin m) (e : Equiv.Perm (Fin m)) :
    ∑ i : Word a (m+1), appendIdentity m 1 Y i (i ∘ (wtbE m).symm (some s, e)) =
      ∑ w : Word a m, Y w (w ∘ e) := by
  rw [wtb_sum_snoc, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [wtb_app1_snoc]
  have h2 : ∀ z : a, ((Fin.snoc w z : Word a (m+1)) ∘ (wtbE m).symm (some s, e)) (Fin.last m) =
      w s := by
    intro z
    simp only [Function.comp_apply, wtbE_last, finSuccEquivLast_symm_some, Fin.snoc_castSucc]
  simp only [h2]
  rw [Finset.sum_eq_single (w s)]
  · rw [if_pos rfl, mul_one]
    congr 1
    funext u
    simp only [Fin.init, Function.comp_apply, wtbE_some_castSucc]
    by_cases h : e u = s
    · rw [if_pos h, Fin.snoc_last, h]
    · rw [if_neg h, Fin.snoc_castSucc]
  · intro z _ hz
    rw [if_neg hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma wtb_S_succ (m : ℕ) (Y : Op (Word a m)) :
    wtbS (m+1) (appendIdentity m 1 Y) = ((Fintype.card a : ℂ) + m) * wtbS m Y := by
  unfold wtbS
  rw [← (wtbE m).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [wtb_S_none, wtb_S_some]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

lemma wtb_step (m : ℕ) (Y : Op (Word a m)) :
    ((m : ℂ) + 1) * (appendIdentity m 1 Y * symProjector a (m+1)).trace =
      ((m : ℂ) + Fintype.card a) * (Y * symProjector a m).trace := by
  rw [wtb_trace_mul_symProjector, wtb_trace_mul_symProjector, wtb_S_succ, Nat.factorial_succ]
  push_cast
  have h1 : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp
  ring

lemma wtb_dim (D m : ℕ) :
    (m + 1) * symDimension D (m+1) = (m + D) * symDimension D m := by
  unfold symDimension
  rcases D with _ | d
  · rcases m with _ | m
    · simp
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega), mul_zero,
        mul_zero]
  · have h1 : m + 1 + (d + 1) - 1 = m + d + 1 := by omega
    have h2 : m + (d + 1) - 1 = m + d := by omega
    have h3 : m + (d + 1) = m + d + 1 := by omega
    rw [h1, h2, h3, Nat.add_one_mul_choose_eq]
    ring

omit [Fintype a] in
lemma wtb_app_zero (n : ℕ) (Y : Op (Word a n)) : appendIdentity n 0 Y = Y := by
  ext i j
  simp only [appendIdentity]
  rw [if_pos (funext (fun t => Fin.elim0 t)), mul_one]
  rfl

omit [Fintype a] in
lemma wtb_fin_split (n k : ℕ) (i j : Word a (n+(k+1))) :
    ((fun t : Fin (k+1) => i (Fin.natAdd n t)) = fun t => j (Fin.natAdd n t)) ↔
      ((fun t : Fin k => i (Fin.castAdd 1 (Fin.natAdd n t))) =
          fun t => j (Fin.castAdd 1 (Fin.natAdd n t))) ∧
      ((fun t : Fin 1 => i (Fin.natAdd (n+k) t)) = fun t => j (Fin.natAdd (n+k) t)) := by
  constructor
  · intro h
    refine ⟨funext fun t => congrFun h (Fin.castSucc t), funext fun t => ?_⟩
    obtain rfl : t = 0 := Subsingleton.elim _ _
    exact congrFun h (Fin.last k)
  · rintro ⟨hB, hC⟩
    funext t
    induction t using Fin.lastCases with
    | last => exact congrFun hC 0
    | cast s => exact congrFun hB s

omit [Fintype a] in
lemma wtb_app_succ (n k : ℕ) (Y : Op (Word a n)) :
    appendIdentity n (k+1) Y = appendIdentity (n+k) 1 (appendIdentity n k Y) := by
  ext i j
  have hs := wtb_fin_split (a := a) n k i j
  simp only [appendIdentity]
  rw [mul_assoc]
  congr 1
  by_cases hB : (fun t : Fin k => i (Fin.castAdd 1 (Fin.natAdd n t))) =
      fun t => j (Fin.castAdd 1 (Fin.natAdd n t))
  · by_cases hC : (fun t : Fin 1 => i (Fin.natAdd (n+k) t)) = fun t => j (Fin.natAdd (n+k) t)
    · rw [if_pos (hs.mpr ⟨hB, hC⟩), if_pos hB, if_pos hC, mul_one]
    · rw [if_neg (fun h => hC (hs.mp h).2), if_neg hC, mul_zero]
  · rw [if_neg (fun h => hB (hs.mp h).1), if_neg hB, zero_mul]

lemma wtb_induct (n k : ℕ) (Y : Op (Word a n)) :
    (symDimension (Fintype.card a) n : ℂ) *
        (appendIdentity n k Y * symProjector a (n+k)).trace =
      (symDimension (Fintype.card a) (n+k) : ℂ) * (Y * symProjector a n).trace := by
  induction k with
  | zero => rw [wtb_app_zero]; rfl
  | succ k ih =>
    have hs := wtb_step (n+k) (appendIdentity n k Y)
    have hd : (((n+k : ℕ) : ℂ) + 1) * (symDimension (Fintype.card a) (n+k+1) : ℂ) =
        (((n+k : ℕ) : ℂ) + Fintype.card a) * (symDimension (Fintype.card a) (n+k) : ℂ) := by
      exact_mod_cast wtb_dim (Fintype.card a) (n+k)
    have h2 : (((n+k : ℕ) : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+k)
    rw [wtb_app_succ]
    show (symDimension (Fintype.card a) n : ℂ) *
        (appendIdentity (n+k) 1 (appendIdentity n k Y) * symProjector a (n+k+1)).trace =
      (symDimension (Fintype.card a) (n+k+1) : ℂ) * (Y * symProjector a n).trace
    apply mul_left_cancel₀ h2
    calc (((n+k : ℕ) : ℂ) + 1) * ((symDimension (Fintype.card a) n : ℂ) *
          (appendIdentity (n+k) 1 (appendIdentity n k Y) * symProjector a (n+k+1)).trace)
        = (symDimension (Fintype.card a) n : ℂ) * ((((n+k : ℕ) : ℂ) + 1) *
          (appendIdentity (n+k) 1 (appendIdentity n k Y) * symProjector a (n+k+1)).trace) := by
          ring
      _ = (symDimension (Fintype.card a) n : ℂ) * ((((n+k : ℕ) : ℂ) + Fintype.card a) *
          (appendIdentity n k Y * symProjector a (n+k)).trace) := by rw [hs]
      _ = (((n+k : ℕ) : ℂ) + Fintype.card a) * ((symDimension (Fintype.card a) n : ℂ) *
          (appendIdentity n k Y * symProjector a (n+k)).trace) := by ring
      _ = (((n+k : ℕ) : ℂ) + Fintype.card a) * ((symDimension (Fintype.card a) (n+k) : ℂ) *
          (Y * symProjector a n).trace) := by rw [ih]
      _ = (((n+k : ℕ) : ℂ) + 1) * ((symDimension (Fintype.card a) (n+k+1) : ℂ) *
          (Y * symProjector a n).trace) := by rw [← mul_assoc, ← hd]; ring

end WTB

theorem solution {a : Type} [Fintype a] (n k : ℕ) (X : Op (Word a n)) :
    (symDimension (Fintype.card a) n : ℂ) *
        (symProjector a (n+k) * appendIdentity n k (symProjector a n * X * symProjector a n) *
          symProjector a (n+k)).trace =
      (symDimension (Fintype.card a) (n+k) : ℂ) *
        (symProjector a n * X * symProjector a n).trace := by
  have hQ : (symProjector a (n+k) * appendIdentity n k (symProjector a n * X * symProjector a n) *
      symProjector a (n+k)).trace =
      (appendIdentity n k (symProjector a n * X * symProjector a n) * symProjector a (n+k)).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, wtb_symProjector_mul_self,
      Matrix.trace_mul_comm]
  have hP : (symProjector a n * X * symProjector a n * symProjector a n).trace =
      (symProjector a n * X * symProjector a n).trace := by
    rw [Matrix.mul_assoc (symProjector a n * X), wtb_symProjector_mul_self]
  rw [hQ, wtb_induct, hP]
