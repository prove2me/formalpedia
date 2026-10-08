-- Prove2me | solution 1 for KonyaginUnitVectors.Alon.gold_charsum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:38:36.692977+00:00
-- url     : https://prove2.me/submissions/88f2c03a-37fa-409e-8cf1-cb92ccccb14a

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction

set_option autoImplicit false

namespace KonyaginUnitVectors.Alon

/-! ### Algebraic identities of PROOF.md, Lemma 5, Steps 2 and 3 (any field of characteristic 2) -/

section Identities
variable {F : Type*} [Field F]

/-- Step 2: `f(x) + f(x+h) = f(h) + D(x,h)` for `f(x) = a x + b x^3 + c x^5 + x^9`. -/
theorem pk_step2 [CharP F 2] (a b c x h : F) :
    (a * (x + h) + b * (x + h) ^ 3 + c * (x + h) ^ 5 + (x + h) ^ 9) +
        (a * x + b * x ^ 3 + c * x ^ 5 + x ^ 9)
      = (a * h + b * h ^ 3 + c * h ^ 5 + h ^ 9) +
        (b * (x ^ 2 * h + x * h ^ 2) + c * (x ^ 4 * h + x * h ^ 4) + (x ^ 8 * h + x * h ^ 8)) := by
  have h2 : (x + h) ^ 2 = x ^ 2 + h ^ 2 := CharTwo.add_sq x h
  have h4 : (x + h) ^ 4 = x ^ 4 + h ^ 4 := by
    rw [show (x + h) ^ 4 = ((x + h) ^ 2) ^ 2 by ring, h2, CharTwo.add_sq]; ring
  have h8 : (x + h) ^ 8 = x ^ 8 + h ^ 8 := by
    rw [show (x + h) ^ 8 = ((x + h) ^ 4) ^ 2 by ring, h4, CharTwo.add_sq]; ring
  have e3 : (x + h) ^ 3 = (x ^ 2 + h ^ 2) * (x + h) := by rw [← h2]; ring
  have e5 : (x + h) ^ 5 = (x ^ 4 + h ^ 4) * (x + h) := by rw [← h4]; ring
  have e9 : (x + h) ^ 9 = (x ^ 8 + h ^ 8) * (x + h) := by rw [← h8]; ring
  rw [e3, e5, e9]
  have two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (a * x + b * x ^ 3 + c * x ^ 5 + x ^ 9) * two

/-- Step 3: `t(D(x,h)) = t(x^8 P(h))` for any additive `t` with `t(z^2) = t z`. -/
theorem pk_step3 {A : Type*} [AddCommGroup A] (t : F →+ A) (ht : ∀ z, t (z ^ 2) = t z)
    (b c x h : F) :
    t (b * (x ^ 2 * h + x * h ^ 2) + c * (x ^ 4 * h + x * h ^ 4) + (x ^ 8 * h + x * h ^ 8))
      = t (x ^ 8 * (b ^ 4 * h ^ 4 + b ^ 8 * h ^ 16 + c ^ 2 * h ^ 2 + c ^ 8 * h ^ 32 + h + h ^ 64)) := by
  have t4 : ∀ z, t (z ^ 4) = t z := fun z => by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, ht, ht]
  have t8 : ∀ z, t (z ^ 8) = t z := fun z => by
    rw [show z ^ 8 = (z ^ 4) ^ 2 by ring, ht, t4]
  have e1 : t (b * (x ^ 2 * h)) = t (x ^ 8 * (b ^ 4 * h ^ 4)) := by
    rw [← t4 (b * (x ^ 2 * h))]; congr 1; ring
  have e2 : t (b * (x * h ^ 2)) = t (x ^ 8 * (b ^ 8 * h ^ 16)) := by
    rw [← t8 (b * (x * h ^ 2))]; congr 1; ring
  have e3 : t (c * (x ^ 4 * h)) = t (x ^ 8 * (c ^ 2 * h ^ 2)) := by
    rw [← ht (c * (x ^ 4 * h))]; congr 1; ring
  have e4 : t (c * (x * h ^ 4)) = t (x ^ 8 * (c ^ 8 * h ^ 32)) := by
    rw [← t8 (c * (x * h ^ 4))]; congr 1; ring
  have e6 : t (x * h ^ 8) = t (x ^ 8 * h ^ 64) := by
    rw [← t8 (x * h ^ 8)]; congr 1; ring
  have lhs : t (b * (x ^ 2 * h + x * h ^ 2) + c * (x ^ 4 * h + x * h ^ 4) + (x ^ 8 * h + x * h ^ 8))
      = t (b * (x ^ 2 * h)) + t (b * (x * h ^ 2)) + (t (c * (x ^ 4 * h)) + t (c * (x * h ^ 4)))
        + (t (x ^ 8 * h) + t (x * h ^ 8)) := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, ← map_add]
    congr 1; ring
  have rhs : t (x ^ 8 * (b ^ 4 * h ^ 4 + b ^ 8 * h ^ 16 + c ^ 2 * h ^ 2 + c ^ 8 * h ^ 32 + h + h ^ 64))
      = t (x ^ 8 * (b ^ 4 * h ^ 4)) + t (x ^ 8 * (b ^ 8 * h ^ 16)) + (t (x ^ 8 * (c ^ 2 * h ^ 2))
        + t (x ^ 8 * (c ^ 8 * h ^ 32))) + (t (x ^ 8 * h) + t (x ^ 8 * h ^ 64)) := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, ← map_add]
    congr 1; ring
  rw [lhs, rhs, e1, e2, e3, e4, e6]

end Identities

/-! ### Trace and character facts -/

section Char
variable (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- `Tr (z²) = Tr z` (Frobenius invariance of the absolute trace). -/
theorem pk_trace_sq (z : F) :
    Algebra.trace (ZMod 2) F (z ^ 2) = Algebra.trace (ZMod 2) F z := by
  apply (algebraMap (ZMod 2) F).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_trace_eq_sum_pow]
  simp only [Nat.card_zmod]
  have hcard : Fintype.card F = 2 ^ Module.finrank (ZMod 2) F := by
    simpa [ZMod.card] using Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
  have hq : z ^ (2 ^ Module.finrank (ZMod 2) F) = z := by
    have := FiniteField.pow_card z
    rwa [hcard] at this
  have hpos : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
  obtain ⟨m', hm'⟩ : ∃ m', Module.finrank (ZMod 2) F = m' + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm'] at hq ⊢
  rw [Finset.sum_range_succ (fun x => (z ^ 2) ^ 2 ^ x), Finset.sum_range_succ' (fun x => z ^ 2 ^ x)]
  have h2 : z ^ (2 * 2 ^ m') = z := by rw [← pow_succ']; exact hq
  simp only [← pow_mul, pow_succ' 2, pow_zero, pow_one]
  rw [h2]

/-- Nondegeneracy of the trace form. -/
theorem pk_nondeg {a : F} (ha : a ≠ 0) : ∃ b : F, Algebra.trace (ZMod 2) F (a * b) ≠ 0 := by
  have htr := (traceForm_nondegenerate (ZMod 2) F).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

theorem pk_psi_add (y z : F) : psi F (y + z) = psi F y * psi F z := by
  unfold psi
  rw [map_add]
  generalize Algebra.trace (ZMod 2) F y = a
  generalize Algebra.trace (ZMod 2) F z = b
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl <;> simp [h11, h10]

theorem pk_psi_le_one (y : F) : psi F y ≤ 1 := by
  unfold psi; split_ifs <;> norm_num

theorem pk_psi_congr {y z : F} (h : Algebra.trace (ZMod 2) F y = Algebra.trace (ZMod 2) F z) :
    psi F y = psi F z := by
  unfold psi; rw [h]

/-- Lemma 1: `∑_x ψ(x z) = q [z = 0]`. -/
theorem pk_orth [DecidableEq F] (z : F) :
    ∑ x : F, psi F (x * z) = if z = 0 then (Fintype.card F : ℝ) else 0 := by
  by_cases hz : z = 0
  · simp [hz, psi]
  · obtain ⟨b, hb⟩ := pk_nondeg F hz
    have hpsi : psi F (b * z) = -1 := by
      unfold psi; rw [mul_comm, if_neg hb]
    have hS : ∑ x : F, psi F (x * z) = - ∑ x : F, psi F (x * z) :=
      calc ∑ x : F, psi F (x * z) = ∑ x : F, psi F ((x + b) * z) :=
            (Equiv.sum_comp (Equiv.addRight b) (fun x => psi F (x * z))).symm
        _ = ∑ x : F, psi F (x * z) * psi F (b * z) := by simp_rw [add_mul, pk_psi_add]
        _ = - ∑ x : F, psi F (x * z) := by rw [hpsi, ← Finset.sum_mul]; ring
    rw [if_neg hz]
    linarith

/-- `x ↦ x ^ 8` is a bijection of a finite field of characteristic 2. -/
theorem pk_pow8_bij : Function.Bijective (fun x : F => x ^ 8) := by
  have : ExpChar F 2 := ExpChar.prime Nat.prime_two
  have hinj : Function.Injective (fun x : F => x ^ 8) := by
    have := iterateFrobenius_inj F 2 3
    intro x y h
    exact this (by simpa [iterateFrobenius_def] using h)
  exact Finite.injective_iff_bijective.1 hinj

end Char

/-! ### Counting the roots of the linearised polynomial `P` -/

section Count
open Polynomial
variable (F : Type*) [Field F]

theorem pk_count (b c : F)
    [DecidablePred fun h : F => b ^ 4 * h ^ 4 + b ^ 8 * h ^ 16 + c ^ 2 * h ^ 2 + c ^ 8 * h ^ 32 + h
      + h ^ 64 = 0] [Fintype F] :
    (Finset.univ.filter fun h : F =>
      b ^ 4 * h ^ 4 + b ^ 8 * h ^ 16 + c ^ 2 * h ^ 2 + c ^ 8 * h ^ 32 + h + h ^ 64 = 0).card
      ≤ 64 := by
  classical
  set Pp : F[X] := X ^ 64 + C (c ^ 8) * X ^ 32 + C (b ^ 8) * X ^ 16 + C (b ^ 4) * X ^ 4
    + C (c ^ 2) * X ^ 2 + X with hPp
  have hmon : Pp.Monic := by rw [hPp]; monicity!
  have hdeg : Pp.natDegree = 64 := by rw [hPp]; compute_degree!
  have hsub : (Finset.univ.filter fun h : F =>
      b ^ 4 * h ^ 4 + b ^ 8 * h ^ 16 + c ^ 2 * h ^ 2 + c ^ 8 * h ^ 32 + h + h ^ 64 = 0)
      ⊆ Pp.roots.toFinset := by
    intro h hh
    have h0 := (Finset.mem_filter.1 hh).2
    rw [Multiset.mem_toFinset, mem_roots hmon.ne_zero, IsRoot.def]
    simp only [hPp, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    linear_combination h0
  calc _ ≤ Pp.roots.toFinset.card := by convert Finset.card_le_card hsub
    _ ≤ Pp.roots.card := Multiset.toFinset_card_le _
    _ ≤ Pp.natDegree := card_roots' _
    _ = 64 := hdeg

end Count

end KonyaginUnitVectors.Alon

open KonyaginUnitVectors.Alon

theorem solution (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (a b c : F) :
    (∑ x : F, psi F (a * x + b * x ^ 3 + c * x ^ 5 + x ^ 9)) ^ 2 ≤ 64 * (Fintype.card F : ℝ) := by
  classical
  set f : F → F := fun x => a * x + b * x ^ 3 + c * x ^ 5 + x ^ 9 with hf
  set P : F → F := fun h =>
    b ^ 4 * h ^ 4 + b ^ 8 * h ^ 16 + c ^ 2 * h ^ 2 + c ^ 8 * h ^ 32 + h + h ^ 64 with hP
  let t : F →+ ZMod 2 := (Algebra.trace (ZMod 2) F).toAddMonoidHom
  -- Step 3: the character of `D(x,h)` equals that of `x^8 P(h)`
  have hD : ∀ x h : F, psi F (f x + f (x + h)) = psi F (f h) * psi F (x ^ 8 * P h) := by
    intro x h
    have e2 : f x + f (x + h) = f h +
        (b * (x ^ 2 * h + x * h ^ 2) + c * (x ^ 4 * h + x * h ^ 4) + (x ^ 8 * h + x * h ^ 8)) := by
      rw [add_comm]; exact pk_step2 a b c x h
    rw [e2, pk_psi_add]
    congr 1
    exact pk_psi_congr F (pk_step3 t (fun z => pk_trace_sq F z) b c x h)
  -- Step 4: summing over `x`
  have key : ∀ h : F, ∑ x : F, psi F (f x + f (x + h)) =
      psi F (f h) * (if P h = 0 then (Fintype.card F : ℝ) else 0) := by
    intro h
    simp_rw [hD, ← Finset.mul_sum]
    congr 1
    rw [(pk_pow8_bij F).sum_comp (fun u => psi F (u * P h))]
    exact pk_orth F (P h)
  -- Step 1: squaring
  have hsq : (∑ x : F, psi F (f x)) ^ 2 = ∑ h : F, ∑ x : F, psi F (f x + f (x + h)) := by
    rw [sq, Finset.sum_mul_sum]
    simp_rw [← pk_psi_add]
    have hre : ∀ x : F, ∑ y : F, psi F (f x + f y) = ∑ h : F, psi F (f x + f (x + h)) := fun x =>
      (Equiv.sum_comp (Equiv.addLeft x) (fun y => psi F (f x + f y))).symm
    simp_rw [hre]
    exact Finset.sum_comm
  -- Step 5: counting
  have hq : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  show (∑ x : F, psi F (f x)) ^ 2 ≤ 64 * (Fintype.card F : ℝ)
  calc (∑ x : F, psi F (f x)) ^ 2
      = ∑ h : F, psi F (f h) * (if P h = 0 then (Fintype.card F : ℝ) else 0) := by
        rw [hsq]; exact Finset.sum_congr rfl fun h _ => key h
    _ ≤ ∑ h : F, (if P h = 0 then (Fintype.card F : ℝ) else 0) := by
        refine Finset.sum_le_sum fun h _ => ?_
        split_ifs
        · exact mul_le_of_le_one_left hq (pk_psi_le_one F _)
        · simp
    _ = (Fintype.card F : ℝ) * ((Finset.univ.filter fun h : F => P h = 0).card : ℝ) := by
        rw [← Finset.sum_filter]; simp [mul_comm]
    _ ≤ (Fintype.card F : ℝ) * 64 := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        exact_mod_cast pk_count F b c
    _ = 64 * (Fintype.card F : ℝ) := by ring

#print axioms solution
