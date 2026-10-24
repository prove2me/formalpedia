-- Prove2me | solution 1 for OAI.RationalHitting.ExecutableGenerator.implementation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:21:37.002317+00:00
-- url     : https://prove2.me/submissions/d96ff619-0d15-4812-be5f-d02c2295227c

import Mathlib
import Definitions.Def_RationalHitting
import Definitions.Def_OAIQWRHT004
import Theorems.Thm_OAI_RationalHitting_Generator_list_hits

section
-- module Solutions.OAIQW_RationalHitting.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.CyclotomicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.CyclotomicRing
open Polynomial Matrix Module
noncomputable section

lemma basis_apply (e : ℕ) (i : Fin (degree e)) :
    basis e i = AdjoinRoot.root (modulus e)^i.val := by
  rw [basis,Basis.reindex_apply]
  exact (powerBasis e).basis_eq_pow _

end
end RationalHitting.CyclotomicRing


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

lemma grid_length (H : ℕ) : (grid H).length = H^3 := by
  simp [grid,List.length_flatMap,pow_succ,Nat.mul_assoc]

lemma length_output_le (n N e H : ℕ) : (output n N e H).tuples.length ≤ H^3 :=
  (List.length_filterMap_le _ _).trans_eq (grid_length H)

end
end RationalHitting.Generator

namespace RationalHitting.Parameters

theorem threshold_pos (n s : ℕ) : 0 < B s * delta n s := by
  simp only [B,delta,w]
  positivity

theorem M_le (n s : ℕ) : M n s ≤ 2*(B s*delta n s) := by
  unfold M
  rw [pow_succ]
  have h := Nat.pow_log_le_self 2 (threshold_pos n s).ne'
  unfold exponent
  omega

theorem w_bound (n s : ℕ) : w n ≤ n+s+1 := by unfold w; omega

theorem B_bound (n s : ℕ) : B s ≤ 2*(n+s+1) := by unfold B; omega

theorem delta_bound (n s : ℕ) : delta n s ≤ 4*(n+s+1)^4 := by
  calc delta n s ≤ 2*(n+s+1)^3*(2*(n+s+1)) := by
         unfold delta
         gcongr
         · exact w_bound n s
         · exact B_bound n s
       _ = _ := by ring

theorem polynomial_M (n s : ℕ) : M n s ≤ 16*(n+s+1)^5 := by
  calc M n s ≤ 2*(B s*delta n s) := M_le n s
       _ ≤ 2*((2*(n+s+1))*(4*(n+s+1)^4)) := by
          gcongr
          · exact B_bound n s
          · exact delta_bound n s
       _ = _ := by ring

theorem polynomial_H (n s : ℕ) (hn : 1 ≤ n) : H n s ≤ 24577*(n+s+1)^17 := by
  have hp : 1 ≤ (n+s+1)^17 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc H n s ≤ 1+3*(n+s+1)*(2*(n+s+1))*(16*(n+s+1)^5)^3 := by
         unfold H
         apply Nat.add_le_add_left
         apply Nat.mul_le_mul
         · apply Nat.mul_le_mul
           · exact Nat.mul_le_mul_left 3 (by omega)
           · exact B_bound n s
         · exact Nat.pow_le_pow_left (polynomial_M n s) 3
       _ = 1+24576*(n+s+1)^17 := by ring
       _ ≤ _ := by omega

end RationalHitting.Parameters

namespace RationalHitting.Generator
noncomputable section

theorem list_dimension_bound (n s : ℕ) : (list n s).dimension ≤ 256*(n+s+1)^10 := by
  have hd : CyclotomicRing.degree (Parameters.exponent n s) ≤ Parameters.M n s := by
    unfold CyclotomicRing.degree Parameters.M
    exact Nat.pow_le_pow_right (by omega) (by omega)
  change Parameters.M n s * CyclotomicRing.degree (Parameters.exponent n s) ≤ _
  calc _ ≤ (16*(n+s+1)^5)*(16*(n+s+1)^5) :=
             Nat.mul_le_mul (Parameters.polynomial_M n s) (hd.trans (Parameters.polynomial_M n s))
       _ = _ := by ring

theorem list_length_bound (n s : ℕ) (hn : 1 ≤ n) :
    (list n s).tuples.length ≤ 24577^3*(n+s+1)^51 := by
  calc _ ≤ (Parameters.H n s)^3 := length_output_le ..
       _ ≤ (24577*(n+s+1)^17)^3 := Nat.pow_le_pow_left (Parameters.polynomial_H n s hn) 3
       _ = _ := by rw [mul_pow,← pow_mul]

end
end RationalHitting.Generator

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.IntegralLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.CyclotomicRing
open Polynomial Matrix Module
noncomputable section

lemma root_degree (e : ℕ) : AdjoinRoot.root (modulus e)^degree e = -1 := by
  have h := AdjoinRoot.eval₂_root (modulus e)
  change Polynomial.eval₂ (AdjoinRoot.of (modulus e)) (AdjoinRoot.root (modulus e))
    ((X : ℚ[X])^degree e+1) = 0 at h
  rw [Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_one] at h
  exact eq_neg_of_add_eq_zero_left h

lemma root_pow_reduce (e k : ℕ) :
    AdjoinRoot.root (modulus e)^k = (-1 : R e)^(k/degree e) *
      (basis e ⟨k % degree e,Nat.mod_lt _ (degree_pos e)⟩) := by
  rw [basis_apply,← root_degree,← pow_mul,← pow_add]
  congr 1
  change k = degree e*(k/degree e)+k%degree e
  exact (Nat.div_add_mod k (degree e)).symm

/-- Every regular-representation entry of a cyclotomic monomial is 0 or ±1.
This also gives an explicit integral computation with a division and remainder. -/
lemma rho_root_pow (e k : ℕ) (i j : Fin (degree e)) :
    rho e (AdjoinRoot.root (modulus e)^k) i j =
      if (k+j.val) % degree e = i.val then (-1 : ℚ)^((k+j.val)/degree e) else 0 := by
  rw [rho,Algebra.leftMulMatrix_eq_repr_mul,basis_apply,← pow_add,root_pow_reduce]
  rw [show (-1 : R e)^((k+j.val)/degree e) =
      algebraMap ℚ (R e) ((-1 : ℚ)^((k+j.val)/degree e)) by simp]
  rw [← Algebra.smul_def, map_smul, Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply]
  simp only [smul_eq_mul,mul_ite,mul_one,mul_zero]
  congr 1
  exact propext ⟨fun h => congrArg Fin.val h,fun h => Fin.ext h⟩

lemma rho_character (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) :
    rho e (character e a) i j =
      if (a.val+j.val) % degree e = i.val then (-1 : ℚ)^((a.val+j.val)/degree e) else 0 := by
  rw [character,AddChar.zmodChar_apply,rho_root_pow]

lemma rho_character_integral (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) :
    rho e (character e a) i j = (signedEntry e a i j : ℚ) := by
  simp only [rho_character,signedEntry,Int.cast_ite,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_zero]

lemma signedEntry_abs (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) :
    |signedEntry e a i j| ≤ 1 := by
  unfold signedEntry
  split_ifs <;> simp [abs_pow]

end
end RationalHitting.CyclotomicRing


namespace RationalHitting.IntegralTest
open Polynomial Matrix
open scoped BigOperators

lemma coeff_bound (a : ℤ) (w M k j : ℕ) (hw : 1 ≤ w) (ha : |a| ≤ w) (hk : k ≤ M) :
    |(((X+C a)^k : ℤ[X]).coeff j)| ≤ (2*w : ℤ)^M := by
  rw [coeff_X_add_C_pow,abs_mul,abs_pow,Int.abs_natCast]
  have hw' : (1 : ℤ) ≤ w := by exact_mod_cast hw
  have hc : (k.choose j : ℤ) ≤ (2 : ℤ)^M := by
    exact_mod_cast (Nat.choose_le_two_pow k j).trans (Nat.pow_le_pow_right (by omega) hk)
  calc |a|^(k-j)*(k.choose j : ℤ) ≤ (w : ℤ)^M * (2 : ℤ)^M := by
         apply mul_le_mul _ hc (by positivity) (by positivity)
         exact (pow_le_pow_left₀ (abs_nonneg a) ha (k-j)).trans (pow_le_pow_right₀ hw' (Nat.sub_le k j |>.trans hk))
       _ = _ := by rw [← mul_pow]; congr 1; ring

lemma full_bound (M : ℕ) (a t : ℤ) (w H : ℕ) (hw : 1 ≤ w) (hH : 1 ≤ H)
    (ha : |a| ≤ w) (ht : |t| ≤ H) (i j : Fin M) :
    |full M a t i j| ≤ (M : ℤ)*(2*w : ℤ)^(2*M)*(H : ℤ)^M := by
  unfold full
  simp_rw [← coeff_X_add_C_pow]
  calc |∑ r : Fin M, _| ≤ ∑ r : Fin M, |(((X+C (-a))^r.rev.val : ℤ[X]).coeff i.val) *
          (((X+C a)^j.val : ℤ[X]).coeff r.val) * t^r.val| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _r : Fin M, (2*w : ℤ)^(2*M)*(H : ℤ)^M := by
         apply Finset.sum_le_sum
         intro r _
         rw [abs_mul,abs_mul,abs_pow]
         have hh : (1 : ℤ) ≤ H := by exact_mod_cast hH
         calc _ ≤ ((2*w : ℤ)^M*(2*w : ℤ)^M)*(H : ℤ)^M := by
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · apply mul_le_mul (coeff_bound (-a) w M _ _ hw (by simpa using ha) (Nat.le_of_lt r.rev.isLt))
                    (coeff_bound a w M _ _ hw ha (Nat.le_of_lt j.isLt)) (abs_nonneg _) (by positivity)
                · exact (pow_le_pow_left₀ (abs_nonneg t) ht r.val).trans (pow_le_pow_right₀ hh (Nat.le_of_lt r.isLt))
              _ = _ := by rw [← pow_add]; simp [two_mul]
       _ = _ := by simp [mul_assoc]

lemma padded_bound (M N : ℕ) (a t : ℤ) (w H : ℕ) (hw : 1 ≤ w) (hH : 1 ≤ H)
    (ha : |a| ≤ w) (ht : |t| ≤ H) (i j : Fin M) :
    |padded M N a t i j| ≤ (M : ℤ)*(2*w : ℤ)^(2*M)*(H : ℤ)^M := by
  by_cases h : j.val < N
  · simpa [padded,h] using full_bound M a t w H hw hH ha ht i j
  · simp only [padded,h,ite_false,abs_zero]; positivity

end RationalHitting.IntegralTest


namespace RationalHitting.IntegralTest
open Matrix Polynomial
open scoped BigOperators

lemma full_cast {K : Type*} [Field K] (M : ℕ) (a t : ℤ) (i j : Fin M) :
    Polynomial.eval (t : K) (TestPolynomial.full M (a : K) i j) =
      (full M a t i j : K) := by
  simp only [TestPolynomial.full,full,coeff_X_add_C_pow,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_natCast]

lemma padded_cast {K : Type*} [Field K] (M N : ℕ) (a t : ℤ) (i j : Fin M) :
    Polynomial.eval (t : K) (TestPolynomial.padded M N (a : K) i j) =
      (padded M N a t i j : K) := by
  by_cases h : j.val < N
  · simpa [TestPolynomial.padded,padded,h] using full_cast M a t i j (K := K)
  · simp [TestPolynomial.padded,padded,h]

end RationalHitting.IntegralTest

namespace RationalHitting.ThreeLift
open Polynomial MvPolynomial Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]

lemma eval_uni (x : Fin 3 → K) (p : K[X]) : MvPolynomial.eval x (uni p) = Polynomial.eval (x 0) p := by
  have he : (MvPolynomial.eval x).comp uni = Polynomial.evalRingHom (x 0) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [uni]
    · simp [uni]
  exact DFunLike.congr_fun he p

lemma eval_lift (χ : AddChar (ZMod d) K) (R : Matrix (ZMod d) (ZMod d) K[X])
    (x : Fin 3 → K) (i j : ZMod d) :
    MvPolynomial.eval x (lift χ R i j) =
      (d : K)⁻¹ * ∑ a : ZMod d, ∑ b : ZMod d, ∑ k : ZMod d,
        χ (-a*k)*Polynomial.eval (x 0) (R k (k-b)) * QuantumMatrices.weyl χ a b i j *
          (x 1)^a.val*(x 2)^b.val := by
  simp only [lift,map_sum,map_mul,map_pow,eval_uni,MvPolynomial.eval_C,MvPolynomial.eval_X,coeffP,
    Polynomial.eval_C]
  simp only [Finset.mul_sum,Finset.sum_mul]
  congr 1
  ext a
  congr 1
  ext b
  congr 1
  ext k
  ring

end
end RationalHitting.ThreeLift

namespace RationalHitting.IntegralLift
open _root_.OAI.RationalHitting.CyclotomicRing Matrix
open scoped BigOperators
noncomputable section

lemma entry_bound (e : ℕ) (T : Matrix (ZMod (dimension e)) (ZMod (dimension e)) ℤ)
    (p r : ℤ) (A H : ℕ) (hT : ∀ i j, |T i j| ≤ A) (hH : 1 ≤ H)
    (hp : |p| ≤ H) (hr : |r| ≤ H) (u v : ZMod (dimension e)) (i j : Fin (degree e)) :
    |entry e T p r u v i j| ≤ (dimension e : ℤ)^3*A*(H : ℤ)^(2*dimension e) := by
  have hH' : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hterm (a b k : ZMod (dimension e)) :
      |(if u=v+b then T k (k-b)*signedEntry e (-a*k+a*u) i j*p^a.val*r^b.val else 0)| ≤
        (A : ℤ)*(H : ℤ)^(2*dimension e) := by
    split_ifs
    · simp only [abs_mul,abs_pow]
      calc _ ≤ ((A : ℤ)*1*(H : ℤ)^dimension e)*(H : ℤ)^dimension e := by
               apply mul_le_mul _ _ (by positivity) (by positivity)
               · apply mul_le_mul _ _ (by positivity) (by positivity)
                 · exact mul_le_mul (hT _ _) (signedEntry_abs ..) (abs_nonneg _) (by positivity)
                 · exact (pow_le_pow_left₀ (abs_nonneg p) hp a.val).trans
                     (pow_le_pow_right₀ hH' (Nat.le_of_lt a.val_lt))
               · exact (pow_le_pow_left₀ (abs_nonneg r) hr b.val).trans
                   (pow_le_pow_right₀ hH' (Nat.le_of_lt b.val_lt))
           _ = _ := by rw [mul_one,mul_assoc,← pow_add]; simp [two_mul]
    · simp only [abs_zero]; positivity
  unfold entry
  calc |∑ a : ZMod (dimension e), _| ≤ ∑ a : ZMod (dimension e), |∑ b : ZMod (dimension e), _| :=
          Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ a : ZMod (dimension e), ∑ b : ZMod (dimension e), ∑ k : ZMod (dimension e),
          (A : ℤ)*(H : ℤ)^(2*dimension e) := by
         apply Finset.sum_le_sum
         intro a _
         apply (Finset.abs_sum_le_sum_abs _ _).trans
         apply Finset.sum_le_sum
         intro b _
         exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => hterm a b k))
       _ = _ := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]; ring

end
end RationalHitting.IntegralLift

namespace RationalHitting.IntegralLift
open Matrix _root_.OAI.RationalHitting.CyclotomicRing Polynomial
open scoped BigOperators
noncomputable section

lemma rho_rat_mul (e : ℕ) (q : ℚ) (z : R e) (i j : Fin (degree e)) :
    rho e (algebraMap ℚ (R e) q * z) i j = q * rho e z i j := by
  rw [← Algebra.smul_def, map_smul, Matrix.smul_apply, smul_eq_mul]

lemma rho_div_nat (e : ℕ) (z : R e) (i j : Fin (degree e)) :
    (dimension e : ℚ) * rho e ((dimension e : R e)⁻¹*z) i j = rho e z i j := by
  have hc : (dimension e : R e)⁻¹ = algebraMap ℚ (R e) ((dimension e : ℚ)⁻¹) := by simp
  have hd : (dimension e : ℚ) ≠ 0 := by exact_mod_cast (dimension_pos e).ne'
  rw [hc,rho_rat_mul,← mul_assoc,mul_inv_cancel₀ hd,one_mul]

lemma entry_spec (e : ℕ)
    (P : Matrix (ZMod (dimension e)) (ZMod (dimension e)) (R e)[X])
    (T : Matrix (ZMod (dimension e)) (ZMod (dimension e)) ℤ) (t p r : ℤ)
    (hT : ∀ u v, Polynomial.eval (t : R e) (P u v) = (T u v : R e))
    (u v : ZMod (dimension e)) (i j : Fin (degree e)) :
    (entry e T p r u v i j : ℚ) = (dimension e : ℚ) *
      rho e (MvPolynomial.eval ![(t : R e),(p : R e),(r : R e)]
        (ThreeLift.lift (character e) P u v)) i j := by
  rw [ThreeLift.eval_lift,rho_div_nat]
  simp only [entry,Int.cast_sum,map_sum,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,hT,
    QuantumMatrices.weyl]
  by_cases h : u = v+b
  · simp only [ite_eq_left h]
    have he : character e (-a*k)*(T k (k-b) : R e)*character e (a*u)*
        (p : R e)^a.val*(r : R e)^b.val =
        algebraMap ℚ (R e) ((T k (k-b)*p^a.val*r^b.val : ℤ) : ℚ) *
          character e (-a*k+a*u) := by
      rw [AddChar.map_add_eq_mul]
      simp only [map_mul,map_pow,map_intCast,Int.cast_mul,Int.cast_pow]
      ring
    change ((T k (k-b)*signedEntry e (-a*k+a*u) i j*p^a.val*r^b.val : ℤ) : ℚ) =
      rho e (character e (-a*k)*(T k (k-b) : R e)*character e (a*u)*
        (p : R e)^a.val*(r : R e)^b.val) i j
    rw [he,rho_rat_mul,rho_character_integral]
    simp only [Int.cast_mul,Int.cast_pow]
    ring
  · simp [h]

end
end RationalHitting.IntegralLift

namespace RationalHitting.Generator
open Matrix
open scoped BigOperators
noncomputable section

lemma regular_apply (e : ℕ)
    (A : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) (CyclotomicRing.R e))
    (i j : Fin (D e)) : regular e A i j = CyclotomicRing.rho e
      (A ((coordinate e).symm i).1 ((coordinate e).symm j).1)
      ((coordinate e).symm i).2 ((coordinate e).symm j).2 := rfl

lemma U_cast (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) :
    (U n N e x a).map (Int.castRingHom ℚ) = (CyclotomicRing.dimension e : ℚ) • Z n N e x a := by
  ext i j
  change (U n N e x a i j : ℚ) = (CyclotomicRing.dimension e : ℚ) * regular e (Zring n N e x a) i j
  rw [regular_apply]
  unfold U
  have hh := IntegralLift.entry_spec e
    (PencilDeformation.test (CyclotomicRing.dimension e) N (a.val : CyclotomicRing.R e))
    (integerTest N e (a.val : ℤ) (x 0 : ℤ)) (x 0 : ℤ) (x 1 : ℤ) (x 2 : ℤ)
    (fun u v => by
      simp only [PencilDeformation.test,integerTest,Matrix.reindex_apply]
      simpa only [Int.cast_natCast,Matrix.submatrix_apply] using IntegralTest.padded_cast (K := CyclotomicRing.R e) (CyclotomicRing.dimension e)
        N (a.val : ℤ) (x 0 : ℤ) _ _)
    ((coordinate e).symm i).1 ((coordinate e).symm j).1
    ((coordinate e).symm i).2 ((coordinate e).symm j).2
  have hx : (fun j : Fin 3 => (x j : CyclotomicRing.R e)) =
      ![(x 0 : CyclotomicRing.R e),(x 1 : CyclotomicRing.R e),(x 2 : CyclotomicRing.R e)] := by
    funext j
    fin_cases j <;> rfl
  simpa only [Zring,PencilCertificates.lifts,RingHom.mapMatrix_apply,Matrix.map_apply,
    MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_id,Int.cast_natCast,hx] using hh

lemma U_bound (n N e H : ℕ) (x : Fin 3 → ℕ) (hH : 1 ≤ H) (hx : ∀ l, x l ≤ H)
    (a : Fin (n+1)) (i j : Fin (D e)) :
    |U n N e x a i j| ≤ (CyclotomicRing.dimension e : ℤ)^4 *
      (2*(n+1) : ℤ)^(2*CyclotomicRing.dimension e) * (H : ℤ)^(3*CyclotomicRing.dimension e) := by
  have hT (u v) : |integerTest N e (a.val : ℤ) (x 0 : ℤ) u v| ≤
      (CyclotomicRing.dimension e : ℤ)*(2*(n+1) : ℤ)^(2*CyclotomicRing.dimension e)*(H : ℤ)^CyclotomicRing.dimension e := by
    apply IntegralTest.padded_bound _ _ _ _ (n+1) H (by omega) hH
    · rw [Int.abs_natCast]; exact_mod_cast (Nat.le_of_lt a.isLt)
    · rw [Int.abs_natCast]; exact_mod_cast hx 0
  have hh := IntegralLift.entry_bound e (integerTest N e (a.val : ℤ) (x 0 : ℤ))
    (x 1 : ℤ) (x 2 : ℤ)
    (CyclotomicRing.dimension e*(2*(n+1))^(2*CyclotomicRing.dimension e)*H^CyclotomicRing.dimension e)
    H (by simpa using hT) hH (by simpa using hx 1) (by simpa using hx 2)
    ((coordinate e).symm i).1 ((coordinate e).symm j).1
    ((coordinate e).symm i).2 ((coordinate e).symm j).2
  apply hh.trans_eq
  push_cast
  rw [show 3*CyclotomicRing.dimension e = CyclotomicRing.dimension e+2*CyclotomicRing.dimension e by omega,pow_add]
  ring

lemma scaled_normalization {d : ℕ} (A B : Mat d) (hA : A.det ≠ 0) (c : ℚ) (hc : c ≠ 0) :
    (c • A)⁻¹ * (c • B) = A⁻¹*B := by
  let : Invertible c := invertibleOfNonzero hc
  have hi : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
    simpa only [invOf_eq_inv] using (Matrix.inv_smul (A := A) c (isUnit_iff_ne_zero.mpr hA))
  rw [hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  simp [hc]

lemma tupleAt_integer (n N e : ℕ) (x : Fin 3 → ℕ) (hz : (Z n N e x 0).det ≠ 0)
    (a : Fin n) :
    tupleAt n N e x a = ((U n N e x 0).map (Int.castRingHom ℚ))⁻¹ *
      (U n N e x a.succ).map (Int.castRingHom ℚ) := by
  rw [U_cast,U_cast,scaled_normalization _ _ hz _ (by exact_mod_cast (CyclotomicRing.dimension_pos e).ne')]
  rfl

lemma U_det_ne_zero (n N e : ℕ) (x : Fin 3 → ℕ) (hz : (Z n N e x 0).det ≠ 0) :
    (U n N e x 0).det ≠ 0 := by
  have hu : ((U n N e x 0).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [U_cast,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (CyclotomicRing.dimension_pos e).ne')) hz
  have he : ((U n N e x 0).map (Int.castRingHom ℚ)).det = ((U n N e x 0).det : ℚ) :=
    (Int.cast_det _).symm
  rw [he] at hu
  exact_mod_cast hu

end
end RationalHitting.Generator

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.EncodingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.EncodingBounds
open Matrix
open scoped BigOperators

lemma determinant_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ)
    (hA : ∀ i j, |A i j| ≤ B) : |A.det| ≤ (d.factorial : ℤ)*(B : ℤ)^d := by
  rw [Matrix.det_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc ∑ σ : Equiv.Perm (Fin d), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| ≤
          ∑ _σ : Equiv.Perm (Fin d), (B : ℤ)^d := by
         apply Finset.sum_le_sum
         intro σ _
         rw [Units.smul_def, zsmul_eq_mul, abs_mul]
         have hsign : |((Equiv.Perm.sign σ : ℤˣ) : ℤ)| = 1 := by
           rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
         change |((Equiv.Perm.sign σ : ℤˣ) : ℤ)| * |∏ i, A (σ i) i| ≤ (B : ℤ)^d
         rw [hsign]
         rw [one_mul,Finset.abs_prod]
         calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin d, (B : ℤ) :=
                Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => hA _ _)
              _ = _ := by simp
       _ = _ := by simp [Fintype.card_perm]

/-- Cramer's rule used by the generator, without any assumption on arithmetic algorithms. -/
lemma normalized_entry_ratio {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (hA : A.det ≠ 0)
    (i j : Fin d) :
    ((A.map (Int.castRingHom ℚ))⁻¹ * B.map (Int.castRingHom ℚ)) i j =
      Rat.divInt ((A.updateCol i (fun k => B k j)).det) A.det := by
  let AQ := A.map (Int.castRingHom ℚ)
  have hdet : AQ.det ≠ 0 := by
    change (A.map (fun z : ℤ => (z : ℚ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hA
  have h := Matrix.det_smul_inv_mulVec_eq_cramer AQ ((B.map (Int.castRingHom ℚ)).col j)
    (isUnit_iff_ne_zero.mpr hdet)
  have hi := congrFun h i
  simp only [Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply] at hi
  have hcol : AQ.updateCol i ((B.map (Int.castRingHom ℚ)).col j) =
      (A.updateCol i (fun k => B k j)).map (Int.castRingHom ℚ) := by
    ext a b
    simp [AQ,Matrix.updateCol_apply,Matrix.col,Matrix.map_apply]
  rw [hcol] at hi
  change AQ.det * (AQ⁻¹ *ᵥ (B.map (Int.castRingHom ℚ)).col j) i =
    ((A.updateCol i (fun k => B k j)).map (fun z : ℤ => (z : ℚ))).det at hi
  rw [← Int.cast_det] at hi
  change AQ.det * (AQ⁻¹ * B.map (Int.castRingHom ℚ)) i j = _ at hi
  rw [Rat.divInt_eq_div]
  apply (eq_div_iff (show (A.det : ℚ) ≠ 0 from by exact_mod_cast hA)).mpr
  rw [mul_comm]
  have he : AQ.det = (A.det : ℚ) := (Int.cast_det A).symm
  rw [he] at hi
  exact hi

lemma nat_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have : 0 < 2^n := by positivity
    omega

lemma determinant_pow_bound {d b : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ)^b) : |A.det| < (2 : ℤ)^(d*d+d*b+1) := by
  have hb := determinant_bound A (2^b) (by simpa using hA)
  have hf : d.factorial ≤ (2^d)^d :=
    (Nat.factorial_le_pow d).trans (Nat.pow_le_pow_left ((nat_le_two_pow d)) d)
  have hfc : (d.factorial : ℤ) ≤ ((2 : ℤ)^d)^d := by exact_mod_cast hf
  have hn : |A.det| ≤ (2 : ℤ)^(d*d+d*b) := by
    calc |A.det| ≤ (d.factorial : ℤ)*((2 : ℤ)^b)^d := by simpa using hb
         _ ≤ ((2 : ℤ)^d)^d*((2 : ℤ)^b)^d := mul_le_mul_of_nonneg_right hfc (by positivity)
         _ = _ := by rw [← pow_mul,← pow_mul,← pow_add]; congr 1; ring
  apply hn.trans_lt
  rw [pow_succ]
  have : (0 : ℤ) < 2^(d*d+d*b) := by positivity
  omega

lemma normalization_bit_bound {d b : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (hA : A.det ≠ 0)
    (hAb : ∀ i j, |A i j| ≤ (2 : ℤ)^b) (hBb : ∀ i j, |B i j| ≤ (2 : ℤ)^b) (i j : Fin d) :
    (encodeRat (((A.map (Int.castRingHom ℚ))⁻¹ * B.map (Int.castRingHom ℚ)) i j)).length ≤
      4*(d*d+d*b+1)+3 := by
  rw [normalized_entry_ratio A B hA i j]
  apply encodeRat_ratio_le _ _ hA
  · have h := determinant_pow_bound (A.updateCol i (fun k => B k j)) (b := b) (by
      intro a c
      by_cases hc : c = i
      · simpa [Matrix.updateCol_apply,hc] using hBb a j
      · simpa [Matrix.updateCol_apply,hc] using hAb a c)
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · have h := determinant_pow_bound A hAb
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h

end RationalHitting.EncodingBounds

namespace RationalHitting.EncodingBounds

lemma flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length*B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [Nat.add_mul,Nat.one_mul]
    omega

lemma tuple_length_le {n d B : ℕ} (X : Tuple n d)
    (h : ∀ a i j, (encodeRat (X a i j)).length ≤ B) :
    (encodeTuple X).length ≤ n*d*d*B := by
  unfold encodeTuple
  calc _ ≤ (List.finRange n).length*(d*(d*B)) := by
          apply flatMap_length_le
          intro a _
          calc _ ≤ (List.finRange d).length*(d*B) := by
                   apply flatMap_length_le
                   intro i _
                   calc _ ≤ (List.finRange d).length*B := flatMap_length_le _ _ B (fun j _ => h a i j)
                        _ = _ := by simp
               _ = _ := by simp
       _ = _ := by simp [Nat.mul_assoc]

lemma encodeNat_linear (a : ℕ) : (encodeNat a).length ≤ 2*(a+1)+1 := by
  apply encodeNat_le
  have h := nat_le_two_pow a
  have hp : 0 < 2^a := by positivity
  rw [pow_succ]
  omega

lemma output_length_le {n B : ℕ} (H : Output n)
    (hb : ∀ X ∈ H.tuples, ∀ a i j, (encodeRat (X a i j)).length ≤ B) :
    (encodeOutput H).length ≤ 2*(H.dimension+1)+1 + 2*(H.tuples.length+1)+1 +
      H.tuples.length*n*H.dimension*H.dimension*B := by
  have hd := encodeNat_linear H.dimension
  have hc := encodeNat_linear H.tuples.length
  have ht := flatMap_length_le H.tuples encodeTuple (n*H.dimension*H.dimension*B)
    (fun X hX => tuple_length_le X (hb X hX))
  simp only [encodeOutput,List.length_append] at *
  rw [← Nat.mul_assoc,← Nat.mul_assoc,← Nat.mul_assoc] at ht
  omega

end RationalHitting.EncodingBounds


namespace RationalHitting.PolynomialBounds

/-- Coefficient/exponent bookkeeping, with no symbolic expansion of large powers. -/
lemma mul_monomials (a b m i j : ℕ) : (a*m^i)*(b*m^j) = (a*b)*m^(i+j) := by
  rw [pow_add]
  ac_rfl

lemma lift_power (c m i j : ℕ) (hm : 1 ≤ m) (hij : i ≤ j) : c*m^i ≤ c*m^j :=
  Nat.mul_le_mul_left c (Nat.pow_le_pow_right hm hij)

lemma one_le_pow (m k : ℕ) (hm : 1 ≤ m) : 1 ≤ m^k :=
  Nat.one_le_pow k m hm

theorem logarithmic_bound (n s : ℕ) (hn : 1 ≤ n) :
    logarithmic n s ≤ logConstant*(n+s+1)^22 := by
  let m := n+s+1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hM := Parameters.polynomial_M n s
  have hH := Parameters.polynomial_H n s hn
  have h₁ : 4*Parameters.M n s ≤ 64*m^22 := by
    calc _ ≤ 4*(16*m^5) := Nat.mul_le_mul_left 4 hM
         _ = 64*m^5 := by rw [← Nat.mul_assoc]
         _ ≤ _ := lift_power _ _ _ _ hm (by omega)
  have h₂ : 4*Parameters.M n s*(n+1) ≤ 64*m^22 := by
    calc _ ≤ (64*m^5)*m := by
               apply Nat.mul_le_mul
               · calc _ ≤ 4*(16*m^5) := Nat.mul_le_mul_left 4 hM
                      _ = _ := by rw [← Nat.mul_assoc]
               · dsimp [m]; omega
         _ = 64*m^6 := by rw [show m^6 = m^5*m from pow_succ m 5,Nat.mul_assoc]
         _ ≤ _ := lift_power _ _ _ _ hm (by omega)
  have h₃ : 3*Parameters.M n s*Parameters.H n s ≤ (3*16*24577)*m^22 := by
    calc _ ≤ (3*(16*m^5))*(24577*m^17) := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hM) hH
         _ = (48*m^5)*(24577*m^17) := by rw [← Nat.mul_assoc 3 16]
         _ = _ := mul_monomials 48 24577 m 5 17
  unfold logarithmic logConstant
  change _ ≤ (64+64+3*16*24577)*m^22
  rw [Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃

theorem normalized_bits_bound (m D b : ℕ) (hm : 1 ≤ m)
    (hD : D ≤ 256*m^10) (hb : b ≤ logConstant*m^22) :
    4*(D*D+D*b+1)+3 ≤ bitConstant*m^32 := by
  have h₁ : D*D ≤ (256*256)*m^32 := by
    calc _ ≤ (256*m^10)*(256*m^10) := Nat.mul_le_mul hD hD
         _ = (256*256)*m^20 := mul_monomials ..
         _ ≤ _ := lift_power _ _ _ _ hm (by omega)
  have h₂ : D*b ≤ (256*logConstant)*m^32 := by
    calc _ ≤ (256*m^10)*(logConstant*m^22) := Nat.mul_le_mul hD hb
         _ = _ := mul_monomials ..
  have hp := one_le_pow m 32 hm
  unfold bitConstant
  rw [Nat.add_mul,Nat.mul_assoc,Nat.add_mul,Nat.add_mul,one_mul]
  omega

theorem output_bits_bound (n m D L B : ℕ) (hm : 1 ≤ m) (hn : n ≤ m)
    (hD : D ≤ 256*m^10) (hL : L ≤ 24577^3*m^51) (hB : B ≤ bitConstant*m^32) :
    2*(D+1)+1 + 2*(L+1)+1 + L*n*D*D*B ≤ outputConstant*m^104 := by
  have hp := one_le_pow m 104 hm
  have hd : D ≤ 256*m^104 := hD.trans (lift_power _ _ _ _ hm (by omega))
  have hl : L ≤ 24577^3*m^104 := hL.trans (lift_power _ _ _ _ hm (by omega))
  have hproduct : L*n*D*D*B ≤ (24577^3*256*256*bitConstant)*m^104 := by
    calc _ ≤ (24577^3*m^51)*m*(256*m^10)*(256*m^10)*(bitConstant*m^32) := by
               gcongr
         _ = _ := by
           have hh := mul_monomials (24577^3*256*256) bitConstant m 72 32
           calc _ = ((24577^3*256*256)*m^72)*(bitConstant*m^32) := by
                     congr 1
                     calc _ = ((24577^3*256)*m^62)*(256*m^10) := by
                                congr 1
                                calc _ = (24577^3*m^52)*(256*m^10) := by
                                           congr 1
                                           rw [show m^52=m^51*m from pow_succ m 51,Nat.mul_assoc]
                                     _ = _ := mul_monomials _ _ _ _ _
                          _ = _ := mul_monomials _ _ _ _ _
                _ = _ := hh
  unfold outputConstant
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.add_mul]
  omega

end RationalHitting.PolynomialBounds

namespace RationalHitting.Generator
open Matrix EncodingBounds
open scoped BigOperators
noncomputable section

lemma U_power_bound (n N e H : ℕ) (x : Fin 3 → ℕ) (hH : 1 ≤ H) (hx : ∀ l, x l ≤ H)
    (a : Fin (n+1)) (i j : Fin (D e)) :
    |U n N e x a i j| ≤ (2 : ℤ)^(4*CyclotomicRing.dimension e +
      4*CyclotomicRing.dimension e*(n+1)+3*CyclotomicRing.dimension e*H) := by
  let M := CyclotomicRing.dimension e
  have hM : (M : ℤ) ≤ 2^M := by exact_mod_cast nat_le_two_pow M
  have hn : (2*(n+1) : ℤ) ≤ 2^(2*(n+1)) := by exact_mod_cast nat_le_two_pow (2*(n+1))
  have hh : (H : ℤ) ≤ 2^H := by exact_mod_cast nat_le_two_pow H
  calc _ ≤ (M : ℤ)^4*(2*(n+1) : ℤ)^(2*M)*(H : ℤ)^(3*M) := U_bound n N e H x hH hx a i j
       _ ≤ ((2 : ℤ)^M)^4*((2 : ℤ)^(2*(n+1)))^(2*M)*((2 : ℤ)^H)^(3*M) := by
          gcongr
       _ = _ := by
          simp only [← pow_mul,← pow_add]
          congr 1
          dsimp [M]
          ring

lemma tupleAt_bit_bound (n N e H : ℕ) (x : Fin 3 → ℕ) (hH : 1 ≤ H) (hx : ∀ l, x l ≤ H)
    (hz : (Z n N e x 0).det ≠ 0) (a : Fin n) (i j : Fin (D e)) :
    (encodeRat (tupleAt n N e x a i j)).length ≤
      4*(D e*D e+D e*(4*CyclotomicRing.dimension e +
        4*CyclotomicRing.dimension e*(n+1)+3*CyclotomicRing.dimension e*H)+1)+3 := by
  rw [tupleAt_integer n N e x hz a]
  exact normalization_bit_bound _ _ (U_det_ne_zero n N e x hz)
    (U_power_bound n N e H x hH hx 0) (U_power_bound n N e H x hH hx a.succ) i j

lemma output_entry_bit_bound (n N e H : ℕ) (hH : 1 ≤ H)
    (X : Tuple n (D e)) (hX : X ∈ (output n N e H).tuples)
    (a : Fin n) (i j : Fin (D e)) :
    (encodeRat (X a i j)).length ≤
      4*(D e*D e+D e*(4*CyclotomicRing.dimension e +
        4*CyclotomicRing.dimension e*(n+1)+3*CyclotomicRing.dimension e*H)+1)+3 := by
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp hX
  by_cases hz : (Z n N e (fun l => (x l).val+1) 0).det = 0
  · simp [atPoint,hz] at he
  · simp only [atPoint,ite_eq_right hz,Option.some.injEq] at he
    rw [← he]
    exact tupleAt_bit_bound n N e H _ hH (fun l => by omega) hz a i j

lemma list_output_bound (n s : ℕ) (hn : 1 ≤ n) :
    (encodeOutput (list n s)).length ≤ PolynomialBounds.outputConstant*(n+s+1)^104 := by
  have hH : 1 ≤ Parameters.H n s := by unfold Parameters.H; omega
  have hb : ∀ X ∈ (list n s).tuples, ∀ a i j,
      (encodeRat (X a i j)).length ≤ PolynomialBounds.bitConstant*(n+s+1)^32 := by
    intro X hX a i j
    apply (output_entry_bit_bound n (Parameters.N n s) (Parameters.exponent n s)
      (Parameters.H n s) hH X hX a i j).trans
    apply PolynomialBounds.normalized_bits_bound (hm := by omega)
    · exact list_dimension_bound n s
    · exact PolynomialBounds.logarithmic_bound n s hn
  apply (output_length_le (list n s) hb).trans
  apply PolynomialBounds.output_bits_bound (hm := by omega) (hn := by omega)
  · exact list_dimension_bound n s
  · exact list_length_bound n s hn
  · exact Nat.le_refl _

end
end RationalHitting.Generator


/-! A staged division-free determinant computation for integer matrices.
Explicit dense tables prevent recursive matrix-entry recomputation. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.DeterminantAlgorithm
open Matrix
open scoped BigOperators

lemma stages_spec {n : ℕ} (A : Table n) (k : ℕ) :
    denote (stages A k) = (BirdDet.Spec.stepEntry (denote A))^[k] (denote A) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stages,step,denote_tabulate,Function.iterate_succ_apply',ih]

lemma sumFrom_eq_sum_Ico {n lo : ℕ} (f : ℕ → ℤ) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

lemma sumFrom_fin_tail {n : ℕ} (i : Fin n) (f : ℕ → ℤ) :
    BirdDet.sumFrom n (i.val+1) f = ∑ k ∈ Finset.Ioi i, f k.val := by
  rw [sumFrom_eq_sum_Ico]
  calc _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; simp; omega
       _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
       _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
       _ = _ := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

lemma iterate_array_spec {n : ℕ} (A : Array ℤ) (hA : A.size = n*n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [Function.iterate_succ_apply',BirdDet.stepEntry_eq,BirdDet.Spec.stepEntry_eq,
      sumFrom_fin_tail,ih,Matrix.of_apply,BirdDet.get_eq]

lemma array_spec {n : ℕ} (A : Array ℤ) (hA : A.size = n*n) :
    BirdDet.birdDet n A = BirdDet.Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero,BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp [BirdDet.birdDet_succ,BirdDet.Spec.birdDetSpec_succ,← iterate_array_spec A hA k]

lemma spec_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    BirdDet.Spec.birdDet A = A.det := by
  let a := Array.ofFn fun k : Fin (n*n) => A k.divNat k.modNat
  have ha : a.size = n*n := Array.size_ofFn
  have he : Matrix.ofArray a ha = A := Matrix.ofArray_ofFn A
  rw [← he,← array_spec a ha,← BirdDet.det_eq_birdDet a ha]

/-- A genuine executable determinant, not `Matrix.det`'s permutation sum. -/
theorem determinant_eq {n : ℕ} (A : Table n) : determinant A = (denote A).det := by
  rw [← spec_eq_det]
  cases n with
  | zero => rfl
  | succ k => simp only [determinant,stages_spec,BirdDet.Spec.birdDetSpec_succ]

lemma step_bound {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (B C : ℕ)
    (hA : ∀ i j, |A i j| ≤ B) (hF : ∀ i j, |F i j| ≤ C) (i j : Fin n) :
    |BirdDet.Spec.stepEntry A F i j| ≤ (2*n*B*C : ℕ) := by
  have hc : (Finset.Ioi i).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hsum : |∑ k ∈ Finset.Ioi i, F k k| ≤ (n*C : ℕ) := by
    calc _ ≤ ∑ k ∈ Finset.Ioi i, |F k k| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _k ∈ Finset.Ioi i, (C : ℤ) := Finset.sum_le_sum (fun k _ => hF k k)
         _ ≤ (n*C : ℕ) := by
            simp only [Finset.sum_const,nsmul_eq_mul]
            exact_mod_cast Nat.mul_le_mul_right C hc
  have hprod : |∑ k ∈ Finset.Ioi i, F i k*A k j| ≤ (n*C*B : ℕ) := by
    calc _ ≤ ∑ k ∈ Finset.Ioi i, |F i k*A k j| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _k ∈ Finset.Ioi i, ((C : ℤ)*(B : ℤ)) := by
            apply Finset.sum_le_sum
            intro k _
            rw [abs_mul]
            exact mul_le_mul (hF i k) (hA k j) (abs_nonneg _) (by positivity)
         _ ≤ (n*C*B : ℕ) := by
            simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
            exact_mod_cast (Nat.mul_le_mul_right (C*B) hc).trans_eq (Nat.mul_assoc n C B).symm
  change |(-(∑ k ∈ Finset.Ioi i, F k k))*A i j + ∑ k ∈ Finset.Ioi i, F i k*A k j| ≤ _
  calc _ ≤ |(-(∑ k ∈ Finset.Ioi i, F k k))*A i j| + |∑ k ∈ Finset.Ioi i, F i k*A k j| := abs_add_le _ _
       _ ≤ (n*C : ℕ)*(B : ℤ) + (n*C*B : ℕ) := by
          apply add_le_add _ hprod
          rw [abs_mul,abs_neg]
          exact mul_le_mul hsum (hA i j) (abs_nonneg _) (by positivity)
       _ = _ := by push_cast; ring

lemma self_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have : 0 < 2^n := by positivity
    omega

end RationalHitting.DeterminantAlgorithm

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Executable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.ExecutableGenerator
open Matrix DeterminantAlgorithm

lemma normalizedEntry_spec {d : ℕ} (A B : Table d) (hA : (denote A).det ≠ 0) (i j : Fin d) :
    normalizedEntry A B (determinant A) i j =
      (((denote A).map (Int.castRingHom ℚ))⁻¹*(denote B).map (Int.castRingHom ℚ)) i j := by
  rw [normalizedEntry,determinant_eq,denote_tabulate,determinant_eq]
  exact (EncodingBounds.normalized_entry_ratio (denote A) (denote B) hA i j).symm

lemma U_det_eq_zero (n N e : ℕ) (x : Fin 3 → ℕ) :
    (Generator.U n N e x 0).det = 0 ↔ (Generator.Z n N e x 0).det = 0 := by
  have he := congrArg Matrix.det (Generator.U_cast n N e x 0)
  rw [Matrix.det_smul] at he
  simp only [Fintype.card_fin] at he
  change ((Generator.U n N e x 0).map (fun z : ℤ => (z : ℚ))).det =
    (CyclotomicRing.dimension e : ℚ)^(Generator.D e) * (Generator.Z n N e x 0).det at he
  have hc : (CyclotomicRing.dimension e : ℚ)^(Generator.D e) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (CyclotomicRing.dimension_pos e).ne')
  constructor
  · intro h
    have hv : (((Generator.U n N e x 0).det : ℤ) : ℚ) = 0 := by simp [h]
    rw [Int.cast_det,he] at hv
    exact (mul_eq_zero.mp hv).resolve_left hc
  · intro h
    have hv : (((Generator.U n N e x 0).det : ℤ) : ℚ) = 0 := by
      rw [Int.cast_det,he,h,mul_zero]
    exact_mod_cast hv

/-- Exact pointwise equality, including points rejected by the original determinant test. -/
theorem atPoint_spec (n N e : ℕ) (x : Fin 3 → ℕ) :
    atPoint n N e x = Generator.atPoint n N e x := by
  simp only [atPoint,determinant_eq,inputTables_denote,Generator.atPoint]
  by_cases hz : (Generator.Z n N e x 0).det = 0
  · simp [hz,(U_det_eq_zero n N e x).mpr hz]
  · have hu := mt (U_det_eq_zero n N e x).mp hz
    simp only [hz,hu,ite_false,Option.some.injEq]
    funext a i j
    rw [tuple_normalized]
    have hh := normalizedEntry_spec ((inputTables n N e x).get 0)
      ((inputTables n N e x).get a.succ) (by simpa using hu) i j
    simp only [inputTables_denote,determinant_eq] at hh
    rw [hh,Generator.tupleAt_integer n N e x hz a]

theorem output_spec (n N e H : ℕ) : output n N e H = Generator.output n N e H := by
  simp only [output,Generator.output,atPoint_spec]

theorem list_spec (n s : ℕ) : list n s = Generator.list n s := output_spec ..

end RationalHitting.ExecutableGenerator


namespace RationalHitting.ExecutableGenerator

/-- The hitting property and output-size bounds for the computed list. -/


theorem exact_output (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (list n s).dimension ≤ 256*(n+s+1)^10 ∧
    (encodeOutput (list n s)).length ≤ PolynomialBounds.outputConstant*(n+s+1)^104 ∧
    Hits s (list n s) := by
  rw [list_spec]
  exact ⟨Generator.list_dimension_bound n s,Generator.list_output_bound n s hn,
    Generator.list_hits n s hs⟩

end RationalHitting.ExecutableGenerator


/-! Quantitative compilation measured in ordinary TM0 transitions. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.StackLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime
open Turing

lemma exec_add {α : Type*} (step : α → Option α) (s t : ℕ) (a : α) :
    exec step (s+t) a = (exec step s a).bind (exec step t) := by
  induction s generalizing a with
  | zero => simp [exec]
  | succ s ih =>
    simp only [Nat.succ_add,exec,ih,Option.bind_assoc]

lemma exec_trans {α : Type*} {step : α → Option α} {s t : ℕ} {a b c : α}
    (h : exec step s a = some b) (h' : exec step t b = some c) :
    exec step (s+t) a = some c := by rw [exec_add,h,Option.bind_some,h']

lemma exec_positive_congr {α : Type*} {step : α → Option α} {t : ℕ} (ht : 0<t)
    {a b : α} (h : step a = step b) : exec step t a = exec step t b := by
  cases t with
  | zero => omega
  | succ t => simp only [exec,h]

namespace OneToZero
variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- Each TM1 macro-step takes at most its statement size in real TM0 steps.
Load and branch are absorbed into the next primitive step by Mathlib's compiler. -/
theorem statement_time (M : Λ → TM1.Stmt Γ Λ σ) (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ t, 0<t ∧ t ≤ weight q ∧
      exec (TM0.step (TM1to0.tr M)) t ⟨(some q,v),T⟩ =
        some (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih v (T.move d)
    refine ⟨t+1,by omega,by simpa [weight] using Nat.add_le_add_right hb 1,?_⟩
    simpa only [exec,TM0.step,TM1to0.tr,TM1to0.trAux,
      Option.map_some,Option.bind_some,TM1.stepAux] using he
  | write f q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih v (T.write (f T.head v))
    refine ⟨t+1,by omega,by simpa [weight] using Nat.add_le_add_right hb 1,?_⟩
    simpa only [exec,TM0.step,TM1to0.tr,TM1to0.trAux,
      Option.map_some,Option.bind_some,TM1.stepAux] using he
  | load f q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih (f T.head v) T
    refine ⟨t,ht,by simp only [weight]; omega,?_⟩
    rw [exec_positive_congr ht (by rfl : TM0.step (TM1to0.tr M)
      ⟨(some (.load f q),v),T⟩ = TM0.step (TM1to0.tr M) ⟨(some q,f T.head v),T⟩)]
    exact he
  | branch f q r ihq ihr =>
    cases hh : f T.head v with
    | false =>
      obtain ⟨t,ht,hb,he⟩ := ihr v T
      refine ⟨t,ht,by simp only [weight]; omega,?_⟩
      rw [exec_positive_congr ht (by simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hh,Bool.cond_false] :
        TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some r,v),T⟩)]
      simpa [TM1.stepAux,hh] using he
    | true =>
      obtain ⟨t,ht,hb,he⟩ := ihq v T
      refine ⟨t,ht,by simp only [weight]; omega,?_⟩
      rw [exec_positive_congr ht (by simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hh,Bool.cond_true] :
        TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some q,v),T⟩)]
      simpa [TM1.stepAux,hh] using he
  | goto f =>
    refine ⟨1,by omega,by simp [weight],?_⟩
    simp [exec,TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,by simp [weight],?_⟩
    simp [exec,TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,Tape.write_self]

/-- Linear transition overhead for a finitely supported TM1 program. -/
theorem execution_time (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hs : TM1.Supports M S) (C : ℕ) (hC : ∀ l ∈ S, weight (M l) ≤ C)
    (t : ℕ) (a b : TM1.Cfg Γ Λ σ) (ha : a.l ∈ Finset.insertNone S)
    (hr : exec (TM1.step M) t a = some b) :
    ∃ u ≤ C*t, exec (TM0.step (TM1to0.tr M)) u (TM1to0.trCfg M a) =
      some (TM1to0.trCfg M b) := by
  induction t generalizing a with
  | zero =>
    simp only [exec,Option.some.injEq] at hr
    subst b
    exact ⟨0, by omega, rfl⟩
  | succ t ih =>
    obtain ⟨l,v,T⟩ := a
    cases l with
    | none => simp [exec,TM1.step] at hr
    | some l =>
      have hl : l ∈ S := Finset.some_mem_insertNone.mp ha
      have hnext : (TM1.stepAux (M l) v T).l ∈ Finset.insertNone S :=
        TM1.step_supports M hs (by rfl) ha
      change exec (TM1.step M) t (TM1.stepAux (M l) v T) = some b at hr
      obtain ⟨u,hu,he⟩ := ih _ hnext hr
      obtain ⟨v',_,hv',hv⟩ := statement_time M (M l) v T
      refine ⟨v'+u,?_,exec_trans hv he⟩
      have := hC l hl
      linarith

end OneToZero
end RationalHitting.TMTime

/-! A finite structured binary-stack language. Every primitive is a push,
pop, or transfer. -/
namespace RationalHitting.StackLanguage
open Turing
open RationalHitting.TMTime
variable {K : Type} [DecidableEq K]

/-- Exact big-step correctness in real TM2 steps, with no unbounded internal
state or alphabet. -/
theorem eval_compiles {p : Program K} {s v : Store K} {t : ℕ}
    (h : Eval p s v t) (main : Program K) (ps : List (Program K)) :
    exec (TM2.step (machine main)) t (cfg (p::ps) s) = some (cfg ps v) := by
  induction h generalizing ps with
  | skip s => rfl
  | push k b s => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump]
  | drop k s => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump]
  | transfer a b s =>
    cases hh : s a with
    | nil => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,transfer,hh]
    | cons x xs => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,transfer,hh]
  | @seq p q s u v t w hp hq ihp ihq =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.seq p q::ps) s) =
        some (cfg (p::q::ps) s) := by rfl
    simpa only [Nat.add_assoc] using exec_trans h₁ (exec_trans (ihp (q::ps)) (ihq ps))
  | @branchNone k p q r s v t hh h ih =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.branch k p q r::ps) s) =
        some (cfg (p::ps) s) := by simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
    exact exec_trans h₁ (ih ps)
  | @branchFalse k p q r s v t ls hh h ih =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.branch k p q r::ps) s) =
        some (cfg (q::ps) s) := by simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
    exact exec_trans h₁ (ih ps)
  | @branchTrue k p q r s v t ls hh h ih =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.branch k p q r::ps) s) =
        some (cfg (r::ps) s) := by simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
    exact exec_trans h₁ (ih ps)
  | @whileNil k p s hh =>
    simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
  | @whileCons k p s u v t w hh hp hw ihp ihw =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.loop k p::ps) s) =
        some (cfg (p::.loop k p::ps) s) := by
      cases hv : s k with
      | nil => exact (hh hv).elim
      | cons x xs => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hv]
    simpa only [Nat.add_assoc] using exec_trans h₁ (exec_trans (ihp (.loop k p::ps)) (ihw ps))

lemma root_closed (p : Program K) (ps : List (Program K)) (S : Finset (List (Program K)))
    (hs : locations p ps ⊆ S) : successors (p::ps) ⊆ S := by
  cases p with
  | skip | push k b | drop k | transfer a b => simpa [successors] using hs (exit_mem _ _)
  | seq a b => simpa [successors] using hs (by simp [locations])
  | branch k a b c =>
    simp only [successors,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hs (by simp [locations]),hs (by simp [locations]),hs (by simp [locations])⟩
  | loop k a =>
    simp only [successors,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hs (by simp [locations]),hs (by simp [locations])⟩

lemma locations_closed (p : Program K) (ps : List (Program K)) (S : Finset (List (Program K)))
    (hs : locations p ps ⊆ S) (hk : successors ps ⊆ S) :
    ∀ l ∈ locations p ps, successors l ⊆ S := by
  induction p generalizing ps S with
  | skip | push k b | drop k | transfer a b =>
    intro l hl
    simp only [locations,Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl|rfl
    · exact root_closed _ _ _ hs
    · exact hk
  | seq a b iha ihb =>
    have hb : locations b ps ⊆ S := fun l hl => hs (by simp [locations,hl])
    have ha : locations a (b::ps) ⊆ S := fun l hl => hs (by simp [locations,hl])
    have hb' := ihb ps S hb hk
    intro l hl
    simp only [locations,Finset.mem_insert,Finset.mem_union] at hl
    rcases hl with rfl|hl|hl
    · exact root_closed _ _ _ hs
    · exact iha (b::ps) S ha (hb' _ (entry_mem b ps)) l hl
    · exact hb' l hl
  | branch k a b c iha ihb ihc =>
    intro l hl
    simp only [locations,Finset.mem_insert,Finset.mem_union] at hl
    rcases hl with rfl|(hl|hl)|hl
    · exact root_closed _ _ _ hs
    · exact iha ps S (fun x hx => hs (by simp [locations,hx])) hk l hl
    · exact ihb ps S (fun x hx => hs (by simp [locations,hx])) hk l hl
    · exact ihc ps S (fun x hx => hs (by simp [locations,hx])) hk l hl
  | loop k a ih =>
    intro l hl
    simp only [locations,Finset.mem_insert] at hl
    rcases hl with rfl|rfl|hl
    · exact root_closed _ _ _ hs
    · exact hk
    · exact ih _ S (fun x hx => hs (by simp [locations,hx])) (root_closed _ _ _ hs) l hl


lemma instruction_supported (S : Finset (Labels K)) (ps : List (Program K))
    (h : ∀ q ∈ successors ps, some q ∈ S) : TM2.SupportsStmt S (instruction ps) := by
  cases ps with
  | nil => trivial
  | cons p ps =>
    cases p <;> simp only [instruction,TM2.SupportsStmt,jump,successors,
      Finset.mem_insert,Finset.mem_singleton] at * <;> aesop

theorem machine_supported (p : Program K) : TM2.Supports (machine p) (support p) := by
  constructor
  · exact Finset.mem_insert_self _ _
  · intro q hq
    simp only [support,Finset.mem_insert,Finset.mem_image] at hq
    rcases hq with rfl|⟨ps,hps,rfl⟩
    · simp only [machine,jump,TM2.SupportsStmt]
      intro v
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨[p],entry_mem p [],rfl⟩)
    · apply instruction_supported
      intro qs hqs
      have hh := locations_closed p [] (locations p []) (fun _ h => h)
        (by simp [successors]) ps hps hqs
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨qs,hh,rfl⟩)

/-- Entry and halting are one actual macrostep apiece. -/
theorem complete_run {p : Program K} {s v : Store K} {t : ℕ} (h : Eval p s v t) :
    exec (TM2.step (machine p)) (t+2) ⟨some none,none,s⟩ = some ⟨none,none,v⟩ := by
  have he : exec (TM2.step (machine p)) 1 ⟨some none,none,s⟩ = some (cfg [p] s) := rfl
  have hf : exec (TM2.step (machine p)) 1 (cfg [] v) = some ⟨none,none,v⟩ := rfl
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    exec_trans he (exec_trans (eval_compiles h p []) hf)

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.StackToOne
open Turing Turing.TM2to1
open TM2to1.Λ'
open Function
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ)

lemma go_time {k} (o q v) {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n) (H : n ≤ S.length) :
    exec (TM1.step (tr M)) n ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩ =
      some ⟨some (go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply exec_trans (ih (by omega))
    simp only [exec,TM1.step,Option.bind_some,TM1.stepAux,tr,
      Tape.mk'_nth_nat,Tape.move_right_n_head,addBottom_nth_snd]
    rw [stk_nth_val _ hL,List.getElem?_eq_getElem (by simpa using H)]
    simp only [Option.isNone_some,Bool.cond_false]
    rw [iterate_succ_apply']

lemma return_time {q v} {L : ListBlank (∀ k, Option (Γ k))} (n : ℕ) :
    exec (TM1.step (tr M)) n
      ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : TM1.step (tr M)
        ⟨some (ret q),v,(Tape.move Dir.right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [TM1.step]
      congr 1
      rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
        addBottom_nth_succ_fst,TM1.stepAux,iterate_succ',Function.comp_apply,Tape.move_right_left]
      rfl
    rw [exec,hstep,Option.bind_some]
    exact ih

lemma stackWeight_run.{v_1, v_2, v_3, v_4} {K : Type v_1}
  {Γ : K → Type v_2} {Λ : Type v_3} {σ : Type v_4} [DecidableEq K] {k : K}
  (o : Turing.TM2to1.StAct K Γ σ k) (q : Turing.TM2.Stmt Γ Λ σ) :
  RationalHitting.TMTime.StackToOne.stackWeight (Turing.TM2to1.stRun o q) =
    RationalHitting.TMTime.StackToOne.stackWeight q + 1 := by cases o <;> rfl

lemma stWrite_length.{v_1, v_2, v_4} {K : Type v_1} {Γ : K → Type v_2}
  {σ : Type v_4} [DecidableEq K] {k : K} (o : Turing.TM2to1.StAct K Γ σ k) (v : σ)
  (l : List (Γ k)) : (Turing.TM2to1.stWrite v l o).length ≤ l.length + 1 := by
  cases o <;> simp [stWrite,List.length_tail] ; omega

lemma updated_length {k : K} (o : StAct K Γ σ k) (v : σ)
    (S : ∀ k, List (Γ k)) (L : ℕ) (hS : ∀ k, (S k).length ≤ L) :
    ∀ j, (update S k (stWrite v (S k) o) j).length ≤ L+1 := by
  intro j
  by_cases h : j = k
  · subst j
    rw [Function.update_self]
    exact (stWrite_length o v (S k)).trans (Nat.add_le_add_right (hS k) 1)
  · rw [Function.update_of_ne h]
    exact (hS j).trans (by omega)

/-- Real TM1 transition count for the compiled continuation of a TM2 statement.
The multipliers count sweeps to and from actual stack tops. -/
theorem continuation_time (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (T : ListBlank (∀ k, Option (Γ k))) (L : ℕ)
    (hT : ∀ k, T.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (hS : ∀ k, (S k).length ≤ L) :
    ∃ u b, u ≤ stackWeight q*(2*(L+stackWeight q)+3) ∧
      TrCfg (TM2.stepAux q v S) b ∧
      exec (TM1.step (tr M)) u (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) = some b := by
  induction q using stmtStRec generalizing v S T L with
  | run k o q ih =>
    have hg := go_time M o q v (hT k) (S k).length le_rfl
    obtain ⟨T',hT',hact⟩ := tr_respects_aux₂ (Λ := Λ) hT o
    have hactStep : exec (TM1.step (tr M)) 1
        ⟨some (go k o q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom T))⟩ =
        some ⟨some (ret q),stVar v (S k) o,
          (Tape.move Dir.right)^[(stWrite v (S k) o).length] (Tape.mk' ∅ (addBottom T'))⟩ := by
      simp only [exec,TM1.step,Option.bind_some,tr,TM1.stepAux,
        Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hT k),List.getElem?_eq_none (le_of_eq List.length_reverse),
        Option.isNone_none,Bool.cond_true]
      rw [hact]
      simp only [TM1.stepAux,Function.update_self]
    have hr := return_time M (q := q) (v := stVar v (S k) o) (L := T') (stWrite v (S k) o).length
    obtain ⟨u,b,hu,hb,he⟩ := ih _ _ _ (L+1) hT' (updated_length o v S L hS)
    refine ⟨(S k).length+1+(stWrite v (S k) o).length+1+u,b,?_,?_,?_⟩
    · rw [stackWeight_run]
      have hl := hS k
      have hs := stWrite_length o v (S k)
      linarith
    · simpa only [step_run] using hb
    · simp only [trNormal_run,TM1.stepAux]
      rw [show (S k).length+1+(stWrite v (S k) o).length+1+u =
        (S k).length+1+(stWrite v (S k) o).length+(1+u) by omega]
      apply exec_trans (exec_trans (exec_trans hg hactStep) hr)
      change exec (TM1.step (tr M)) (1+u) _ = some b
      rw [exec_add]
      simpa only [exec,TM1.step,Option.bind_some,exec_zero,tr,TM1.stepAux,
        Tape.mk'_head,addBottom_head_fst,Bool.cond_true] using he
  | load f q ih => simpa only [TM2.stepAux,trNormal,TM1.stepAux,stackWeight] using ih (f v) S T L hT hS
  | branch f q r iq ir =>
    cases hh : f v with
    | false =>
      obtain ⟨u,b,hu,hb,he⟩ := ir v S T L hT hS
      refine ⟨u,b,?_,?_,?_⟩
      · simp only [stackWeight]
        apply hu.trans
        exact Nat.mul_le_mul (Nat.le_max_right _ _) (by omega)
      · simpa [TM2.stepAux,hh] using hb
      · simpa [trNormal,TM1.stepAux,hh] using he
    | true =>
      obtain ⟨u,b,hu,hb,he⟩ := iq v S T L hT hS
      refine ⟨u,b,?_,?_,?_⟩
      · simp only [stackWeight]
        apply hu.trans
        exact Nat.mul_le_mul (Nat.le_max_left _ _) (by omega)
      · simpa [TM2.stepAux,hh] using hb
      · simpa [trNormal,TM1.stepAux,hh] using he
  | goto f => exact ⟨0,_,by simp [stackWeight],TrCfg.mk T hT,rfl⟩
  | halt => exact ⟨0,_,by simp [stackWeight],TrCfg.mk T hT,rfl⟩

lemma statement_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ℕ) (hS : ∀ k, (S k).length ≤ L) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ L+stackWeight q := by
  induction q using stmtStRec generalizing v S L with
  | run k o q ih =>
    rw [step_run,stackWeight_run]
    intro j
    exact (ih _ _ (L+1) (updated_length o v S L hS) j).trans_eq (by omega)
  | load f q ih => exact ih (f v) S L hS
  | branch f q r iq ir =>
    cases hh : f v with
    | false =>
      simp only [TM2.stepAux,hh,Bool.cond_false,stackWeight]
      exact fun j => (ir v S L hS j).trans (by omega)
    | true =>
      simp only [TM2.stepAux,hh,Bool.cond_true,stackWeight]
      exact fun j => (iq v S L hS j).trans (by omega)
  | goto => simpa [TM2.stepAux,stackWeight] using hS
  | halt => simpa [TM2.stepAux,stackWeight] using hS

theorem step_time (l : Λ) (v : σ) (S : ∀ k, List (Γ k))
    (a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) (L C : ℕ)
    (ha : TrCfg ⟨some l,v,S⟩ a) (hS : ∀ k, (S k).length ≤ L)
    (hC : stackWeight (M l)+1 ≤ C) :
    ∃ u b, u ≤ C*(2*(L+C)+4) ∧ TrCfg (TM2.stepAux (M l) v S) b ∧
      exec (TM1.step (tr M)) u a = some b := by
  obtain ⟨T,hT⟩ := ha
  obtain ⟨u,b,hu,hb,he⟩ := continuation_time M (M l) v S T L hT hS
  refine ⟨u+1,b,?_,hb,?_⟩
  · have hm : 2*(L+stackWeight (M l))+3 ≤ 2*(L+C)+4 := by omega
    have hm' : stackWeight (M l)*(2*(L+stackWeight (M l))+3) ≤
        stackWeight (M l)*(2*(L+C)+4) := Nat.mul_le_mul_left _ hm
    calc u+1 ≤ (stackWeight (M l)+1)*(2*(L+C)+4) := by linarith
         _ ≤ _ := Nat.mul_le_mul_right _ hC
  · simpa only [exec,TM1.step,tr,Option.map_some,Option.bind_some] using he

/-- A bounded TM2 run on stacks of initial length <=L is simulated by Mathlib's
single tape TM1 interpreter in at most C*t*(2*(L+C*t)+4) macro-transitions.
C is a fixed syntactic maximum over the finite program, not input advice. -/
theorem execution_time [Inhabited Λ] (F : Finset Λ) (hF : TM2.Supports M F)
    (C : ℕ) (hC : ∀ l ∈ F, stackWeight (M l)+1 ≤ C)
    (t : ℕ) (a b : TM2.Cfg Γ Λ σ)
    (a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) (L : ℕ)
    (ha : a.l ∈ Finset.insertNone F) (hS : ∀ k, (a.stk k).length ≤ L)
    (htr : TrCfg a a') (hr : exec (TM2.step M) t a = some b) :
    ∃ u b', u ≤ C*t*(2*(L+C*t)+4) ∧ TrCfg b b' ∧
      exec (TM1.step (tr M)) u a' = some b' := by
  induction t generalizing L a a' with
  | zero =>
    simp only [exec,Option.some.injEq] at hr
    subst b
    exact ⟨0,a',by omega,htr,rfl⟩
  | succ t ih =>
    obtain ⟨l,v,S⟩ := a
    cases l with
    | none => simp [exec,TM2.step] at hr
    | some l =>
      have hl := Finset.some_mem_insertNone.mp ha
      obtain ⟨u₀,c',hu₀,hc',he₀⟩ := step_time M l v S a' L C htr hS (hC l hl)
      have hnext : (TM2.stepAux (M l) v S).l ∈ Finset.insertNone F :=
        TM2.step_supports M hF (by rfl) ha
      have hlen : ∀ k, ((TM2.stepAux (M l) v S).stk k).length ≤ L+C := by
        intro k
        exact (statement_length (M l) v S L hS k).trans (by have := hC l hl; omega)
      change exec (TM2.step M) t (TM2.stepAux (M l) v S) = some b at hr
      obtain ⟨u,b',hu,hb',he⟩ := ih _ _ (L+C) hnext hlen hc' hr
      refine ⟨u₀+u,b',?_,hb',exec_trans he₀ he⟩
      have hu₀' : u₀ ≤ C*(2*(L+C*(t+1))+4) := by
        apply hu₀.trans
        apply Nat.mul_le_mul_left
        have : C ≤ C*(t+1) := by simpa using Nat.mul_le_mul_left C (show 1 ≤ t+1 by omega)
        omega
      have hu' : u ≤ C*t*(2*(L+C*(t+1))+4) := by
        convert hu using 1 ; ring
      calc u₀+u ≤ C*(2*(L+C*(t+1))+4)+C*t*(2*(L+C*(t+1))+4) := Nat.add_le_add hu₀' hu'
           _ = _ := by ring

theorem halts (a : TM2.Cfg Γ Λ σ) (a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (htr : TrCfg a a') (ha : TM2.step M a = none) : TM1.step (tr M) a' = none := by
  obtain ⟨l,v,S⟩ := a
  cases l with
  | none => cases htr; rfl
  | some l => simp [TM2.step] at ha

end RationalHitting.TMTime.StackToOne

namespace RationalHitting.TMTime.FiniteStates
open Turing
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]

lemma stateDecode_encode (S : Finset Λ) (q : Λ) (hq : q∈S) :
    stateDecode S (stateEncode S q)=q := by
  by_cases h : q=default
  · simp [stateEncode,stateDecode,h]
  · simp [stateEncode,stateDecode,h,hq]

lemma step_cfg (M : TM0.Machine Γ Λ) (S : Finset Λ) (a : TM0.Cfg Γ Λ) (ha : a.q∈S) :
    TM0.step (machine M S) (cfg S a) = (TM0.step M a).map (cfg S) := by
  rcases a with ⟨q,T⟩
  simp only [TM0.step,machine,cfg,stateDecode_encode S q ha,Option.map_map]
  rfl

lemma execution (M : TM0.Machine Γ Λ) (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ))
    (t : ℕ) (a b : TM0.Cfg Γ Λ) (ha : a.q∈S)
    (hr : exec (TM0.step M) t a=some b) :
    exec (TM0.step (machine M S)) t (cfg S a)=some (cfg S b) := by
  induction t generalizing a with
  | zero => simpa [exec] using congrArg (Option.map (cfg S)) hr
  | succ t ih =>
    cases he : TM0.step M a with
    | none => simp [exec,he] at hr
    | some c =>
      have hc : c.q∈S := TM0.step_supports M hs he ha
      have hr' : exec (TM0.step M) t c=some b := by simpa [exec,he] using hr
      simp only [exec,step_cfg M S a ha,he,Option.map_some,Option.bind_some]
      exact ih c hc hr'

lemma run_support.{v_1, v_2} {Γ : Type v_1} {Λ : Type v_2}
  [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ] (M : Turing.TM0.Machine Γ Λ) (S : Finset Λ)
  (hs : Turing.TM0.Supports M ↑S) (t : ℕ) (a b : Turing.TM0.Cfg Γ Λ) (ha : a.q ∈ S)
  (hr : RationalHitting.TMTime.exec (Turing.TM0.step M) t a = some b) : b.q ∈ S := by
  induction t generalizing a with
  | zero => simp only [exec,Option.some.injEq] at hr; subst b; exact ha
  | succ t ih =>
    cases he : TM0.step M a with
    | none => simp [exec,he] at hr
    | some c => exact ih c (TM0.step_supports M hs he ha) (by simpa [exec,he] using hr)

/-- Finite-support compression has no transition or tape overhead. -/
theorem finite_machine (M : TM0.Machine Γ Λ) (S : Finset Λ)
    (hs : TM0.Supports M (S : Set Λ)) :
    ∃ (m : ℕ) (G : TM0.Machine Γ (Fin (m+1))), ∀ (l : List Γ) (t : ℕ) (a : TM0.Cfg Γ Λ),
      exec (TM0.step M) t (TM0.init l)=some a → TM0.step M a=none →
      ∃ b : TM0.Cfg Γ (Fin (m+1)), exec (TM0.step G) t (TM0.init l)=some b ∧
        TM0.step G b=none ∧ b.Tape=a.Tape := by
  refine ⟨Fintype.card ↥S,machine M S,?_⟩
  intro l t a hr hh
  have hi : (TM0.init l).q∈S := hs.1
  refine ⟨cfg S a,?_,?_,rfl⟩
  · simpa only [cfg_init] using execution M S hs t (TM0.init l) a hi hr
  · rw [step_cfg M S a (run_support M S hs t _ _ hi hr),hh,Option.map_none]

end RationalHitting.TMTime.FiniteStates

/-! Quantitative finite-control compilation of stack programs,
with an explicit tape encoding. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.FiniteCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage.Compiler
open Turing RationalHitting.TMTime
open scoped BigOperators
variable {K : Type} [DecidableEq K]

lemma stackConstant_bound (p : Program K) (l : Labels K) (hl : l∈support p) :
    StackToOne.stackWeight (machine p l)+1 ≤ stackConstant p := by
  have hh : StackToOne.stackWeight (machine p l)+1 ≤ ∑ j ∈ support p, (StackToOne.stackWeight (machine p j)+1) :=
    Finset.single_le_sum (f:=fun j => StackToOne.stackWeight (machine p j)+1) (fun _ _ => Nat.zero_le _) hl
  unfold stackConstant
  omega

lemma tapeSupported (p : Program K) :
    TM1.Supports (TM2to1.tr (machine p)) (tapeSupport p) :=
  TM2to1.tr_supports (machine p) (machine_supported p)

end RationalHitting.StackLanguage.Compiler

namespace RationalHitting.TMTime.Alphabet
open Turing
open TM1 TM1to1
variable {Γ Λ σ : Type*} [Inhabited Γ]
variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
variable (enc0 : enc default = List.Vector.replicate n false)
variable (encdec : ∀ a, dec (enc a) = a)

include encdec

/-- Alphabet coding adds at most one macrostep per deferred write. -/
theorem continuation_time (M : Λ → TM1.Stmt Γ Λ σ) (q : TM1.Stmt Γ Λ σ)
    (v : σ) (L R : ListBlank Γ) :
    ∃ t ≤ writesWeight q,
      exec (TM1.step (TM1to1.tr enc dec M)) t
        (TM1.stepAux (TM1to1.trNormal dec q) v (TM1to1.trTape' enc0 L R)) =
        some (TM1to1.trCfg enc enc0 (TM1.stepAux q v (Tape.mk' L R))) := by
  induction q generalizing v L R with
  | move d q ih =>
    cases d <;>
      simp only [trNormal,stepAux_move,stepAux,Tape.move_left_mk',Tape.move_right_mk',
        trTape'_move_left enc0,trTape'_move_right enc0,writesWeight] <;> apply ih
  | write f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux]
    obtain ⟨a,R,rfl⟩ := R.exists_cons
    obtain ⟨t,ht,he⟩ := ih v L (R.cons (f a v))
    refine ⟨t+1,by simpa [writesWeight] using Nat.add_le_add_right ht 1,?_⟩
    rw [exec]
    simp only [TM1.step,Option.bind_some,TM1to1.tr,Tape.mk'_head,ListBlank.head_cons,
      stepAux_write,stepAux_move,trTape'_move_left enc0,ListBlank.head_cons,
      ListBlank.tail_cons]
    simpa only [Tape.write_mk',trTape_mk',ListBlank.cons_head_tail,ListBlank.tail_cons] using he
  | load f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,Tape.mk'_head,writesWeight]
    apply ih
  | branch p q r ihq ihr =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,Tape.mk'_head]
    cases h : p R.head v with
    | false =>
      simp only [Bool.cond_false]
      obtain ⟨t,ht,he⟩ := ihr v L R
      exact ⟨t,ht.trans (Nat.le_max_right _ _),he⟩
    | true =>
      simp only [Bool.cond_true]
      obtain ⟨t,ht,he⟩ := ihq v L R
      exact ⟨t,ht.trans (Nat.le_max_left _ _),he⟩
  | goto f =>
    refine ⟨0,by simp [writesWeight],?_⟩
    simp only [exec,trNormal,stepAux_read dec enc0 encdec,stepAux,trCfg,trTape_mk',Option.map_some,Tape.mk'_head]
  | halt =>
    refine ⟨0,by simp [writesWeight],?_⟩
    simp only [exec,trNormal,stepAux,trCfg,trTape_mk',Option.map_none]

/-- Linear macrostep time overhead for the finite-alphabet compiler. Physical
moves and reads are subsequently counted by the quantitative TM1->TM0 compiler. -/
theorem execution_time [Inhabited Λ] (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hs : TM1.Supports M S) (C : ℕ) (hC : ∀ l ∈ S, writesWeight (M l)+1 ≤ C)
    (t : ℕ) (a b : TM1.Cfg Γ Λ σ) (ha : a.l ∈ Finset.insertNone S)
    (hr : exec (TM1.step M) t a = some b) :
    ∃ u ≤ C*t, exec (TM1.step (TM1to1.tr enc dec M)) u
      (TM1to1.trCfg enc enc0 a) = some (TM1to1.trCfg enc enc0 b) := by
  induction t generalizing a with
  | zero =>
    simp only [exec,Option.some.injEq] at hr
    subst b
    exact ⟨0,by omega,rfl⟩
  | succ t ih =>
    obtain ⟨l,v,T⟩ := a
    cases l with
    | none => simp [exec,TM1.step] at hr
    | some l =>
      obtain ⟨L,R,rfl⟩ := T.exists_mk'
      have hl : l ∈ S := Finset.some_mem_insertNone.mp ha
      have hn : (TM1.stepAux (M l) v (Tape.mk' L R)).l ∈ Finset.insertNone S :=
        TM1.step_supports M hs (by rfl) ha
      change exec (TM1.step M) t (TM1.stepAux (M l) v (Tape.mk' L R)) = some b at hr
      obtain ⟨u,hu,he⟩ := ih _ hn hr
      obtain ⟨w,hw,hwx⟩ := continuation_time enc dec enc0 encdec M (M l) v L R
      have hx : exec (TM1.step (TM1to1.tr enc dec M)) (w+1)
          (TM1to1.trCfg enc enc0 ⟨some l,v,Tape.mk' L R⟩) =
          some (TM1to1.trCfg enc enc0 (TM1.stepAux (M l) v (Tape.mk' L R))) := by
        simpa only [exec,TM1.step,trCfg,Option.map_some,Option.bind_some,tr,trTape_mk'] using hwx
      refine ⟨(w+1)+u,?_,exec_trans hx he⟩
      have hb := hC l hl
      linarith

omit encdec in
theorem halts.{v_1, v_2, v_3} {Γ : Type v_1} {Λ : Type v_2} {σ : Type v_3}
  [Inhabited Γ] {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default = List.Vector.replicate n false) (_encdec : ∀ (a : Γ), dec (enc a) = a)
  (M : Λ → Turing.TM1.Stmt Γ Λ σ) (a : Turing.TM1.Cfg Γ Λ σ) (ha : Turing.TM1.step M a = none) :
  Turing.TM1.step (Turing.TM1to1.tr enc dec M) (Turing.TM1to1.trCfg enc enc0 a) = none := by
  rcases a with ⟨l,v,T⟩
  cases l <;> simp_all [TM1.step,trCfg]

end RationalHitting.TMTime.Alphabet

namespace RationalHitting.TMTime.Alphabet
open Turing
lemma compiled_init {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    {b : ℕ} (enc : Γ → List.Vector Bool b) (h0 : enc default=List.Vector.replicate b false)
    (w : List Γ) :
    TM1to1.trCfg enc h0 (TM1.init w : TM1.Cfg Γ Λ σ)=
      TM1.init (w.flatMap (fun a => (enc a).toList)) := by
  simp [TM1to1.trCfg,TM1.init,Tape.mk₁,Tape.mk₂,TM1to1.trTape_mk',TM1to1.trTape']
  rfl
end RationalHitting.TMTime.Alphabet

namespace RationalHitting.StackLanguage.Compiler
open Turing RationalHitting.TMTime
open scoped BigOperators
variable {K : Type} [DecidableEq K] [Fintype K]

/- The alphabet is finite because the number of stacks is fixed. -/

/-- Polynomial-time compilation to a binary finite-state TM0,
preserving an explicit fixed block encoding. -/

theorem binary_compilation (p : Program K) :
    ∃ (b : ℕ) (enc : TapeAlphabet K → List.Vector Bool b)
      (dec : List.Vector Bool b → TapeAlphabet K)
      (h0 : enc default=List.Vector.replicate b false),
      (∀ a,dec (enc a)=a) ∧
      ∃ (m : ℕ) (G : TM0.Machine Bool (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ (k : K) (w : List Bool) (v : Store K) (t : ℕ),
        Eval p (Function.update (fun _ => []) k w) v t →
        ∃ u ≤ C*(w.length+t+3)^2, ∃ a,
          exec (TM0.step G) u (TM0.init ((TM2to1.trInit k w).flatMap (fun z => (enc z).toList)))=some a ∧
          TM0.step G a=none ∧
          ∃ c : TM1.Cfg (TapeAlphabet K) (TapeLabels K) (Option Bool),
            TM2to1.TrCfg (⟨none,none,v⟩ : TM2.Cfg (fun _ : K => Bool) (Labels K) (Option Bool)) c ∧
            a.Tape=TM1to1.trTape h0 c.Tape := by
  classical
  obtain ⟨b,enc,dec,h0,hd⟩ := TM1to1.exists_enc_dec (Γ:=TapeAlphabet K)
  let M := TM2to1.tr (machine p)
  let F := tapeSupport p
  have hF : TM1.Supports M F := tapeSupported p
  let N := TM1to1.tr enc dec M
  let H := TM1to1.trSupp M F
  have hH : TM1.Supports N H := TM1to1.tr_supports enc dec M hF
  let A := stackConstant p
  let B := 1+∑ l ∈ F, (Alphabet.writesWeight (M l)+1)
  let D := 1+∑ l ∈ H, OneToZero.weight (N l)
  have hA : 1≤A := by simp [A,stackConstant]
  have hB : 1≤B := by simp [B]
  have hD : 1≤D := by simp [D]
  have hbnd : ∀ l ∈ F, Alphabet.writesWeight (M l)+1≤B := by
    intro l hl
    have hh := Finset.single_le_sum (f:=fun j => Alphabet.writesWeight (M j)+1)
      (fun _ _ => Nat.zero_le _) hl
    exact hh.trans (Nat.le_add_left _ _)
  have hdnd : ∀ l ∈ H, OneToZero.weight (N l)≤D := by
    intro l hl
    have hh := Finset.single_le_sum (f:=fun j => OneToZero.weight (N j))
      (fun _ _ => Nat.zero_le _) hl
    exact hh.trans (Nat.le_add_left _ _)
  let S := TM1to0.trStmts N H
  have hs : TM0.Supports (TM1to0.tr N) (S : Set (TM1to0.Λ' N)) := TM1to0.tr_supports N hH
  obtain ⟨m,G,hG⟩ := FiniteStates.finite_machine (TM1to0.tr N) S hs
  refine ⟨b,enc,dec,h0,hd,m,G,10*D*B*(A+1)^2,by positivity,?_⟩
  intro k w v t he
  let a₂ : TM2.Cfg (fun _ : K => Bool) (Labels K) (Option Bool) := TM2.init k w
  let b₂ : TM2.Cfg (fun _ : K => Bool) (Labels K) (Option Bool) := ⟨none,none,v⟩
  let a₁ : TM1.Cfg (TapeAlphabet K) (TapeLabels K) (Option Bool) := TM1.init (TM2to1.trInit k w)
  have hr : exec (TM2.step (machine p)) (t+2) a₂=some b₂ := complete_run he
  have hlen : ∀ j, (a₂.stk j).length≤w.length := by
    intro j
    simp only [a₂,TM2.init]
    by_cases hj : j=k <;> simp [hj]
  obtain ⟨u,c,hu,htr,hx⟩ := StackToOne.execution_time (machine p) (support p)
    (machine_supported p) A (stackConstant_bound p) (t+2) a₂ b₂ a₁ w.length
    (Finset.some_mem_insertNone.mpr (machine_supported p).1) hlen
    (TM2to1.trCfg_init (Γ:=fun _ : K => Bool) (Λ:=Labels K) (σ:=Option Bool) k w) hr
  have hhal : TM1.step M c=none := StackToOne.halts (machine p) b₂ c htr rfl
  obtain ⟨u',hu',hx'⟩ := Alphabet.execution_time enc dec h0 hd M F hF B hbnd u a₁ c
    (Finset.some_mem_insertNone.mpr hF.1) hx
  have hi : TM1to1.trCfg enc h0 a₁ =
      TM1.init ((TM2to1.trInit k w).flatMap (fun z => (enc z).toList)) :=
    Alphabet.compiled_init enc h0 _
  rw [hi] at hx'
  have hh' := Alphabet.halts enc dec h0 hd M c hhal
  obtain ⟨u'',hu'',hx''⟩ := OneToZero.execution_time N H hH D hdnd u'
    (TM1.init ((TM2to1.trInit k w).flatMap (fun z => (enc z).toList)))
    (TM1to1.trCfg enc h0 c) (Finset.some_mem_insertNone.mpr hH.1) hx'
  have hz : TM1to0.trCfg N (TM1.init ((TM2to1.trInit k w).flatMap (fun z => (enc z).toList)))=
      TM0.init ((TM2to1.trInit k w).flatMap (fun z => (enc z).toList)) := rfl
  rw [hz] at hx''
  obtain ⟨a,ha,hh,htape⟩ := hG _ u'' _ hx'' (OneToZero.halts N _ hh')
  refine ⟨u'',?_,a,ha,hh,c,htr,htape⟩
  have hx₁ : t+2≤w.length+t+3 := by omega
  have hx₂ : w.length+A*(t+2)≤(A+1)*(w.length+t+3) := by linarith only [Nat.zero_le (A*w.length)]
  have hx₃ : 2*(w.length+A*(t+2))+4≤4*(A+1)*(w.length+t+3) := by nlinarith only [hx₂,hA,Nat.zero_le w.length,Nat.zero_le t]
  calc u'' ≤ D*u' := hu''
       _ ≤ D*(B*u) := Nat.mul_le_mul_left _ hu'
       _ ≤ D*(B*(A*(t+2)*(2*(w.length+A*(t+2))+4))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hu)
       _ ≤ D*(B*(A*(w.length+t+3)*(4*(A+1)*(w.length+t+3)))) :=
         Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hx₁) hx₃))
       _ ≤ 10*D*B*(A+1)^2*(w.length+t+3)^2 := by nlinarith [Nat.zero_le (D*B*(w.length+t+3)^2)]

end RationalHitting.StackLanguage.Compiler

namespace RationalHitting.TMTime.OneToZero
open Turing
open scoped BigOperators

lemma supports_univ {Γ Λ σ : Type*} [Fintype Λ] (q : TM1.Stmt Γ Λ σ) :
    TM1.SupportsStmt Finset.univ q := by
  induction q <;> simp_all [TM1.SupportsStmt]

/-- Every fixed finite-control TM1 has an ordinary finite-state TM0 compiling
all runs at a fixed linear cost and preserving the literal tape. -/
theorem finite_compiler {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    [Fintype Λ] [Fintype σ] (M : Λ → TM1.Stmt Γ Λ σ) :
    ∃ (m : ℕ) (G : TM0.Machine Γ (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ (w : List Γ) (t : ℕ) (a : TM1.Cfg Γ Λ σ),
        exec (TM1.step M) t (TM1.init w)=some a → TM1.step M a=none →
        ∃ u≤C*t, ∃ b : TM0.Cfg Γ (Fin (m+1)),
          exec (TM0.step G) u (TM0.init w)=some b ∧ TM0.step G b=none ∧ b.Tape=a.Tape := by
  classical
  let F : Finset Λ := Finset.univ
  have hs : TM1.Supports M F := ⟨Finset.mem_univ _,fun q _ => supports_univ (M q)⟩
  let S := TM1to0.trStmts M F
  have hs' : TM0.Supports (TM1to0.tr M) (S : Set (TM1to0.Λ' M)) := TM1to0.tr_supports M hs
  obtain ⟨m,G,hG⟩ := FiniteStates.finite_machine (TM1to0.tr M) S hs'
  let C := 1+∑ q∈F, weight (M q)
  have hC : ∀ q∈F, weight (M q)≤C := by
    intro q hq
    exact (Finset.single_le_sum (f:=fun q => weight (M q)) (fun _ _ => Nat.zero_le _) hq).trans (Nat.le_add_left _ _)
  refine ⟨m,G,C,by simp [C],?_⟩
  intro w t a hr hh
  obtain ⟨u,hu,hx⟩ := execution_time M F hs C hC t (TM1.init w) a
    (Finset.some_mem_insertNone.mpr hs.1) hr
  have hi : TM1to0.trCfg M (TM1.init w)=TM0.init w := rfl
  rw [hi] at hx
  obtain ⟨b,hb,hhb,ht⟩ := hG w u _ hx (halts M a hh)
  exact ⟨u,hu,b,hb,hhb,ht⟩

end RationalHitting.TMTime.OneToZero

/-! Raw unary input adapter for the finite block-coded stack compiler.
The alphabet is exactly Fin 4. No list-processing oracle is an instruction. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.InputAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.InputAdapter
open Turing

lemma stepAux_writeBits (bs : List Bool) (q : Stmt) (v : V) (L R : List A) :
    TM1.stepAux (writeBits bs q) v (Tape.mk₂ L R)=
      TM1.stepAux q v (Tape.mk₂ ((bs.map bit).reverse++L) (R.drop bs.length)) := by
  induction bs generalizing L R with
  | nil => simp [writeBits]
  | cons b bs ih =>
    simp only [writeBits,TM1.stepAux,write₂,right₂,ih,List.map_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append,List.length_cons]
    have hd : R.tail.drop bs.length = R.drop (bs.length+1) := by
      rw [←List.drop_one,List.drop_drop]
      simp [Nat.add_comm]
    rw [hd]

lemma scan_right (F : Q → Stmt) (q : Q) (v : V) (l L R : List A)
    (h : ∀ a∈l, ∀ L R, TM1.step F (⟨some q,v,Tape.mk₂ L (a::R)⟩ : Cfg)=
      some ⟨some q,v,Tape.mk₂ (a::L) R⟩) :
    exec (TM1.step F) l.length (⟨some q,v,Tape.mk₂ L (l++R)⟩ : Cfg)=
      some ⟨some q,v,Tape.mk₂ (l.reverse++L) R⟩ := by
  induction l generalizing L R with
  | nil => simp []
  | cons a l ih =>
    have hs := h a (by simp) L (l++R)
    simp only [List.cons_append,List.length_cons,exec,hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using ih (a::L) R (fun b hb => h b (by simp [hb]))

lemma scan_left (F : Q → Stmt) (q r : Q) (v : V) (l L R : List A)
    (hF : F q=leftTo q r) (hl : ∀ a∈l, a≠3) :
    exec (TM1.step F) (l.length+1) (⟨some q,v,Tape.mk₂ (l++3::L) R⟩ : Cfg)=
      some ⟨some r,v,Tape.mk₂ L (3::l.reverse++R)⟩ := by
  induction l generalizing R with
  | nil =>
    simp [exec,TM1.step,hF,leftTo,jump,TM1.stepAux,Tape.mk₂]
  | cons a l ih =>
    have ha := hl a (by simp)
    have hh := ih (a::R) (fun b hb => hl b (by simp [hb]))
    have hs : TM1.step F (⟨some q,v,Tape.mk₂ ((a::l)++3::L) R⟩ : Cfg)=
        some ⟨some q,v,Tape.mk₂ (l++3::L) (a::R)⟩ := by
      simp [TM1.step,hF,leftTo,TM1.stepAux,beq_eq_false_iff_ne.mpr ha,jump]
    change (TM1.step F _).bind (exec (TM1.step F) (l.length+1)) = _
    rw [hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using hh

lemma process (code : Bool → Bool → List Bool) (x f b : Bool) (xs out : List Bool) (k : ℕ) :
    exec (TM1.step (M code)) (2*k+2*out.length+(code f x).length+7)
      (invariant (x::xs) k out f b)=
      some (invariant xs (k+1) (out++code f x) false x) := by
  let X := xs.map raw
  let O := out.map bit
  let Z := List.replicate (k+1) (0:A)
  let c := code f x
  let C := c.map bit
  have h1 : exec (TM1.step (M code)) 1 (invariant (x::xs) k out f b)=
      some (state 2 f x (3::X) (Z++3::O++[3])) := by
    cases x <;> simp [exec,TM1.step,TM1.stepAux,M,invariant,state,raw,jump,move,X,O,Z,
      List.replicate_succ]
  have h2 : exec (TM1.step (M code)) Z.length (state 2 f x (3::X) (Z++3::O++[3]))=
      some (state 2 f x (Z.reverse++3::X) (3::O++[3])) := by
    simp only [state,List.append_assoc,List.cons_append]
    apply scan_right
    intro a ha L R
    have ha0 : a=0 := by simpa [Z] using ha
    subst a
    simp [TM1.step,TM1.stepAux,M,jump,move]
  have h3 : exec (TM1.step (M code)) 1 (state 2 f x (Z.reverse++3::X) (3::O++[3]))=
      some (state 3 f x (3::Z.reverse++3::X) (O++[3])) := by
    simp [exec,state,TM1.step,TM1.stepAux,M,jump,move]
  have h4 : exec (TM1.step (M code)) O.length (state 3 f x (3::Z.reverse++3::X) (O++[3]))=
      some (state 3 f x (O.reverse++3::Z.reverse++3::X) [3]) := by
    simp only [state,List.append_assoc,List.cons_append]
    apply scan_right
    intro a ha L R
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ha
    simp [TM1.step,TM1.stepAux,M,jump,move,beq_eq_false_iff_ne.mpr (bit_ne_three y)]
  have h5 : exec (TM1.step (M code)) 1 (state 3 f x (O.reverse++3::Z.reverse++3::X) [3])=
      some (state 4 false x (C.reverse++O.reverse++3::Z.reverse++3::X) [3]) := by
    cases f <;> cases x <;>
      simp [exec,state,TM1.step,M,TM1.stepAux,stepAux_writeBits,write₂,head₂,jump,
        List.append_assoc,C,c]
  have h6 : exec (TM1.step (M code)) ((O++C).length+1)
      (state 4 false x (C.reverse++O.reverse++3::Z.reverse++3::X) [3])=
      some (state 5 false x (Z.reverse++3::X) (3::(O++C)++[3])) := by
    have hn : ∀ a ∈ (O++C).reverse, a≠3 := by
      intro a ha
      rcases List.mem_append.mp (List.mem_reverse.mp ha) with ho|hc
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ho
        exact bit_ne_three y
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hc
        exact bit_ne_three y
    simpa only [state,List.reverse_reverse,List.reverse_append,List.append_assoc,List.cons_append,
      List.length_reverse,List.length_append,Nat.add_comm] using
      scan_left (M code) 4 5 (false,x) (O++C).reverse (Z.reverse++3::X) [3] rfl hn
  have h7 : exec (TM1.step (M code)) (Z.length+1)
      (state 5 false x (Z.reverse++3::X) (3::(O++C)++[3]))=
      some (invariant xs (k+1) (out++code f x) false x) := by
    have hn : ∀ a∈Z.reverse, a≠3 := by
      intro a ha
      have ha0 : a=0 := by simpa [Z] using ha
      subst a
      decide
    have hh := scan_left (M code) 5 1 (false,x) Z.reverse X (3::(O++C)++[3]) rfl hn
    dsimp [state,invariant,X,Z,O,C,c] at hh ⊢
    simp only [List.reverse_replicate,List.map_append] at hh ⊢
    simp only [List.cons_append,List.append_assoc] at hh ⊢
    exact hh
  have he := exec_trans (exec_trans (exec_trans (exec_trans (exec_trans
    (exec_trans h1 h2) h3) h4) h5) h6) h7
  have ht : 2*k+2*out.length+(code f x).length+7 =
      1+Z.length+1+O.length+1+((O++C).length+1)+(Z.length+1) := by
    simp [Z,O,C,c,List.length_append]
    omega
  rw [ht]
  exact he

lemma all_process (code : Bool → Bool → List Bool) (xs out : List Bool) (k : ℕ) (f b : Bool) :
    ∃ f' b', exec (TM1.step (M code)) (cost code f xs k out.length)
      (invariant xs k out f b)=
      some (invariant [] (k+xs.length) (out++emit code f xs) f' b') := by
  induction xs generalizing out k f b with
  | nil => exact ⟨f,b,by simp [cost,emit]⟩
  | cons x xs ih =>
    obtain ⟨f',b',hh⟩ := ih (out++code f x) (k+1) false x
    refine ⟨f',b',?_⟩
    have he := exec_trans (process code x f b xs out k) hh
    simpa [cost,emit,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he

lemma emit_length (code : Bool → Bool → List Bool) (B : ℕ)
    (hb : ∀ f x, (code f x).length≤B) (f : Bool) (xs : List Bool) :
    (emit code f xs).length≤B*xs.length := by
  induction xs generalizing f with
  | nil => simp [emit]
  | cons x xs ih =>
    simp only [emit,List.length_append,List.length_cons]
    have hh := ih false
    have hc := hb f x
    linarith

lemma cost_bound (code : Bool → Bool → List Bool) (B : ℕ)
    (hb : ∀ f x, (code f x).length≤B) (f : Bool) (xs : List Bool) (k L : ℕ) :
    cost code f xs k L ≤ xs.length*(2*(k+xs.length)+2*(L+B*xs.length)+B+7) := by
  induction xs generalizing f k L with
  | nil => simp [cost]
  | cons x xs ih =>
    have hh := ih false (k+1) (L+(code f x).length)
    have hc := hb f x
    simp only [cost,List.length_cons]
    calc
      _ ≤ 2*k+2*L+(code f x).length+7 +
          xs.length*(2*((k+1)+xs.length)+2*((L+(code f x).length)+B*xs.length)+B+7) :=
        Nat.add_le_add_left hh _
      _ ≤ 2*(k+(xs.length+1))+2*(L+B*(xs.length+1))+B+7 +
          xs.length*(2*(k+(xs.length+1))+2*(L+B*(xs.length+1))+B+7) := by
        apply Nat.add_le_add
        · nlinarith
        · apply Nat.mul_le_mul_left
          linarith
      _ = _ := by ring

lemma clear_blanks (O : List A) (k : ℕ) :
    Tape.mk₂ (List.replicate k (0:A)) (O++[0])=Tape.mk₁ O := by
  unfold Tape.mk₂ Tape.mk₁
  have hL : ListBlank.mk (List.replicate k (0:A))=ListBlank.mk [] :=
    Quotient.sound (Or.inr ⟨k,by simp⟩)
  have hR : ListBlank.mk (O++[(0:A)])=ListBlank.mk O :=
    Quotient.sound (Or.inr ⟨1,by rfl⟩)
  rw [hL,hR]
  rfl

lemma scan_six_zero (code : Bool → Bool → List Bool) (f b : Bool) (L R : List A) :
    TM1.step (M code) (state 6 f b L (0::R))=some (state 6 f b (0::L) R) := by
  simp [state,TM1.step,TM1.stepAux,M,jump,move]

lemma enter_finish (code : Bool → Bool → List Bool) (out : List Bool) (k : ℕ) (f b : Bool) :
    exec (TM1.step (M code)) 1 (invariant [] k out f b)=
      some (state 6 f b [] (List.replicate (k+2) 0++3::out.map bit++[3])) := by
  simp [exec,invariant,state,TM1.step,M,TM1.stepAux,left_empty,jump,List.replicate_succ]

lemma finish (code : Bool → Bool → List Bool) (out : List Bool) (k : ℕ) (f b : Bool) :
    exec (TM1.step (M code)) (k+2*out.length+7) (invariant [] k out f b)=
      some ⟨none,(f,b),Tape.mk₁ (out.map bit)⟩ := by
  let O := out.map bit
  let Z := List.replicate (k+2) (0:A)
  have h1 : exec (TM1.step (M code)) 1 (invariant [] k out f b)=
      some (state 6 f b [] (Z++3::O++[3])) := by
    simpa only [Z,O] using enter_finish code out k f b
  have h2 : exec (TM1.step (M code)) Z.length (state 6 f b [] (Z++3::O++[3]))=
      some (state 6 f b Z.reverse (3::O++[3])) := by
    have hh := scan_right (M code) 6 (f,b) Z [] (3::O++[3]) (by
      intro a ha L R
      have ha0 : a=0 := by simpa [Z] using ha
      subst a
      exact scan_six_zero code f b L R)
    dsimp [state] at hh ⊢
    simpa only [List.append_nil,List.append_assoc,List.cons_append] using hh

  have h3 : exec (TM1.step (M code)) 1 (state 6 f b Z.reverse (3::O++[3]))=
      some (state 7 f b (3::Z.reverse) (O++[3])) := by
    simp [exec,state,TM1.step,TM1.stepAux,M,jump,move]
  have h4 : exec (TM1.step (M code)) O.length (state 7 f b (3::Z.reverse) (O++[3]))=
      some (state 7 f b (O.reverse++3::Z.reverse) [3]) := by
    apply scan_right
    intro a ha L R
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ha
    simp [TM1.step,TM1.stepAux,M,jump,move,beq_eq_false_iff_ne.mpr (bit_ne_three y)]
  have h5 : exec (TM1.step (M code)) 1 (state 7 f b (O.reverse++3::Z.reverse) [3])=
      some (state 8 f b (O.reverse++3::Z.reverse) [0]) := by
    simp [exec,state,TM1.step,TM1.stepAux,M,jump]
  have h6 : exec (TM1.step (M code)) (O.length+1)
      (state 8 f b (O.reverse++3::Z.reverse) [0])=
      some (state 9 f b Z.reverse (3::O++[0])) := by
    simpa [state,List.reverse_reverse] using
      scan_left (M code) 8 9 (f,b) O.reverse Z.reverse [0] rfl (by
        intro a ha
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
        exact bit_ne_three y)
  have h7 : exec (TM1.step (M code)) 1 (state 9 f b Z.reverse (3::O++[0]))=
      some (⟨none,(f,b),Tape.mk₁ O⟩ : Cfg) := by
    have hc : Tape.mk₂ (0::Z.reverse) (O++[0])=Tape.mk₁ O := by
      have hz : Z.reverse=List.replicate (k+2) (0:A) := by simp only [Z,List.reverse_replicate]
      rw [hz,←List.replicate_succ]
      exact clear_blanks O (k+3)
    simp [exec,state,TM1.step,TM1.stepAux,M,hc]
  have he := exec_trans (exec_trans (exec_trans (exec_trans (exec_trans
    (exec_trans h1 h2) h3) h4) h5) h6) h7
  have ht : k+2*out.length+7 = 1+Z.length+1+O.length+1+(O.length+1)+1 := by
    simp [Z,O]
    omega
  rw [ht]
  exact he

lemma scan_zero_raw (code : Bool → Bool → List Bool) (x : Bool) (v : V) (L R : List A) :
    TM1.step (M code) (⟨some 0,v,Tape.mk₂ L (raw x::R)⟩ : Cfg)=
      some ⟨some 0,v,Tape.mk₂ (raw x::L) R⟩ := by
  simp [TM1.step,TM1.stepAux,M,jump,move,beq_eq_false_iff_ne.mpr (raw_ne_zero x)]

lemma start_markers (code : Bool → Bool → List Bool) (w : List Bool) (v : V) :
    exec (TM1.step (M code)) 1 (⟨some 0,v,Tape.mk₂ (w.map raw) []⟩ : Cfg)=
      some (invariant w 0 [] true false) := by
  simp [exec,TM1.step,M,TM1.stepAux,jump,state,invariant,Tape.mk₂]

lemma start (code : Bool → Bool → List Bool) (w : List Bool) (v : V) :
    exec (TM1.step (M code)) (w.length+1) (⟨some 0,v,Tape.mk₁ (w.map raw)⟩ : Cfg)=
      some (invariant w.reverse 0 [] true false) := by
  have hh := scan_right (M code) 0 v (w.map raw) [] [] (by
    intro a ha L R
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact scan_zero_raw code x v L R)
  have hs : exec (TM1.step (M code)) w.length (⟨some 0,v,Tape.mk₁ (w.map raw)⟩ : Cfg)=
      some ⟨some 0,v,Tape.mk₂ (w.reverse.map raw) []⟩ := by
    simpa [Tape.mk₁,List.map_reverse] using hh
  exact exec_trans hs (start_markers code w.reverse v)

/-- Literal Fin4 raw input is physically erased; no hidden encoded-input
precondition is used. The macrotransition charge is quadratic; TM1 compilation
adds a fixed multiplicative constant for this one fixed adapter machine. -/
theorem prepare (code : Bool → Bool → List Bool) (B : ℕ)
    (hb : ∀ f x, (code f x).length≤B) (w : List Bool) (v : V) :
    ∃ t ≤ (4*B+12)*(w.length+1)^2, ∃ v',
      exec (TM1.step (M code)) t (⟨some 0,v,Tape.mk₁ (w.map raw)⟩ : Cfg)=
        some ⟨none,v',Tape.mk₁ ((emit code true w.reverse).map bit)⟩ := by
  obtain ⟨f,b,hh⟩ := all_process code w.reverse [] 0 true false
  simp only [Nat.zero_add,List.nil_append,List.length_nil,List.length_reverse] at hh
  have hf := finish code (emit code true w.reverse) w.length f b
  have he := exec_trans (exec_trans (start code w v) hh) hf
  refine ⟨_,?_,(f,b),he⟩
  have ht := cost_bound code B hb true w.reverse 0 0
  have hl := emit_length code B hb true w.reverse
  simp only [List.length_reverse,Nat.zero_add] at ht hl
  calc
    _ ≤ (w.length+1)+w.length*(2*w.length+2*(B*w.length)+B+7)+
        (w.length+2*(B*w.length)+7) := by omega
    _ ≤ (4*B+12)*(w.length+1)^2 := by
      linarith [Nat.zero_le (B*w.length*w.length),Nat.zero_le (B*w.length),
        Nat.zero_le (w.length*w.length)]

end RationalHitting.TMTime.InputAdapter

namespace RationalHitting.TMTime.InputAdapter
open Turing

lemma emit_false (code : Bool → Bool → List Bool) (xs : List Bool) :
    emit code false xs=xs.flatMap (code false) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [emit,ih]

lemma stack_encoding {K : Type} [DecidableEq K] (k : K) (b : ℕ)
    (enc : TM2to1.Γ' K (fun _ => Bool) → List.Vector Bool b)
    (w : List Bool) (hw : w≠[]) :
    emit (fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList) true w.reverse=
      (TM2to1.trInit k w).flatMap (fun a => (enc a).toList) := by
  cases he : w.reverse with
  | nil => simp only [List.reverse_eq_nil_iff] at he; exact False.elim (hw he)
  | cons x xs =>
    unfold TM2to1.trInit
    rw [he]
    change (enc (true,Function.update (fun _ => none) k (some x))).toList ++
      emit (fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList) false xs =
      (enc (true,Function.update (fun _ => none) k (some x))).toList ++
        ((xs.map (fun a => (false,Function.update (fun _ => none) k (some a)))).flatMap
          (fun a => (enc a).toList))
    rw [emit_false]
    exact congrArg (fun l => (enc (true,Function.update (fun _ => none) k (some x))).toList ++ l)
      (List.flatMap_map (fun a => (false,Function.update (fun _ => none) k (some a)))
        (fun a => (enc a).toList) xs).symm


/-- Real finite TM0 raw-input adapter, at quadratic bit cost, reaching exactly
Mathlib's initial tape for the binary stack simulator, not an assumed encoding. -/
theorem raw_stack_input {K : Type} [DecidableEq K] (k : K) (b : ℕ)
    (enc : TM2to1.Γ' K (fun _ => Bool) → List.Vector Bool b) :
    ∃ (m : ℕ) (G : TM0.Machine A (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ w : List Bool, w≠[] → ∃ t≤C*(w.length+1)^2, ∃ a : TM0.Cfg A (Fin (m+1)),
        exec (TM0.step G) t (TM0.init (w.map raw))=some a ∧ TM0.step G a=none ∧
        a.Tape=Tape.mk₁ (((TM2to1.trInit k w).flatMap (fun z => (enc z).toList)).map bit) := by
  let code := fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList
  obtain ⟨m,G,D,hD,hG⟩ := OneToZero.finite_compiler (M code)
  refine ⟨m,G,D*(4*b+12),by positivity,?_⟩
  intro w hw
  obtain ⟨t,ht,v,hx⟩ := prepare code b (by intro f x; simp [code]) w default
  obtain ⟨u,hu,a,ha,hh,he⟩ := hG (w.map raw) t _ hx (by rfl)
  refine ⟨u,hu.trans ?_,a,ha,hh,?_⟩
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left D ht
  · simpa only [TM1.Cfg.Tape,code,stack_encoding k b enc w hw] using he

end RationalHitting.TMTime.InputAdapter

/-! Required reverse interface from a block-coded finite stack simulator to
literal Fin4 output digits. All registers of this transducer are finite. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.OutputAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.OutputAdapter
open Turing

lemma fill_apply {b} (is : List (Fin b)) (w v : Word b) (j : Fin b) :
    fill is w v j=if j∈is then w j else v j := by
  induction is generalizing v with
  | nil => simp [fill]
  | cons i is ih =>
    simp only [fill,List.foldl_cons] at *
    rw [ih]
    by_cases hi : j=i <;> by_cases hj : j∈is <;> simp_all

@[simp] lemma fill_all {b} (w v : Word b) : fill (List.finRange b) w v=w := by
  funext j
  simp [fill_apply]

lemma readBlock_spec {b} (is : List (Fin b)) (w v : Word b) (x : Option Bool)
    (q : Stmt b) (L R : List A) :
    TM1.stepAux (readBlock is q) (v,x) (Tape.mk₂ L (is.map (fun i => bit (w i))++R))=
      TM1.stepAux q (fill is w v,x) (Tape.mk₂ (List.replicate is.length 0++L) R) := by
  induction is generalizing v L with
  | nil => simp [readBlock,fill]
  | cons i is ih =>
    simp only [readBlock,List.map_cons,List.cons_append,TM1.stepAux,head₂,List.headI_cons,
      bit_beq_one,write₂,List.tail_cons,right₂,ih,fill,List.foldl_cons,List.length_cons]
    congr 2
    simp [List.replicate_succ',List.append_assoc]

lemma scan_right {b} (F : Q → Stmt b) (q : Q) (v : V b) (l L R : List A)
    (h : ∀ a∈l, ∀ L R, TM1.step F (state q v L (a::R))=some (state q v (a::L) R)) :
    exec (TM1.step F) l.length (state q v L (l++R))=
      some (state q v (l.reverse++L) R) := by
  induction l generalizing L R with
  | nil => simp
  | cons a l ih =>
    have hs := h a (by simp) L (l++R)
    simp only [List.cons_append,List.length_cons,exec,hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using ih (a::L) R (fun z hz => h z (by simp [hz]))

lemma scan_left {b} (F : Q → Stmt b) (q r : Q) (v : V b) (l L R : List A)
    (hF : F q=leftTo q r) (hl : ∀ a∈l, a≠3) :
    exec (TM1.step F) (l.length+1) (state q v (l++3::L) R)=
      some (state r v L (3::l.reverse++R)) := by
  induction l generalizing R with
  | nil => simp [exec,state,TM1.step,hF,leftTo,jump,TM1.stepAux,Tape.mk₂]
  | cons a l ih =>
    have ha := hl a (by simp)
    have hh := ih (a::R) (fun z hz => hl z (by simp [hz]))
    have hs : TM1.step F (state q v ((a::l)++3::L) R)=
        some (state q v (l++3::L) (a::R)) := by
      simp [state,TM1.step,hF,leftTo,TM1.stepAux,beq_eq_false_iff_ne.mpr ha,jump]
    change (TM1.step F _).bind (exec (TM1.step F) (l.length+1)) = _
    rw [hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using hh

lemma zeros_cons (k : ℕ) (L : List A) :
    List.replicate k (0:A)++0::L=0::(List.replicate k 0++L) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons 0) ih

lemma consume_some {b} (get : Word b → Option Bool) (w : Word b) (x : Bool)
    (hx : get w=some x) (gap : ℕ) (out : List Bool) (R : List A) (v : V b) :
    exec (TM1.step (M get)) 1 (invariant gap out (block w++R) v)=
      some (state 2 (w,some x) (List.replicate (gap+b) 0++3::out.reverse.map raw++[3]) (3::R)) := by
  rcases v with ⟨va,vo⟩
  simp only [exec,TM1.step,invariant,state,M,TM1.stepAux,write₂,List.tail_cons,right₂,
    block,readBlock_spec,fill_all,List.length_finRange,hx,Option.isSome_some,Bool.cond_true,
    zeros_cons,left₂,jump,Option.bind_some]
  simp only [List.replicate_add,List.append_assoc,Nat.add_comm,List.cons_append]

lemma emit_one {b} (hb : 1≤b) (get : Word b → Option Bool) (w : Word b) (x : Bool)
    (hx : get w=some x) (gap : ℕ) (out : List Bool) (R : List A) (v : V b) :
    exec (TM1.step (M get)) (2*(gap+b)+3) (invariant gap out (block w++R) v)=
      some (invariant (gap+b-1) (out++[x]) R (w,some x)) := by
  let L := out.reverse.map raw++[3]
  let Z := List.replicate (gap+b) (0:A)
  let Z' := List.replicate (gap+b-1) (0:A)
  have h1 := consume_some get w x hx gap out R v
  have h2 : exec (TM1.step (M get)) (gap+b+1)
      (state 2 (w,some x) (Z++3::L) (3::R))=
      some (state 3 (w,some x) L (3::Z++3::R)) := by
    simpa [Z] using scan_left (M get) 2 3 (w,some x) Z L (3::R) rfl (by
      intro a ha
      have hz : a=0 := by exact (List.mem_replicate.mp ha).2
      subst a
      decide)
  have hZ : Z=0::Z' := by
    dsimp [Z,Z']
    have ht : gap+b=(gap+b-1)+1 := by omega
    rw [ht,List.replicate_succ]
    simp only [Nat.add_sub_cancel]
  have h3 : exec (TM1.step (M get)) 1 (state 3 (w,some x) L (3::Z++3::R))=
      some (state 4 (w,some x) (3::raw x::L) (Z'++3::R)) := by
    simp [state,exec,TM1.step,M,TM1.stepAux,jump,move,hZ]
  have h4 : exec (TM1.step (M get)) Z'.length (state 4 (w,some x) (3::raw x::L) (Z'++3::R))=
      some (state 4 (w,some x) (Z'.reverse++3::raw x::L) (3::R)) := by
    apply scan_right
    intro a ha L R
    have hz : a=0 := by exact (List.mem_replicate.mp ha).2
    subst a
    simp [state,TM1.step,M,TM1.stepAux,jump,move]
  have h5 : exec (TM1.step (M get)) 1 (state 4 (w,some x) (Z'.reverse++3::raw x::L) (3::R))=
      some (invariant (gap+b-1) (out++[x]) R (w,some x)) := by
    simp [state,invariant,exec,TM1.step,M,TM1.stepAux,jump,move,Z',L,
      List.reverse_append,List.append_assoc]
  have h1' : exec (TM1.step (M get)) 1 (invariant gap out (block w++R) v)=
      some (state 2 (w,some x) (Z++3::L) (3::R)) := by
    simpa only [Z,L,List.cons_append,List.append_assoc] using h1
  have he := exec_trans (exec_trans (exec_trans (exec_trans h1' h2) h3) h4) h5
  have ht : 2*(gap+b)+3=1+(gap+b+1)+1+Z'.length+1 := by
    simp only [Z',List.length_replicate]
    omega
  rw [ht]
  exact he

lemma consume_none {b} (get : Word b → Option Bool) (w : Word b)
    (hx : get w=none) (gap : ℕ) (out : List Bool) (v : V b) :
    exec (TM1.step (M get)) 1 (invariant gap out (block w) v)=
      some (state 5 (w,none) (List.replicate (gap+b+1) 0++3::out.reverse.map raw++[3]) []) := by
  rcases v with ⟨va,vo⟩
  have he : block w=block w++[] := by simp
  rw [he]
  simp only [exec,TM1.step,invariant,state,M,TM1.stepAux,write₂,List.tail_cons,right₂,
    block,readBlock_spec,fill_all,List.length_finRange,hx,Option.isSome_none,Bool.cond_false,
    jump,Option.bind_some]
  simp only [List.replicate_add,List.replicate_succ,List.append_assoc,
    List.cons_append,zeros_cons]
  congr 3
  simp only [←List.append_assoc,←List.replicate_add,Nat.add_comm]

lemma clear_blanks (l r : ℕ) (w : List A) :
    Tape.mk₂ (List.replicate l (0:A)) (w++List.replicate r 0)=Tape.mk₁ w := by
  have hl : ListBlank.mk (List.replicate l (0:A))=ListBlank.mk ([] : List A) := by
    apply Quotient.sound
    exact Or.inr ⟨l,by simp⟩
  have hr : ListBlank.mk (w++List.replicate r (0:A))=ListBlank.mk w := by
    apply Quotient.sound
    exact Or.inr ⟨r,rfl⟩
  simp only [Tape.mk₂,Tape.mk₁,hl,hr]

lemma finish {b} (get : Word b → Option Bool) (w : Word b)
    (hx : get w=none) (gap : ℕ) (out : List Bool) (v : V b) :
    exec (TM1.step (M get)) (gap+b+out.length+6) (invariant gap out (block w) v)=
      some ⟨none,(w,none),Tape.mk₁ (out.map raw)⟩ := by
  let L := out.reverse.map raw
  let Z := List.replicate (gap+b+1) (0:A)
  have h1 := consume_none get w hx gap out v
  have h2 : exec (TM1.step (M get)) (gap+b+2)
      (state 5 (w,none) (Z++3::L++[3]) [])=
      some (state 6 (w,none) (L++[3]) (3::Z)) := by
    simpa [Z,List.append_assoc] using scan_left (M get) 5 6 (w,none) Z (L++[3]) [] rfl (by
      intro a ha
      have ha' : a=0 := (List.mem_replicate.mp ha).2
      subst a
      decide)
  have h3 : exec (TM1.step (M get)) 1 (state 6 (w,none) (L++[3]) (3::Z))=
      some (state 7 (w,none) (L++[3]) (0::Z)) := by
    simp [exec,state,TM1.step,M,TM1.stepAux,jump]
  have h4 : exec (TM1.step (M get)) (out.length+1)
      (state 7 (w,none) (L++[3]) (0::Z))=
      some (state 8 (w,none) [] (3::L.reverse++0::Z)) := by
    simpa [L] using scan_left (M get) 7 8 (w,none) L [] (0::Z) rfl (by
      intro a ha
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      exact raw_ne_three x)
  have h5 : exec (TM1.step (M get)) 1 (state 8 (w,none) [] (3::L.reverse++0::Z))=
      some ⟨none,(w,none),Tape.mk₁ (out.map raw)⟩ := by
    simp only [exec,TM1.step,state,M,TM1.stepAux,write₂,List.cons_append,List.tail_cons,
      right₂,Option.bind_some]
    have he : L.reverse++0::Z=out.map raw++List.replicate (gap+b+2) 0 := by
      simp [L,Z,List.replicate_succ]
    rw [he]
    have hc := clear_blanks 1 (gap+b+2) (out.map raw)
    exact congrArg (fun t => some (TM1.Cfg.mk none (w,none) t)) hc
  have h1' : exec (TM1.step (M get)) 1 (invariant gap out (block w) v)=
      some (state 5 (w,none) (Z++3::L++[3]) []) := h1
  have he := exec_trans (exec_trans (exec_trans (exec_trans h1' h2) h3) h4) h5
  have ht : gap+b+out.length+6=1+(gap+b+2)+1+(out.length+1)+1 := by omega
  rw [ht]
  exact he

lemma decode_stream {b} (hb : 1≤b) (get : Word b → Option Bool)
    (code : Bool → Bool → Word b) (stop : Bool → Word b)
    (hc : ∀ f x,get (code f x)=some x) (hs : ∀ f,get (stop f)=none)
    (xs : List Bool) (f : Bool) (gap : ℕ) (out : List Bool) (v : V b) :
    ∃ u : V b, exec (TM1.step (M get)) (cost b gap out.length xs.length)
      (invariant gap out (stream code stop f xs) v)=
      some ⟨none,u,Tape.mk₁ ((out++xs).map raw)⟩ := by
  induction xs generalizing f gap out v with
  | nil =>
    refine ⟨(stop f,none),?_⟩
    simpa only [stream,List.length_nil,cost,List.append_nil] using finish get (stop f) (hs f) gap out v
  | cons x xs ih =>
    obtain ⟨u,hu⟩ := ih false (gap+b-1) (out++[x]) (code f x,some x)
    refine ⟨u,?_⟩
    have he := exec_trans (emit_one hb get (code f x) x (hc f x) gap out
      (stream code stop false xs) v) hu
    simpa only [stream,List.length_cons,cost,List.length_append,List.length_singleton,List.length_nil,Nat.zero_add,
      List.append_assoc,List.singleton_append] using he

lemma cost_bound (b gap len n : ℕ) :
    cost b gap len n≤(n+1)*(3*(gap+b*(n+1)+len+n+10)) := by
  induction n generalizing gap len with
  | zero => simp only [cost,Nat.zero_add,Nat.add_zero,Nat.mul_one,Nat.one_mul]; omega
  | succ n ih =>
    rw [cost]
    have hi := ih (gap+b-1) (len+1)
    let H := gap+b*(n+1+1)+len+(n+1)+10
    have hH : gap+b-1+b*(n+1)+(len+1)+n+10≤H := by
      dsimp [H]
      simp only [Nat.mul_add,Nat.mul_one]
      omega
    have hh : 2*(gap+b)+3≤3*H := by
      dsimp [H]
      linarith [Nat.zero_le (b*n)]
    calc _ ≤ 2*(gap+b)+3+(n+1)*(3*(gap+b-1+b*(n+1)+(len+1)+n+10)) := Nat.add_le_add_left hi _
         _ ≤ 2*(gap+b)+3+(n+1)*(3*H) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hH)) _
         _ ≤ (n+1+1)*(3*H) := by linarith only [hh]

lemma start {b} (get : Word b → Option Bool) (R : List A) (v : V b) :
    exec (TM1.step (M get)) 1 ⟨some 0,v,Tape.mk₁ R⟩=
      some (invariant 0 [] R v) := by
  change exec (TM1.step (M get)) 1 (state 0 v [] R)=_
  simp [state,invariant,exec,TM1.step,M,TM1.stepAux,jump,move]

/-- Literal block input to literal digit output; both head position and blank
outside the output are guaranteed, with quadratic bit-time. -/
theorem prepare {b} (hb : 1≤b) (get : Word b → Option Bool)
    (code : Bool → Bool → Word b) (stop : Bool → Word b)
    (hc : ∀ f x,get (code f x)=some x) (hs : ∀ f,get (stop f)=none)
    (xs : List Bool) :
    ∃ t≤(3*b+34)*(xs.length+1)^2, ∃ u : V b,
      exec (TM1.step (M get)) t (TM1.init (stream code stop true xs))=
        some ⟨none,u,Tape.mk₁ (xs.map raw)⟩ := by
  obtain ⟨u,hu⟩ := decode_stream hb get code stop hc hs xs true 0 [] default
  refine ⟨1+cost b 0 0 xs.length,?_,u,?_⟩
  · have hh := cost_bound b 0 0 xs.length
    simp only [Nat.zero_add,Nat.add_zero] at hh
    nlinarith [Nat.zero_le (b*(xs.length+1)^2)]
  · exact exec_trans (start get _ default) hu

/-- A genuine Fin4 finite TM0 output transducer; the encoding/decoding functions
are fixed finite tables and no unbounded state or oracle is used. -/
theorem finite_output {b} (hb : 1≤b) (get : Word b → Option Bool)
    (code : Bool → Bool → Word b) (stop : Bool → Word b)
    (hc : ∀ f x,get (code f x)=some x) (hs : ∀ f,get (stop f)=none) :
    ∃ (m : ℕ) (G : TM0.Machine A (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ xs : List Bool, ∃ t≤C*(xs.length+1)^2, ∃ a,
        exec (TM0.step G) t (TM0.init (stream code stop true xs))=some a ∧
        TM0.step G a=none ∧ a.Tape=Tape.mk₁ (xs.map raw) := by
  obtain ⟨m,G,D,hD,hG⟩ := OneToZero.finite_compiler (M get)
  refine ⟨m,G,D*(3*b+34),by positivity,?_⟩
  intro xs
  obtain ⟨t,ht,u,hu⟩ := prepare hb get code stop hc hs xs
  obtain ⟨v,hv,a,ha,hh,he⟩ := hG _ t _ hu rfl
  refine ⟨v,hv.trans ?_,a,ha,hh,he⟩
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left D ht

end RationalHitting.TMTime.OutputAdapter

namespace RationalHitting.TMTime.StackTape
open Turing

/-- At the boundary of a stack macrostep, the simulator's tape is determined
by the actual stack contents. There is no junk-cell assumption. -/
lemma unique {K Λ σ : Type*} {Γ : K → Type*}
    {a b : TM2.Cfg Γ Λ σ} {c d : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ}
    (h : TM2to1.TrCfg a c) (h' : TM2to1.TrCfg b d) (hs : a.stk=b.stk) : c.Tape=d.Tape := by
  cases h with
  | mk L hL =>
    cases h' with
    | mk L' hL' =>
      have he : L=L' := by
        apply ListBlank.ext
        intro i
        funext k
        have hh := (hL k).trans ((congrArg (fun S => ListBlank.mk ((S k).map some).reverse) hs).trans (hL' k).symm)
        have hh' := congrArg (fun T => T.nth i) hh
        simpa only [ListBlank.nth_map,proj,PointedMap.mk_val] using hh'
      rw [he]

lemma clean {K Λ σ : Type*} [DecidableEq K] [Inhabited Λ] [Inhabited σ]
    (k : K) (w : List Bool)
    {c : TM1.Cfg (TM2to1.Γ' K (fun _ => Bool)) (TM2to1.Λ' K (fun _ => Bool) Λ σ) σ}
    (h : TM2to1.TrCfg
      (⟨none,default,Function.update (fun _ => []) k w⟩ : TM2.Cfg (fun _ : K => Bool) Λ σ) c) :
    c.Tape=Tape.mk₁ (TM2to1.trInit k w) := by
  exact unique h (TM2to1.trCfg_init (Γ:=fun _ => Bool) (Λ:=Λ) (σ:=σ) k w) rfl

end RationalHitting.TMTime.StackTape

namespace RationalHitting.TMTime.OutputAdapter
open Turing

lemma blockVector {b} (v : List.Vector Bool b) :
    block v.get=v.toList.map bit := by
  have he : List.ofFn v.get=v.toList := by
    rw [←List.Vector.toList_ofFn,List.Vector.ofFn_get]
  rw [block,←List.ofFn_eq_map]
  change List.ofFn (bit ∘ v.get)=_
  rw [←List.map_ofFn,he]

variable {K : Type} [DecidableEq K]

lemma getter_code {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b)
    (dec : List.Vector Bool b → StackAlphabet K) (hd : ∀ a,dec (enc a)=a) (f x : Bool) :
    getter k dec (code k enc f x)=some x := by
  unfold getter code
  rw [List.Vector.ofFn_get]
  exact (congrArg (fun a : StackAlphabet K => a.2 k) (hd (f,Function.update (fun _ => none) k (some x)))).trans (Function.update_self k (some x) (fun _ => none))

lemma getter_stop {K : Type} [DecidableEq K] {b : ℕ} (k : K)
  (enc : RationalHitting.TMTime.OutputAdapter.StackAlphabet K → List.Vector Bool b)
  (dec : List.Vector Bool b → RationalHitting.TMTime.OutputAdapter.StackAlphabet K)
  (hd : ∀ (a : RationalHitting.TMTime.OutputAdapter.StackAlphabet K), dec (enc a) = a)
  (f : Bool) :
  RationalHitting.TMTime.OutputAdapter.getter k dec
      (RationalHitting.TMTime.OutputAdapter.stop enc f) =
    none := by
  unfold getter stop
  rw [List.Vector.ofFn_get]
  exact congrArg (fun a : StackAlphabet K => a.2 k) (hd (f,fun _ => none))

lemma stream_false {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b) (xs : List Bool) :
    stream (code k enc) (stop enc) false xs=
      (xs.flatMap (fun x => (enc (false,Function.update (fun _ => none) k (some x))).toList)).map bit ++
      block (stop enc false) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [stream,code,blockVector,List.flatMap_cons,List.map_append,List.append_assoc,ih]

lemma stream_encoding {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b)
    (h0 : enc default=List.Vector.replicate b false) (xs : List Bool) :
    Tape.mk₁ (stream (code k enc) (stop enc) true xs)=
      Tape.mk₁ (((TM2to1.trInit k xs.reverse).flatMap (fun z => (enc z).toList)).map bit) := by
  cases xs with
  | nil =>
    change Tape.mk₁ (block (enc (true,fun _ => none)).get)=_
    rw [blockVector]
    have he : TM2to1.trInit (Γ:=fun _ : K => Bool) k ([] : List Bool)=[(true,fun _ => none)] := rfl
    rw [List.reverse_nil,he]
    change Tape.mk₁ ((enc (true,fun _ => none)).toList.map bit)=
      Tape.mk₁ (((enc (true,fun _ => none)).toList++[]).map bit)
    rw [List.append_nil]
  | cons x xs =>
    have he := InputAdapter.stack_encoding k b enc (x::xs).reverse (by simp)
    simp only [List.reverse_reverse] at he
    have ht : stream (code k enc) (stop enc) true (x::xs)=
        (InputAdapter.emit (fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList)
          true (x::xs)).map bit ++ List.replicate b 0 := by
      rw [stream,stream_false]
      simp only [code,blockVector,InputAdapter.emit,InputAdapter.emit_false,List.map_append,List.append_assoc]
      have hh : block (stop enc false)=List.replicate b 0 := by
        change block (enc default).get=_
        rw [blockVector,h0]
        change (List.replicate b false).map bit=List.replicate b 0
        exact List.map_replicate
      rw [hh]
    rw [ht,he]
    exact clear_blanks 0 b _

lemma width_pos {K : Type} [DecidableEq K] {b : ℕ}
  (enc : RationalHitting.TMTime.OutputAdapter.StackAlphabet K → List.Vector Bool b)
  (dec : List.Vector Bool b → RationalHitting.TMTime.OutputAdapter.StackAlphabet K)
  (hd : ∀ (a : RationalHitting.TMTime.OutputAdapter.StackAlphabet K), dec (enc a) = a) : 1 ≤ b := by
  by_contra hb
  have hb' : b=0 := by omega
  subst b
  have hh : enc default=enc (true,fun _ => none) := Subsingleton.elim _ _
  have he : (default : StackAlphabet K)=(true,fun _ => none) :=
    (hd _).symm.trans ((congrArg dec hh).trans (hd _))
  have hf := congrArg Prod.fst he
  exact Bool.false_ne_true hf

/-- Exact inverse interface for a clean output stack, including the bottom
marker, right-side blank padding and output order. -/
theorem raw_stack_output {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b)
    (dec : List.Vector Bool b → StackAlphabet K) (h0 : enc default=List.Vector.replicate b false)
    (hd : ∀ a,dec (enc a)=a) :
    ∃ (m : ℕ) (G : TM0.Machine A (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ xs : List Bool, ∃ t≤C*(xs.length+1)^2, ∃ a,
        exec (TM0.step G) t (TM0.init
          (((TM2to1.trInit k xs.reverse).flatMap (fun z => (enc z).toList)).map bit))=some a ∧
        TM0.step G a=none ∧ a.Tape=Tape.mk₁ (xs.map raw) := by
  obtain ⟨m,G,C,hC,hG⟩ := finite_output (width_pos enc dec hd) (getter k dec) (code k enc) (stop enc)
    (getter_code k enc dec hd) (getter_stop k enc dec hd)
  refine ⟨m,G,C,hC,?_⟩
  intro xs
  obtain ⟨t,ht,a,ha,hh,he⟩ := hG xs
  refine ⟨t,ht,a,?_,hh,he⟩
  have hi : TM0.init (stream (code k enc) (stop enc) true xs)=
      (TM0.init (((TM2to1.trInit k xs.reverse).flatMap (fun z => (enc z).toList)).map bit) : TM0.Cfg A (Fin (m+1))) := by
    exact congrArg (TM0.Cfg.mk default) (stream_encoding k enc h0 xs)
  rwa [hi] at ha

end RationalHitting.TMTime.OutputAdapter

/-! Literal tape-preserving linkage for the raw-input/stack/output compiler.
There is no implicit recoding between machines. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Compiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.Link
open Turing
variable {Γ Λ Δ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Δ]

attribute [local instance] OAI.RationalHitting.TMTime.Link.sumInhabited
lemma step_left (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    {a b : TM0.Cfg Γ Λ} (h : TM0.step F a=some b) :
    TM0.step (machine F G) (left a)=some (left b) := by
  rcases a with ⟨q,T⟩
  simp only [TM0.step] at h
  cases he : F q T.head with
  | none => simp [he] at h
  | some qr =>
    rcases qr with ⟨r,s⟩
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst b
    cases s <;> simp [TM0.step,machine,left,he]

lemma switch (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    {a : TM0.Cfg Γ Λ} (h : TM0.step F a=none) :
    TM0.step (machine F G) (left a)=some (right (⟨default,a.Tape⟩ : TM0.Cfg Γ Δ)) := by
  have he : F a.q a.Tape.head=none := Option.map_eq_none_iff.mp h
  simp [TM0.step,machine,left,right,he]

lemma step_right (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ) (a : TM0.Cfg Γ Δ) :
    TM0.step (machine F G) (right a)=(TM0.step G a).map right := by
  rcases a with ⟨q,T⟩
  simp only [TM0.step,machine,right,Option.map_map]
  congr 1

lemma run_left (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    (t : ℕ) {a b : TM0.Cfg Γ Λ} (h : exec (TM0.step F) t a=some b) :
    exec (TM0.step (machine F G)) t (left a)=some (left b) := by
  induction t generalizing a with
  | zero => simpa only [exec_zero,Option.some.injEq] using congrArg (fun x => left (Δ:=Δ) x) (Option.some.inj h)
  | succ t ih =>
    obtain ⟨c,hc,hr⟩ := Option.bind_eq_some_iff.mp h
    simp only [exec,step_left F G hc,Option.bind_some]
    exact ih hr

lemma run_right (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    (t : ℕ) (a : TM0.Cfg Γ Δ) :
    exec (TM0.step (machine F G)) t (right a)=(exec (TM0.step G) t a).map right := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    simp only [exec,step_right]
    cases TM0.step G a <;> simp [ih]

/-- Splice two halting finite transducers with exactly one glue step. The
intermediate output is the literal tape required by the second input. -/
theorem finite_sequence [Fintype Λ] [Fintype Δ]
    (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ) :
    ∃ (m : ℕ) (H : TM0.Machine Γ (Fin (m+1))),
      ∀ (w v : List Γ) (t u : ℕ) (a : TM0.Cfg Γ Λ) (b : TM0.Cfg Γ Δ),
        exec (TM0.step F) t (TM0.init w)=some a → TM0.step F a=none →
        a.Tape=Tape.mk₁ v → exec (TM0.step G) u (TM0.init v)=some b → TM0.step G b=none →
        ∃ c, exec (TM0.step H) (t+1+u) (TM0.init w)=some c ∧ TM0.step H c=none ∧ c.Tape=b.Tape := by
  classical
  let S : Finset (Sum Λ Δ) := Finset.univ
  have hs : TM0.Supports (machine F G) (S : Set (Sum Λ Δ)) := by
    constructor
    · simp [S]
    · intro q hq a r s hr
      simp [S]
  obtain ⟨m,H,hH⟩ := FiniteStates.finite_machine (machine F G) S hs
  refine ⟨m,H,?_⟩
  intro w v t u a b ha hh ht hb hh'
  have h1 : exec (TM0.step (machine F G)) t (TM0.init w)=some (left a) := run_left F G t ha
  have h2 : exec (TM0.step (machine F G)) 1 (left a)=some (right (TM0.init v)) := by
    simp only [exec,switch F G hh,Option.bind_some,TM0.init,ht]
  have h3 : exec (TM0.step (machine F G)) u (right (TM0.init v))=some (right b) := by
    rw [run_right,hb,Option.map_some]
  have hr := exec_trans (exec_trans h1 h2) h3
  exact hH w (t+1+u) (right b) hr (by rw [step_right,hh',Option.map_none])

end RationalHitting.TMTime.Link

namespace RationalHitting.TMTime.BinaryLift
open Turing
variable {Λ : Type*} [Inhabited Λ]
lemma run (F : TM0.Machine Bool Λ) (t : ℕ) (a : TM0.Cfg Bool Λ) :
    exec (TM0.step (machine F)) t (cfg a)=(exec (TM0.step F) t a).map cfg := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    simp only [exec,step]
    cases TM0.step F a <;> simp [ih]

lemma run_init (F : TM0.Machine Bool Λ) (w : List Bool) (t : ℕ) (a : TM0.Cfg Bool Λ)
    (hr : exec (TM0.step F) t (TM0.init w)=some a) (hh : TM0.step F a=none) :
    exec (TM0.step (machine F)) t (TM0.init (w.map bit))=some (cfg a) ∧
      TM0.step (machine F) (cfg a)=none := by
  have hi : cfg (Λ:=Λ) (TM0.init w)=TM0.init (w.map bit) := by
    simp only [cfg,TM0.init,Tape.map_mk₁,bitMap]
  constructor
  · rw [←hi,run,hr,Option.map_some]
  · rw [step,hh,Option.map_none]
end RationalHitting.TMTime.BinaryLift

namespace RationalHitting.TMTime.Alphabet
open Turing
lemma tape_init {Γ : Type*} [Inhabited Γ] {b : ℕ}
    (enc : Γ → List.Vector Bool b) (h0 : enc default=List.Vector.replicate b false) (w : List Γ) :
    TM1to1.trTape h0 (Tape.mk₁ w)=Tape.mk₁ (w.flatMap (fun a => (enc a).toList)) := by
  exact congrArg TM1.Cfg.Tape (compiled_init (Λ:=Unit) (σ:=Unit) enc h0 w)
end RationalHitting.TMTime.Alphabet

namespace RationalHitting.StackLanguage.Compiler
open Turing RationalHitting.TMTime
variable {K : Type} [DecidableEq K] [Fintype K]

/-- End-to-end, finite-state, Fin4 one-tape compilation. Input and output are
literal 1/2 digit strings, NOT different encodings hidden by an interface. The
stack program is a single fixed finite syntax tree. Final scratch must be empty;
the designated output stack has reversed output order, as explicitly stated. -/
theorem raw_compilation (p : Program K) (ki ko : K) :
    ∃ (m : ℕ) (G : TM0.Machine (Fin 4) (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ (w xs : List Bool) (t : ℕ), w≠[] →
        Eval p (Function.update (fun _ => []) ki w)
          (Function.update (fun _ => []) ko xs.reverse) t →
        ∃ u≤C*(w.length+t+xs.length+3)^2, ∃ a,
          exec (TM0.step G) u (TM0.init (w.map InputAdapter.raw))=some a ∧
          TM0.step G a=none ∧ a.Tape=Tape.mk₁ (xs.map OutputAdapter.raw) := by
  classical
  obtain ⟨b,enc,dec,h0,hd,m₁,F,B,hB,hF⟩ := binary_compilation p
  obtain ⟨m₀,I,A,hA,hI⟩ := InputAdapter.raw_stack_input ki b enc
  obtain ⟨m₂,O,D,hD,hO⟩ := OutputAdapter.raw_stack_output ko enc dec h0 hd
  obtain ⟨m₃,J,hJ⟩ := Link.finite_sequence I (BinaryLift.machine F)
  obtain ⟨m₄,H,hH⟩ := Link.finite_sequence J O
  refine ⟨m₄,H,A+B+D+2,by omega,?_⟩
  intro w xs t hw he
  obtain ⟨i,hi,a,ha,hha,hta⟩ := hI w hw
  obtain ⟨j,hj,c,hc,hhc,e,htr,htc⟩ := hF ki w (Function.update (fun _ => []) ko xs.reverse) t he
  obtain ⟨hlift,hhlift⟩ := BinaryLift.run_init F _ j c hc hhc
  have hcle : c.Tape=Tape.mk₁ ((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)) := by
    rw [htc,StackTape.clean ko xs.reverse htr,Alphabet.tape_init]
  have hcl : (BinaryLift.cfg c).Tape=Tape.mk₁
      (((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)).map InputAdapter.bit) := by
    simp only [BinaryLift.cfg,hcle,Tape.map_mk₁]
    rfl
  obtain ⟨a₃,ha₃,hh₃,ht₃⟩ := hJ (w.map InputAdapter.raw)
    (((TM2to1.trInit ki w).flatMap (fun z => (enc z).toList)).map InputAdapter.bit)
    i j a (BinaryLift.cfg c) ha hha hta (by rw [show InputAdapter.bit = BinaryLift.bit from rfl]; exact hlift) hhlift
  have hxt : a₃.Tape=Tape.mk₁
      (((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)).map InputAdapter.bit) := ht₃.trans hcl
  obtain ⟨k,hk,a₂,ha₂,hh₂,ht₂⟩ := hO xs
  obtain ⟨a₄,ha₄,hh₄,ht₄⟩ := hH (w.map InputAdapter.raw)
    (((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)).map InputAdapter.bit)
    (i+1+j) k a₃ a₂ ha₃ hh₃ hxt ha₂ hh₂
  refine ⟨i+1+j+1+k,?_,a₄,ha₄,hh₄,ht₄.trans ht₂⟩
  let R := w.length+t+xs.length+3
  have hi' : i≤A*R^2 := hi.trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega : w.length+1≤R) 2))
  have hj' : j≤B*R^2 := hj.trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_left (by omega : w.length+t+3≤R) 2))
  have hk' : k≤D*R^2 := hk.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left (by omega : xs.length+1≤R) 2))
  have hR : 1≤R^2 := one_le_pow₀ (by dsimp [R]; omega)
  change i+1+j+1+k≤(A+B+D+2)*R^2
  linarith only [hi',hj',hk',hR]

end RationalHitting.StackLanguage.Compiler


namespace RationalHitting.ExecutableGenerator
open Turing StackLanguage TMTime

lemma run_eq_exec {m : ℕ} (G : Machine m) (t : ℕ) (a : Config m) :
    run G t a = exec (TM0.step G) t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih => simp only [run,exec,ih]

lemma unaryWord_raw (n s : ℕ) : (unaryWord n s).map TMTime.InputAdapter.raw = unaryInput n s := by
  simp [unaryWord,unaryInput,TMTime.InputAdapter.raw]

lemma encoded_raw (n s : ℕ) : (encoded n s).map TMTime.OutputAdapter.raw =
    (encodeOutput (list n s)).map tapeBit := rfl

lemma compilation_sum_bound (x t y R C A : ℕ) (hx : x≤R)
    (ht : t≤C*R) (hy : y≤A*R) (hR : 1≤R) : x+t+y+3≤(C+A+4)*R := by
  linarith only [hx, ht, hy, hR]

lemma compilation_square_bound (D C A x E : ℕ) :
    D*((C+A+4)*x^E)^2 = D*(C+A+4)^2*x^(2*E) := by
  rw [Nat.mul_pow, ←pow_mul, Nat.mul_comm E 2, Nat.mul_assoc]

/-- The raw compiler preserves literal input/output and gives a fixed
finite alphabet and state space with a polynomial transition bound. -/

theorem implementation_of_stack (h : StackImplementation) : Implementation := by
  obtain ⟨r,p,ki,ko,C,k,hC,hk,hp⟩ := h
  obtain ⟨m,G,D,hD,hG⟩ := Compiler.raw_compilation p ki ko
  let A := PolynomialBounds.outputConstant
  let E := k+104
  refine ⟨m,G,D*(C+A+4)^2,2*E,by positivity,by dsimp [E]; omega,?_⟩
  intro n s hn hs
  obtain ⟨t,ht,he⟩ := hp n s hn hs
  have hw : unaryWord n s≠[] := by
    intro heq
    have hh := congrArg List.length heq
    simp [unaryWord] at hh
  obtain ⟨u,hu,a,ha,hhalt,hout⟩ := hG (unaryWord n s) (encoded n s) t hw he
  have hlen : (unaryWord n s).length=n+s+1 := by simp [unaryWord]; omega
  have hsize : (encoded n s).length≤A*(n+s+1)^104 := (exact_output n s hn hs).2.1
  have hm : 1≤n+s+1 := by omega
  have hmE : n+s+1≤(n+s+1)^E := by
    exact (le_refl (n+s+1)).trans (by
      have hh := Nat.pow_le_pow_right hm (by dsimp [E]; omega : 1≤E)
      simpa using hh)
  have ht' : t≤C*(n+s+1)^E := ht.trans (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right hm (by dsimp [E]; omega)))
  have ho' : (encoded n s).length≤A*(n+s+1)^E := hsize.trans (Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right hm (by dsimp [E]; omega)))
  have h1 : 1≤(n+s+1)^E := one_le_pow₀ hm
  have htotal : (unaryWord n s).length+t+(encoded n s).length+3 ≤
      (C+A+4)*(n+s+1)^E := by
    rw [hlen]
    exact compilation_sum_bound _ _ _ _ _ _ hmE ht' ho' h1
  refine ⟨u, hu.trans (le_trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left htotal 2))
    (le_of_eq (compilation_square_bound D C A (n+s+1) E))), a, ?_, hhalt, ?_⟩
  · rw [run_eq_exec,←unaryWord_raw]
    exact ha
  · rw [hout, encoded_raw]
    exact Turing.Tape.mk'_right₀ _ _

end RationalHitting.ExecutableGenerator

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Procedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting

namespace TimeBound

/-- These certificates imply an ordinary fixed positive-coefficient, positive-
degree power bound. This prevents any hidden superpolynomial time allowance. -/
theorem growth (p : TimeBound) :
    ∃ C k : ℕ, 0<C ∧ 0<k ∧ ∀ n : ℕ, 1≤n → p.eval n≤C*n^k := by
  induction p with
  | const c =>
    refine ⟨c+1,1,by omega,by omega,?_⟩
    intro n hn
    simp only [eval,pow_one]
    nlinarith only [hn]
  | «variable» => exact ⟨1,1,by omega,by omega,by intro n _; simp [eval]⟩
  | add p q hp hq =>
    obtain ⟨C,k,hC,hk,hp⟩ := hp
    obtain ⟨D,l,hD,hl,hq⟩ := hq
    refine ⟨C+D,k+l,by omega,by omega,?_⟩
    intro n hn
    have hp' := (hp n hn).trans (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_right hn (Nat.le_add_right k l)))
    have hq' := (hq n hn).trans (Nat.mul_le_mul_left D
      (Nat.pow_le_pow_right hn (Nat.le_add_left l k)))
    simpa only [eval,Nat.add_mul] using Nat.add_le_add hp' hq'
  | mul p q hp hq =>
    obtain ⟨C,k,hC,hk,hp⟩ := hp
    obtain ⟨D,l,hD,hl,hq⟩ := hq
    refine ⟨C*D,k+l,Nat.mul_pos hC hD,by omega,?_⟩
    intro n hn
    calc p.eval n*q.eval n ≤ (C*n^k)*(D*n^l) := Nat.mul_le_mul (hp n hn) (hq n hn)
         _ = (C*D)*n^(k+l) := by rw [pow_add]; ac_rfl

end TimeBound
end RationalHitting


/-! Compositional finite-stack implementation. All the constants introduced
here describe actual finite programs, not arithmetic-operation oracles. -/
namespace RationalHitting.StackLanguage
open Function

attribute [instance] Procedure.finite Procedure.decEq

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Feasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
namespace Feasible
variable {A B C D : Type} {ca : A → List Bool} {cb : B → List Bool}
  {cc : C → List Bool} {cd : D → List Bool} {f : A → B} {g : B → C}

theorem id (ca : A → List Bool) : Feasible ca ca _root_.id := ⟨Procedure.identity ca⟩
theorem const (ca : A → List Bool) (cb : B → List Bool) (b : B) :
    Feasible ca cb (fun _ => b) := ⟨Procedure.const ca cb b⟩
theorem comp (hg : Feasible cb cc g) (hf : Feasible ca cb f) : Feasible ca cc (g ∘ f) := by
  obtain ⟨p⟩ := hf; obtain ⟨q⟩ := hg; exact ⟨q.comp p⟩
theorem pair {f : A → B} {g : A → C} (hf : Feasible ca cb f) (hg : Feasible ca cc g) :
    Feasible ca (pairCode cb cc) (fun a => (f a,g a)) := by
  obtain ⟨p⟩ := hf; obtain ⟨q⟩ := hg; exact ⟨p.pair q⟩
theorem recode {A' B' : Type} (hf : Feasible ca cb f) (ca' : A' → List Bool)
    (cb' : B' → List Bool) (f' : A' → B') (e : A' → A)
    (hi : ∀ a,ca (e a)=ca' a) (ho : ∀ a,cb (f (e a))=cb' (f' a)) : Feasible ca' cb' f' := by
  obtain ⟨p⟩ := hf; exact ⟨p.recode ca' cb' f' e hi ho⟩
theorem of_eq {g : A → B} (hf : Feasible ca cb f) (h : ∀ a,f a=g a) : Feasible ca cb g := by
  have : f=g := funext h
  simpa only [this] using hf

theorem branch {f g : A → B} (hf : Feasible ca cb f) (hg : Feasible ca cb g) :
    Feasible (pairCode boolCode ca) cb (fun a => if a.1 then f a.2 else g a.2) := by
  obtain ⟨p⟩ := hf; obtain ⟨q⟩ := hg; exact ⟨p.branch q⟩
theorem cond {c : A → Bool} {f g : A → B} (hc : Feasible ca boolCode c)
    (hf : Feasible ca cb f) (hg : Feasible ca cb g) :
    Feasible ca cb (fun a => if c a then f a else g a) :=
  (hf.branch hg).comp (hc.pair (id ca))

theorem iterate {f : A → A} (hf : Feasible ca ca f) (Q : TimeBound)
    (hQ : ∀ (n : ℕ) (a : A) (i : ℕ), i≤n →
      (ca (f^[i] a)).length≤Q.eval ((pairCode unaryCode ca (n,a)).length+1)) :
    Feasible (pairCode unaryCode ca) ca (fun a => f^[a.1] a.2) := by
  obtain ⟨p⟩ := hf; exact ⟨p.iterate Q hQ⟩

theorem appendWord : Feasible (pairCode _root_.id _root_.id) _root_.id
    (fun a : List Bool×List Bool => a.1++a.2) := ⟨Procedure.appendWord⟩
theorem reverseWord : Feasible _root_.id _root_.id (List.reverse : List Bool → List Bool) :=
  ⟨Procedure.reverseWord⟩

end Feasible
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Feasible

theorem binaryAdd : Feasible (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1+a.2) :=
  ⟨Procedure.binaryAdd⟩
theorem binaryMul : Feasible (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1*a.2) :=
  ⟨Procedure.binaryMul⟩

theorem unaryAdd : Feasible (pairCode unaryCode unaryCode) unaryCode (fun a => a.1+a.2) := by
  exact appendWord.recode _ _ _ (fun a => (unaryCode a.1,unaryCode a.2))
    (by intro a; rfl) (by intro a; simp only [unaryCode,id_eq,List.replicate_append_replicate])

end Feasible
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Tabulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

namespace Feasible
variable {A B : Type} {ca : A → List Bool} {cb : B → List Bool}

theorem listCons (ca : A → List Bool) :
    Feasible (pairCode ca (listCode ca)) (listCode ca) (fun a => a.1::a.2) :=
  (id (pairCode ca (listCode ca))).recode _ _ _ _root_.id (by intro a; rfl) (by intro a; rfl)

theorem listSingleton (ca : A → List Bool) : Feasible ca (listCode ca) (fun a => [a]) :=
  (listCons ca).comp ((id ca).pair (const ca (listCode ca) []))

theorem listAppend (ca : A → List Bool) :
    Feasible (pairCode (listCode ca) (listCode ca)) (listCode ca) (fun a => a.1++a.2) :=
  appendWord.recode _ _ _ (fun a => (listCode ca a.1,listCode ca a.2))
    (by intro a; rfl) (by intro a; exact (listCode_append ca a.1 a.2).symm)

end Feasible
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Feasible

theorem unarySucc : Feasible unaryCode unaryCode Nat.succ := by
  exact (unaryAdd.comp ((id unaryCode).pair (const unaryCode unaryCode 1))).of_eq
    (by intro n; rfl)

end Feasible

lemma tableStep_iterate_fields {A B : Type} (f : A × ℕ → B) (a : A × (ℕ × List B)) (j : ℕ) :
    ((tableStep f)^[j] a).1 = a.1 ∧ ((tableStep f)^[j] a).2.1 = a.2.1+j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iterate_succ_apply']
    simp [tableStep,ih.1,ih.2,Nat.add_assoc]

lemma tableStep_iterate_size {A B : Type} {ca : A → List Bool} {cb : B → List Bool}
    {f : A × ℕ → B} (p : Procedure (pairCode ca unaryCode) cb f)
    (n : ℕ) (a : A × (ℕ × List B)) (j : ℕ) (hj : j≤n) :
    (tableStateCode ca cb ((tableStep f)^[j] a)).length ≤
      (TimeBound.variable*(2*p.bound+4)).eval
        ((pairCode unaryCode (tableStateCode ca cb) (n,a)).length+1) := by
  let N := (pairCode unaryCode (tableStateCode ca cb) (n,a)).length+1
  let P := p.bound.eval N
  have hN : N = 2*n+2*(ca a.1).length+2*a.2.1+(listCode cb a.2.2).length+4 := by
    dsimp [N]
    simp only [pairCode_length,unaryCode_length,tableStateCode_length]
    omega
  have hb : ∀ j≤n, (tableStateCode ca cb ((tableStep f)^[j] a)).length ≤
      (tableStateCode ca cb a).length+j*(2*P+3) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have ih := ih (by omega)
      have hh := tableStep_iterate_fields f a j
      have hf : (cb (f (((tableStep f)^[j] a).1,((tableStep f)^[j] a).2.1))).length≤P := by
        refine (p.size _).trans (p.bound.monotone ?_)
        simp only [pairCode_length,unaryCode_length,hh.1,hh.2]
        omega
      rw [iterate_succ_apply']
      simp only [tableStateCode_length,tableStep,listCode_append,
        listCode_singleton,List.length_append,codeWord_length] at *
      linarith only [ih,hf]
  have hb' := hb j hj
  have hbase : (tableStateCode ca cb a).length≤N := by
    rw [tableStateCode_length,hN]; omega
  have hjN : j≤N := by omega
  change _ ≤ N*(2*P+4)
  linarith only [hb',hbase,Nat.mul_le_mul_right (2*P+3) hjN]

lemma tableStep_iterate_start {A B : Type} (f : A × ℕ → B) (a : A) (n : ℕ) :
    (tableStep f)^[n] (a,0,[]) = (a,n,(List.range n).map (fun i => f (a,i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',ih]
    simp [tableStep,List.range_succ]

namespace Feasible
variable {A B : Type} {ca : A → List Bool} {cb : B → List Bool} {f : A × ℕ → B}

theorem tableStep (hf : Feasible (pairCode ca unaryCode) cb f) :
    Feasible (tableStateCode ca cb) (tableStateCode ca cb) (StackLanguage.tableStep f) := by
  have ha := fst ca (pairCode unaryCode (listCode cb))
  have hr := snd ca (pairCode unaryCode (listCode cb))
  have hi := (fst unaryCode (listCode cb)).comp hr
  have hl := (snd unaryCode (listCode cb)).comp hr
  have hv := hf.comp (ha.pair hi)
  exact (ha.pair ((unarySucc.comp hi).pair
    ((listAppend cb).comp (hl.pair ((listSingleton cb).comp hv))))).of_eq (by intro a; rfl)

/-- Polynomial-time tabulation of an arbitrary polynomial-time callback.
The construction uses only one finite stack program, including all indexing,
record layout, and loop control; the counter is unary. -/
theorem tabulate (hf : Feasible (pairCode ca unaryCode) cb f) :
    Feasible (pairCode unaryCode ca) (listCode cb)
      (fun a => (List.range a.1).map (fun i => f (a.2,i))) := by
  obtain ⟨p⟩ := hf
  have ht := tableStep (show Feasible (pairCode ca unaryCode) cb f from ⟨p⟩)
  have hi := ht.iterate (TimeBound.variable*(2*p.bound+4)) (tableStep_iterate_size p)
  have ha := snd unaryCode ca
  have hn := fst unaryCode ca
  have hinit := ha.pair ((const (pairCode unaryCode ca) unaryCode 0).pair
    (const (pairCode unaryCode ca) (listCode cb) []))
  have he := hi.comp (hn.pair hinit)
  have ho := ((snd unaryCode (listCode cb)).comp (snd ca (pairCode unaryCode (listCode cb)))).comp he
  exact ho.of_eq (by intro a; simp only [comp_apply,tableStep_iterate_start])

end Feasible
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

export Coding (code)

namespace Poly
open Function
variable {A B C D : Type} [Coding A] [Coding B] [Coding C] [Coding D]

@[fun_prop] theorem id : Poly (fun a : A => a) := Feasible.id code
@[fun_prop] theorem const (b : B) : Poly (fun _ : A => b) := Feasible.const code code b
@[fun_prop] theorem comp {f : A → B} {g : B → C} (hg : Poly g) (hf : Poly f) :
    Poly (fun a => g (f a)) := Feasible.comp hg hf
@[fun_prop] theorem pair {f : A → B} {g : A → C} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => (f a,g a)) := Feasible.pair hf hg
@[fun_prop] theorem subtypeVal (P : A → Prop) : Poly (Subtype.val : {a // P a} → A) :=
  (Feasible.id (code : A → List Bool)).recode _ _ _ Subtype.val (by intro a; rfl) (by intro a; rfl)

theorem subtypeMk {f : A → B} {P : B → Prop} (hf : Poly f) (h : ∀ a,P (f a)) :
    Poly (fun a => (⟨f a,h a⟩ : {b // P b})) :=
  hf.recode _ _ _ _root_.id (by intro a; rfl) (by intro a; rfl)

theorem of_eq {f g : A → B} (hf : Poly f) (h : ∀ a,f a=g a) : Poly g :=
  Feasible.of_eq hf h

@[fun_prop] theorem cond {c : A → Bool} {f g : A → B} (hc : Poly c)
    (hf : Poly f) (hg : Poly g) : Poly (fun a => if c a then f a else g a) :=
  Feasible.cond hc hf hg

@[fun_prop] theorem natAdd : Poly (fun a : ℕ×ℕ => a.1+a.2) := Feasible.binaryAdd
@[fun_prop] theorem natMul : Poly (fun a : ℕ×ℕ => a.1*a.2) := Feasible.binaryMul

@[fun_prop] theorem unarySucc : Poly (fun a : Unary => Unary.mk (a.val+1)) :=
  Feasible.unarySucc.recode _ _ _ Unary.val (by intro a; rfl) (by intro a; rfl)
@[fun_prop] theorem unaryAdd : Poly (fun a : Unary×Unary => Unary.mk (a.1.val+a.2.val)) :=
  Feasible.unaryAdd.recode _ _ _ (fun a => (a.1.val,a.2.val)) (by intro a; rfl) (by intro a; rfl)

@[fun_prop] theorem listCons : Poly (fun a : A×List A => a.1::a.2) := Feasible.listCons code
@[fun_prop] theorem listSingleton : Poly (fun a : A => [a]) := Feasible.listSingleton code
@[fun_prop] theorem listAppend : Poly (fun a : List A×List A => a.1++a.2) := Feasible.listAppend code
@[fun_prop] theorem wordAppend : Poly (fun a : BitWord×BitWord => BitWord.mk (a.1.val++a.2.val)) :=
  Feasible.appendWord.recode _ _ _ (fun a => (a.1.val,a.2.val)) (by intro a; rfl) (by intro a; rfl)

theorem tabulate {f : A×Unary → B} (hf : Poly f) :
    Poly (fun a : Unary×A => (List.range a.1.val).map (fun i => f (a.2,⟨i⟩))) := by
  have h := hf.recode (pairCode (code : A→List Bool) unaryCode) code
    (fun a : A×ℕ => f (a.1,⟨a.2⟩)) (fun a => (a.1,Unary.mk a.2))
    (by intro a; rfl) (by intro a; rfl)
  exact h.tabulate.recode _ _ _ (fun a => (a.1.val,a.2)) (by intro a; rfl) (by intro a; rfl)

end Poly
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.ListProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

namespace Feasible
variable {A : Type} (ca : A → List Bool)

theorem listUncons (z : A) : Feasible (listCode ca) (pairCode ca (listCode ca))
    (fun a => (a.headD z,a.tail)) := by
  refine (show Feasible _root_.id _root_.id _ from ⟨Procedure.padEmpty (codeWord (ca z))⟩).recode
    _ _ _ (listCode ca) (by intro a; rfl) ?_
  intro a
  cases a with
  | nil => simp [pairCode]
  | cons b a =>
    have hne : codeWord (ca b)++listCode ca a≠[] := by
      intro h
      have := congrArg List.length h
      simp at this
    simp [pairCode,hne]

theorem listTail (z : A) : Feasible (listCode ca) (listCode ca) List.tail :=
  (snd ca (listCode ca)).comp (listUncons ca z)

theorem listHeadD (z : A) : Feasible (listCode ca) ca (fun a => a.headD z) :=
  (fst ca (listCode ca)).comp (listUncons ca z)

end Feasible

lemma listCode_tail_le {A : Type} (ca : A → List Bool) (a : List A) :
    (listCode ca a.tail).length≤(listCode ca a).length := by
  cases a <;> simp

lemma listCode_iterate_tail_le {A : Type} (ca : A → List Bool) (a : List A) (n : ℕ) :
    (listCode ca (List.tail^[n] a)).length≤(listCode ca a).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    exact (listCode_tail_le ca _).trans ih

namespace Poly
variable {A : Type} [Coding A]

@[fun_prop] theorem listTail [Inhabited A] : Poly (List.tail : List A → List A) :=
  Feasible.listTail code default
@[fun_prop] theorem listHeadD (z : A) : Poly (fun a : List A => a.headD z) :=
  Feasible.listHeadD code z

theorem iterate {f : A → A} (hf : Poly f) (Q : TimeBound)
    (hQ : ∀ (n : ℕ) (a : A) (i : ℕ), i≤n →
      (code (f^[i] a)).length≤Q.eval ((pairCode unaryCode code (n,a)).length+1)) :
    Poly (fun a : Unary×A => f^[a.1.val] a.2) :=
  (Feasible.iterate hf Q hQ).recode _ _ _ (fun a => (a.1.val,a.2))
    (by intro a; rfl) (by intro a; rfl)

theorem listDrop [Inhabited A] : Poly (fun a : Unary×List A => a.2.drop a.1.val) := by
  have hh := (listTail (A:=A)).iterate TimeBound.variable (by
    intro n a i hi
    have h := listCode_iterate_tail_le (code : A → List Bool) a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    change (listCode code (List.tail^[i] a)).length≤_ at ⊢
    change _≤2*n+1+(listCode code a).length+1
    omega)
  refine hh.of_eq ?_
  intro a
  exact List.tail_iterate _ _

theorem listGetD [Inhabited A] (z : A) :
    Poly (fun a : Unary×List A => (a.2.drop a.1.val).headD z) :=
  (listHeadD z).comp listDrop

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Poly

@[fun_prop] theorem listLength {A : Type} [Coding A] : Poly (fun a : List A => Unary.mk a.length) :=
  (show Feasible (listCode code) unaryCode List.length from ⟨Procedure.listLength code⟩).recode
    _ _ _ _root_.id (by intro a; rfl) (by intro a; rfl)

end Poly
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.SignedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

namespace Poly

@[fun_prop] theorem natDifference : Poly (fun a : ℕ×ℕ => (a.1:ℤ)-(a.2:ℤ)) := by
  have h := Feasible.pair natLt natDifferenceAbs
  refine h.recode _ _ _ _root_.id (by intro a;rfl) ?_
  intro a
  change pairCode boolCode Nat.bits (decide (a.1<a.2),_) = intCode _
  have hsign : decide (a.1<a.2)=decide ((a.1:ℤ)-(a.2:ℤ)<0) := by
    simp only [sub_neg, Int.ofNat_lt]
  simp only [intCode,hsign, id_eq]

@[fun_prop] theorem intSign : Poly (fun a : ℤ => decide (a<0)) :=
  (Feasible.fst boolCode Nat.bits).recode _ _ _ (fun a : ℤ => (decide (a<0),a.natAbs))
    (by intro a;rfl) (by intro a;rfl)
@[fun_prop] theorem intAbs : Poly (Int.natAbs : ℤ → ℕ) :=
  (Feasible.snd boolCode Nat.bits).recode _ _ _ (fun a : ℤ => (decide (a<0),a.natAbs))
    (by intro a;rfl) (by intro a;rfl)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

lemma int_decompose (z : ℤ) : (positivePart z : ℤ)-(negativePart z : ℤ)=z := by
  by_cases h : z<0
  · simp [positivePart,negativePart,h,abs_of_neg h]
  · simp [positivePart,negativePart,h,abs_of_nonneg (by omega : 0≤z)]

namespace Poly

@[fun_prop] theorem positivePart_poly : Poly StackLanguage.positivePart := by
  unfold StackLanguage.positivePart
  fun_prop
@[fun_prop] theorem negativePart_poly : Poly StackLanguage.negativePart := by
  unfold StackLanguage.negativePart
  fun_prop

@[fun_prop] theorem natCastInt : Poly (fun a : ℕ => (a : ℤ)) := by
  have h := natDifference.comp (show Poly (fun a : ℕ => (a,0)) by fun_prop)
  exact h.of_eq (by intro a;simp)
@[fun_prop] theorem intNeg : Poly (fun a : ℤ => -a) := by
  have h := natDifference.comp (show Poly (fun a : ℤ => (negativePart a,positivePart a)) by fun_prop)
  exact h.of_eq (by intro a; have hh := int_decompose a;omega)
@[fun_prop] theorem intAdd : Poly (fun a : ℤ×ℤ => a.1+a.2) := by
  have h := natDifference.comp (show Poly (fun a : ℤ×ℤ =>
      (positivePart a.1+positivePart a.2,negativePart a.1+negativePart a.2)) by fun_prop)
  exact h.of_eq (by intro a;push_cast; have h1 := int_decompose a.1;have h2 := int_decompose a.2;omega)
@[fun_prop] theorem intMul : Poly (fun a : ℤ×ℤ => a.1*a.2) := by
  have h := natDifference.comp (show Poly (fun a : ℤ×ℤ =>
      (positivePart a.1*positivePart a.2+negativePart a.1*negativePart a.2,
      positivePart a.1*negativePart a.2+negativePart a.1*positivePart a.2)) by fun_prop)
  refine h.of_eq ?_
  intro a
  push_cast
  conv_rhs => rw [← int_decompose a.1,← int_decompose a.2]
  ring

@[fun_prop] theorem natZero : Poly (fun a : ℕ => decide (a=0)) := by
  refine (show Feasible _root_.id boolCode _ from ⟨Procedure.wordEmpty⟩).recode
    _ _ _ Nat.bits (by intro a;rfl) ?_
  intro a
  change boolCode a.bits.isEmpty = boolCode (decide (a=0))
  by_cases h : a=0
  · simp [h]
  · have hh : a.bits≠[] := by
      intro e
      have he := congrArg wordValue e
      simp only [wordValue_bits,wordValue] at he
      exact h he
    cases he : a.bits with
    | nil => exact (hh he).elim
    | cons b w => simp [show a≠0 from h]

@[fun_prop] theorem intZero : Poly (fun a : ℤ => decide (a=0)) := by
  have h := natZero.comp intAbs
  exact h.of_eq (by intro a;simp)

@[fun_prop] theorem boolNot : Poly Bool.not := by
  have h : Poly (fun a : Bool => if a then false else true) := by fun_prop
  exact h.of_eq (by intro a;cases a <;> rfl)
@[fun_prop] theorem boolAnd : Poly (fun a : Bool×Bool => a.1 && a.2) := by
  have h : Poly (fun a : Bool×Bool => if a.1 then a.2 else false) := by fun_prop
  exact h.of_eq (by intro a;cases a.1 <;> rfl)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma succ_iterate (a n : ℕ) : Nat.succ^[n] a=a+n := by
  induction n with
  | zero => simp
  | succ n ih => simp [iterate_succ_apply',ih,Nat.add_assoc]

lemma bits_length_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))

namespace Poly
@[fun_prop] theorem unaryToNat : Poly (Unary.val : Unary → ℕ) := by
  have hs : Poly Nat.succ := by
    exact (natAdd.comp (show Poly (fun a : ℕ => (a,1)) by fun_prop)).of_eq (by intro a;rfl)
  have hh := hs.iterate (2*TimeBound.variable) (by
    intro n a i hi
    simp only [succ_iterate,nat_code_length,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_variable,pairCode_length,unaryCode_length]
    have h := add_bits_length a i
    have h' := bits_length_le i
    omega)
  have ht := hh.comp (show Poly (fun a : Unary => (a,(0:ℕ))) by fun_prop)
  exact ht.of_eq (by intro a;simp [succ_iterate])

@[fun_prop] theorem unaryPred : Poly (fun a : Unary => Unary.mk (a.val-1)) :=
  (show Feasible unaryCode unaryCode Nat.pred from ⟨Procedure.unaryPred⟩).recode
    _ _ _ Unary.val (by intro a;rfl) (by intro a;rfl)

@[fun_prop] theorem unaryZero : Poly (fun a : Unary => decide (a.val=0)) := by
  exact natZero.comp unaryToNat

@[fun_prop] theorem unaryLt : Poly (fun a : Unary×Unary => decide (a.1.val<a.2.val)) := by
  exact natLt.comp (show Poly (fun a : Unary×Unary => (a.1.val,a.2.val)) by fun_prop)

@[fun_prop] theorem unaryLe : Poly (fun a : Unary×Unary => decide (a.1.val≤a.2.val)) := by
  have hh := boolNot.comp (unaryLt.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop))
  exact hh.of_eq (by
    intro a
    by_cases h : a.1.val≤a.2.val
    · simp [h,show ¬a.2.val<a.1.val by omega]
    · simp [h,show a.2.val<a.1.val by omega])

@[fun_prop] theorem unaryEq : Poly (fun a : Unary×Unary => decide (a.1.val=a.2.val)) := by
  have hh := boolAnd.comp (unaryLe.pair
    (unaryLe.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop)))
  exact hh.of_eq (by intro a;by_cases h : a.1.val=a.2.val <;> simp_all;omega)

lemma unaryPred_iterate (a : Unary) (n : ℕ) :
    (fun a : Unary => Unary.mk (a.val-1))^[n] a=Unary.mk (a.val-n) := by
  induction n with
  | zero => cases a;rfl
  | succ n ih => simp [iterate_succ_apply',ih,Nat.sub_sub ]

@[fun_prop] theorem unarySub : Poly (fun a : Unary×Unary => Unary.mk (a.1.val-a.2.val)) := by
  have hh := unaryPred.iterate TimeBound.variable (by
    intro n a i hi
    simp only [unaryPred_iterate,unary_code_length,TimeBound.eval_variable,pairCode_length,
      unaryCode_length]
    omega)
  have ht := hh.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop)
  exact ht.of_eq (by intro a;exact unaryPred_iterate _ _)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma int_add_bits_le (a b : ℤ) : (a+b).natAbs.bits.length≤a.natAbs.bits.length+b.natAbs.bits.length :=
  (nat_bits_mono (Int.natAbs_add_le a b)).trans (add_bits_length a.natAbs b.natAbs)

lemma int_mul_bits_le (a b : ℤ) : (a*b).natAbs.bits.length≤a.natAbs.bits.length+b.natAbs.bits.length := by
  simpa only [Int.natAbs_mul, wordValue_bits] using product_bits_length a.natAbs.bits b.natAbs.bits

lemma powerStep_iterate (a : ℤ×ℤ) (n : ℕ) :
    (fun a : ℤ×ℤ => (a.1,a.2*a.1))^[n] a=(a.1,a.2*a.1^n) := by
  induction n with
  | zero => simp
  | succ n ih => simp [iterate_succ_apply',ih,pow_succ,mul_assoc]

lemma int_pow_bits_le (a : ℤ) (n : ℕ) : (a^n).natAbs.bits.length≤1+n*a.natAbs.bits.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hh := int_mul_bits_le (a^n) a
    linarith only [ih,hh]

namespace Poly

@[fun_prop] theorem intPow : Poly (fun a : ℤ×Unary => a.1^a.2.val) := by
  have hs : Poly (fun a : ℤ×ℤ => (a.1,a.2*a.1)) := by fun_prop
  have ht := hs.iterate (10*(TimeBound.variable+1)^2) (by
    intro n a i hi
    simp only [powerStep_iterate,prod_code_length,int_code_length,TimeBound.eval_mul,
      TimeBound.eval_numeral,TimeBound.eval_pow,TimeBound.eval_add,TimeBound.eval_variable,
      pairCode_length,unaryCode_length]
    have hh := int_mul_bits_le a.2 (a.1^i)
    have hp := int_pow_bits_le a.1 i
    have hin := Nat.mul_le_mul_right a.1.natAbs.bits.length hi
    nlinarith only [hh,hp,hin,Nat.zero_le (a.1.natAbs.bits.length^2),
      Nat.zero_le (a.2.natAbs.bits.length^2),Nat.zero_le (n^2)])
  have hm := (show Poly (Prod.snd : ℤ×ℤ → ℤ) from snd).comp
    (ht.comp (show Poly (fun a : ℤ×Unary => (a.2,(a.1,(1:ℤ)))) by fun_prop))
  exact hm.of_eq (by intro a;simp [powerStep_iterate])

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma sumStep_code_le (a : List ℤ×ℤ) : (code (sumStep a)).length≤(code a).length := by
  rcases a with ⟨l,z⟩
  cases l with
  | nil => simp [sumStep]
  | cons x l =>
    have hh := int_add_bits_le z x
    simp only [sumStep,List.tail_cons,List.headD_cons,prod_code_length,int_code_length]
    change 2*(listCode code l).length+1+(z+x).natAbs.bits.length+3≤
      2*(listCode code (x::l)).length+1+z.natAbs.bits.length+3
    simp only [listCode_cons,List.length_append,codeWord_length,int_code_length]
    omega

lemma sumStep_code_iterate_le (a : List ℤ×ℤ) (n : ℕ) :
    (code (sumStep^[n] a)).length≤(code a).length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply']; exact (sumStep_code_le _).trans ih

lemma sumStep_iterate_length (l : List ℤ) (z : ℤ) :
    sumStep^[l.length] (l,z)=([],z+l.sum) := by
  induction l generalizing z with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons,iterate_succ_apply]
    simp only [sumStep,List.tail_cons,List.headD_cons,ih,List.sum_cons]
    simp [add_assoc]

namespace Poly
@[fun_prop] theorem listSum : Poly (List.sum : List ℤ → ℤ) := by
  have hs : Poly sumStep := by unfold sumStep; fun_prop
  have ht := hs.iterate TimeBound.variable (by
    intro n a i hi
    have hh := sumStep_code_iterate_le a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have hm := (show Poly (Prod.snd : List ℤ×ℤ → ℤ) from snd).comp
    (ht.comp (show Poly (fun a : List ℤ => (Unary.mk a.length,(a,(0:ℤ)))) by fun_prop))
  exact hm.of_eq (by intro a;simp [sumStep_iterate_length])

end Poly
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.DenseDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

lemma code_le_of_mem {A : Type} [Coding A] {a : A} {l : List A} (h : a∈l) :
    (code a).length≤(code l).length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.mem_cons] at h
    simp only [list_code_cons]
    rcases h with rfl|h
    · omega
    · have hh:=ih h;omega

lemma list_code_length_le {A : Type} [Coding A] (l : List A) (B : ℕ)
    (h : ∀ a∈l,(code a).length≤B) : (code l).length≤l.length*(2*B+1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (by intro b hb;exact h b (by simp [hb]))
    simp only [list_code_cons,List.length_cons]
    linarith only [ha,hl]

lemma drop_headD_getElem {A : Type} (l : List A) (z : A) (i : ℕ) (hi : i<l.length) :
    (l.drop i).headD z=l[i] := by
  rw [List.headD_eq_getD,List.getD_eq_getElem]
  · exact List.getElem_drop
  · simp;omega

lemma finRows_access {A : Type} (z : A) {n : ℕ} (f : Fin n → A) (i : Fin n) :
    (((List.finRange n).map f).drop i.val).headD z=f i := by
  rw [drop_headD_getElem _ _ i.val (by simp)]
  simp

lemma finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

lemma range_map_to_finRange {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f=(List.finRange n).map (fun i=>f i.val) := by
  rw [←finRange_map_val,List.map_map]
  rfl

lemma DenseSquare.rows_get (a : DenseSquare) (i j : ℕ) :
    (((a.rows.drop i).headD []).drop j).headD 0=a.get i j := by
  unfold DenseSquare.get
  by_cases hi : i<a.dim
  · rw [dite_eq_left hi]
    have he := finRows_access ([] : List ℤ) (fun i : Fin a.dim =>
      (List.finRange a.dim).map (fun j => a.val i j)) ⟨i,hi⟩
    change (List.drop j ((List.drop i a.rows).headD [])).headD 0 = _
    change (a.rows.drop i).headD [] = (List.finRange a.dim).map (fun j => a.val ⟨i,hi⟩ j) at he
    rw [he]
    by_cases hj : j<a.dim
    · rw [dite_eq_left hj]
      exact finRows_access 0 _ ⟨j,hj⟩
    · rw [dite_eq_right hj,List.drop_eq_nil_iff.mpr (by simpa using Nat.le_of_not_lt hj)]
      rfl
  · rw [dite_eq_right hi]
    have he : a.rows.drop i=[] := List.drop_eq_nil_iff.mpr (by simpa [rows] using Nat.le_of_not_lt hi)
    rw [he];simp

lemma DenseSquare.dim_le_code (a : DenseSquare) : a.dim≤(code a).length := by
  change a.dim≤(code (Unary.mk a.dim,a.rows)).length
  simp only [prod_code_length,unary_code_length];omega

lemma DenseSquare.entry_bits_le_code (a : DenseSquare) (i j : Fin a.dim) :
    (a.val i j).natAbs.bits.length≤(code a).length := by
  have hi : ((List.finRange a.dim).map (fun j => a.val i j))∈a.rows := by
    exact List.mem_map.mpr ⟨i,by simp,rfl⟩
  have hj : a.val i j∈((List.finRange a.dim).map (fun j => a.val i j)) := by simp
  have h := (code_le_of_mem hj).trans (code_le_of_mem hi)
  change _≤(code (Unary.mk a.dim,a.rows)).length
  simp only [int_code_length] at h
  simp only [prod_code_length,unary_code_length]
  omega

lemma DenseSquare.get_bits_le_code (a : DenseSquare) (i j : ℕ) :
    (a.get i j).natAbs.bits.length≤(code a).length := by
  unfold DenseSquare.get
  split_ifs with hi hj
  · exact a.entry_bits_le_code ⟨i,hi⟩ ⟨j,hj⟩
  all_goals simp

lemma DenseSquare.code_length_le (a : DenseSquare) (b : ℕ)
    (h : ∀ i j,(a.val i j).natAbs.bits.length≤b) :
    (code a).length≤4*a.dim^2*b+14*a.dim^2+3*a.dim+1 := by
  have hr : ∀ l∈a.rows,(code l).length≤a.dim*(2*b+7) := by
    intro l hl
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
    have hh := list_code_length_le ((List.finRange a.dim).map (fun j => a.val i j)) (b+3)
      (by intro x hx;obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx;simp only [int_code_length];have := h i j;omega)
    convert hh using 1 ; simp only [List.length_map,List.length_finRange] ; ring
  have hl := list_code_length_le a.rows (a.dim*(2*b+7)) hr
  have hlen : a.rows.length=a.dim := by simp [rows]
  rw [hlen] at hl
  change (code (Unary.mk a.dim,a.rows)).length≤_
  simp only [prod_code_length,unary_code_length]
  linarith only [hl]

namespace Poly
@[fun_prop] theorem denseDim : Poly (fun a : DenseSquare => Unary.mk a.dim) :=
  (Feasible.fst (code : Unary→List Bool) (code : List (List ℤ)→List Bool)).recode
    _ _ _ (fun a => (Unary.mk a.dim,a.rows)) (by intro a;rfl) (by intro a;rfl)
@[fun_prop] theorem denseRows : Poly DenseSquare.rows :=
  (Feasible.snd (code : Unary→List Bool) (code : List (List ℤ)→List Bool)).recode
    _ _ _ (fun a => (Unary.mk a.dim,a.rows)) (by intro a;rfl) (by intro a;rfl)

@[fun_prop] theorem denseGet : Poly (fun a : DenseSquare×(Unary×Unary) => a.1.get a.2.1.val a.2.2.val) := by
  have hr := (listGetD ([] : List ℤ)).comp
    (show Poly (fun a : DenseSquare×(Unary×Unary) => (a.2.1,a.1.rows)) by fun_prop)
  have hh := (listGetD (0 : ℤ)).comp
    ((show Poly (fun a : DenseSquare×(Unary×Unary) => a.2.2) by fun_prop).pair hr)
  exact hh.of_eq (fun a => a.1.rows_get _ _)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Poly
variable {A : Type} [Coding A]

theorem denseBuild {n : A → Unary} {f : A×(Unary×Unary) → ℤ}
    (hn : Poly n) (hf : Poly f) :
    Poly (fun a : A => (⟨(n a).val,fun i j => f (a,(⟨i.val⟩,⟨j.val⟩))⟩ : DenseSquare)) := by
  have hc : Poly (fun a : (A×Unary)×Unary => f (a.1.1,(a.1.2,a.2))) :=
    hf.comp (by fun_prop)
  have hr := hc.tabulate.comp
    ((hn.comp (show Poly (Prod.fst : A×Unary → A) from fst)).pair
      (show Poly (fun a : A×Unary => a) from id))
  have hm := hr.tabulate.comp (hn.pair (show Poly (fun a : A => a) from id))
  have hh := hn.pair hm
  refine hh.recode _ _ _ _root_.id (by intro a;rfl) ?_
  intro a
  change code (n a,(List.range (n a).val).map (fun i =>
      (List.range (n a).val).map (fun j => f (a,(⟨i⟩,⟨j⟩))))) =
    code ((n a), (List.finRange (n a).val).map (fun i =>
      (List.finRange (n a).val).map (fun j => f (a,(⟨i.val⟩,⟨j.val⟩)))))
  simp only [range_map_to_finRange]

theorem sumRange {f : A×Unary → ℤ} (hf : Poly f) :
    Poly (fun a : Unary×A => ((List.range a.1.val).map (fun i => f (a.2,⟨i⟩))).sum) :=
  listSum.comp hf.tabulate

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function
open scoped BigOperators

lemma sum_diag_range (A : DenseSquare) (F : DenseSquare) (i : Fin A.dim) :
    ((List.range A.dim).map (fun k => if i.val<k then F.get k k else 0)).sum =
      ∑ k ∈ Finset.Ioi i, F.get k.val k.val := by
  rw [range_map_to_finRange,←List.ofFn_eq_map,List.sum_ofFn]
  simp [←Finset.sum_filter,Finset.filter_lt_eq_Ioi]

lemma sum_product_range (A : DenseSquare) (F : DenseSquare) (i j : Fin A.dim) :
    ((List.range A.dim).map (fun k => if i.val<k then F.get i.val k*A.get k j.val else 0)).sum =
      ∑ k ∈ Finset.Ioi i, F.get i.val k.val*A.val k j := by
  rw [range_map_to_finRange,←List.ofFn_eq_map,List.sum_ofFn]
  simp [←Finset.sum_filter,Finset.filter_lt_eq_Ioi]

namespace Poly

@[fun_prop] theorem denseStep : Poly (fun a : DenseSquare×DenseSquare => a.1.step a.2) := by
  have hd : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      if a.1.2.1.val<a.2.val then a.1.1.2.get a.2.val a.2.val else (0:ℤ)) := by
    have ht := unaryLt.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.2.1,a.2)) by fun_prop)
    have hg := denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.1.2,(a.2,a.2))) by fun_prop)
    exact (ht.cond hg (const 0)).of_eq (by intro a;simp)
  have hp : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      if a.1.2.1.val<a.2.val then a.1.1.2.get a.1.2.1.val a.2.val *
        a.1.1.1.get a.2.val a.1.2.2.val else (0:ℤ)) := by
    have ht := unaryLt.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.2.1,a.2)) by fun_prop)
    have hg1 := denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.1.2,(a.1.2.1,a.2))) by fun_prop)
    have hg2 := denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.1.1,(a.2,a.1.2.2))) by fun_prop)
    exact (ht.cond (intMul.comp (hg1.pair hg2)) (const 0)).of_eq (by intro a;simp)
  have hn := denseDim.comp (show Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) => a.1.1) by fun_prop)
  have hs1 := hd.sumRange.comp (hn.pair (show Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) => a) from id))
  have hs2 := hp.sumRange.comp (hn.pair (show Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) => a) from id))
  have hget := denseGet.comp (show Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) => (a.1.1,a.2)) by fun_prop)
  have he := intAdd.comp ((intMul.comp ((intNeg.comp hs1).pair hget)).pair hs2)
  have hh := denseBuild (denseDim.comp (show Poly (Prod.fst : DenseSquare×DenseSquare → DenseSquare) from fst)) he
  refine hh.of_eq ?_
  intro a
  congr 1
  funext i j
  simp only [sum_diag_range,sum_product_range,DenseSquare.get_fin]
  rfl

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma abs_le_pow_of_bits_le (z : ℤ) (b : ℕ) (h : z.natAbs.bits.length≤b) :
    |z|≤(2:ℤ)^b := by
  rw [Nat.size_eq_bits_len] at h
  have hh := (Nat.size_le.mp h).le
  rw [←Int.natCast_natAbs]
  exact_mod_cast hh

lemma bits_le_of_abs_le_pow (z : ℤ) (b : ℕ) (h : |z|≤(2:ℤ)^b) :
    z.natAbs.bits.length≤b+1 := by
  rw [←Int.natCast_natAbs] at h
  have hn : z.natAbs≤2^b := by exact_mod_cast h
  calc _ ≤ (2^b).bits.length := nat_bits_mono hn
       _ = b+1 := by rw [Nat.size_eq_bits_len,Nat.size_pow]

lemma DenseSquare.step_get_bound (A F : DenseSquare) (B C : ℕ)
    (hA : ∀ i j,|A.get i j|≤B) (hF : ∀ i j,|F.get i j|≤C) (i j : ℕ) :
    |(A.step F).get i j|≤(2*A.dim*B*C:ℕ) := by
  have he : ∀ u v : Fin A.dim, |A.val u v|≤(B:ℤ) := by
    intro u v
    have hh := hA u.val v.val
    rw [DenseSquare.get_fin] at hh
    exact hh
  have hh := DeterminantAlgorithm.step_bound A.val (fun u v => F.get u.val v.val) B C he
    (fun u v => hF u.val v.val)
  change |(if hi : i<A.dim then if hj : j<A.dim then
    BirdDet.Spec.stepEntry A.val (fun u v => F.get u.val v.val) ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0)|≤_
  split_ifs with hi hj
  · exact hh ⟨i,hi⟩ ⟨j,hj⟩
  all_goals simp only [abs_zero]; positivity

lemma DenseSquare.iterate_get_bound (A F : DenseSquare) (b : ℕ)
    (hA : ∀ i j,|A.get i j|≤(2:ℤ)^b) (hF : ∀ i j,|F.get i j|≤(2:ℤ)^b)
    (k i j : ℕ) : |((A.step)^[k] F).get i j|≤(2:ℤ)^(b+k*(1+A.dim+b)) := by
  induction k generalizing i j with
  | zero => simpa using hF i j
  | succ k ih =>
    rw [iterate_succ_apply']
    have hf : 2*A.dim*2^b≤2^(1+A.dim+b) := by
      calc _ ≤2*2^A.dim*2^b := Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (DeterminantAlgorithm.self_le_two_pow A.dim))
           _ = _ := by rw [pow_add,pow_add];norm_num
    have ht := A.step_get_bound ((A.step)^[k] F) (2^b) (2^(b+k*(1+A.dim+b)))
      (by simpa using hA) (by intro u v;simpa using ih u v) i j
    calc _ ≤ ((2*A.dim*2^b*2^(b+k*(1+A.dim+b)):ℕ):ℤ) := ht
         _ ≤ ((2^(1+A.dim+b)*2^(b+k*(1+A.dim+b)):ℕ):ℤ) := by
           exact_mod_cast Nat.mul_le_mul_right (2^(b+k*(1+A.dim+b))) hf
         _ = _ := by push_cast;rw [←pow_add];congr 1;ring

lemma DenseSquare.iterate_dim (A F : DenseSquare) (k : ℕ) :
    ((A.step)^[k+1] F).dim=A.dim := by rw [iterate_succ_apply'];rfl

lemma DenseSquare.iterate_code_bound (A F : DenseSquare) (b k : ℕ)
    (hA : (code A).length≤b) (hF : (code F).length≤b) :
    (code ((A.step)^[k+1] F)).length≤
      4*A.dim^2*(b+(k+1)*(1+A.dim+b)+1)+14*A.dim^2+3*A.dim+1 := by
  have hg := DenseSquare.iterate_get_bound A F b
    (fun i j => abs_le_pow_of_bits_le _ _ ((A.get_bits_le_code i j).trans hA))
    (fun i j => abs_le_pow_of_bits_le _ _ ((F.get_bits_le_code i j).trans hF)) (k+1)
  have hh := DenseSquare.code_length_le ((A.step)^[k+1] F) (b+(k+1)*(1+A.dim+b)+1)
    (by
      intro i j
      apply bits_le_of_abs_le_pow
      rw [←DenseSquare.get_fin ((A.step)^[k+1] F) i j]
      exact hg i.val j.val)
  simpa only [DenseSquare.iterate_dim] using hh

lemma birdState_iterate (a : DenseSquare×DenseSquare) (k : ℕ) :
    birdState^[k] a=(a.1,(a.1.step)^[k] a.2) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ_apply',ih,birdState]

lemma birdState_iterate_size (n : ℕ) (a : DenseSquare×DenseSquare) (i : ℕ) (hi : i≤n) :
    (code (birdState^[i] a)).length≤
      (64*(TimeBound.variable+1)^4).eval ((pairCode unaryCode code (n,a)).length+1) := by
  let L := (pairCode unaryCode code (n,a)).length+1
  have hL : L=2*n+2+2*(code a.1).length+1+(code a.2).length := by
    simp [L,pairCode_length,unaryCode_length,prod_code_length];omega
  have hA : (code a.1).length≤L := by omega
  have hF : (code a.2).length≤L := by omega
  have hn : n≤L := by omega
  have hd : a.1.dim≤L := a.1.dim_le_code.trans hA
  simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,TimeBound.eval_add,
    TimeBound.eval_variable]
  change _≤64*(L+1)^4
  rw [birdState_iterate,prod_code_length]
  cases i with
  | zero => simp;linarith only [hA,hF,Nat.zero_le (L^2),Nat.zero_le (L^3),Nat.zero_le (L^4)]
  | succ k =>
    have hh := a.1.iterate_code_bound a.2 L k hA hF
    have hek : L+(k+1)*(1+a.1.dim+L)+1≤2*(L+1)^2 := by
      have hk : k+1≤L := hi.trans hn
      have hm := Nat.mul_le_mul hk (show 1+a.1.dim+L≤1+L+L by omega)
      linarith only [hm]
    have hm := Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) hek
    have h2 := Nat.pow_le_pow_left hd 2
    linarith only [hh,hm,h2,hd,hA,Nat.zero_le (L^2),Nat.zero_le (L^3),Nat.zero_le (L^4)]

namespace Poly
@[fun_prop] theorem birdState_poly : Poly birdState :=
  (show Poly (Prod.fst : DenseSquare×DenseSquare → DenseSquare) from fst).pair denseStep

@[fun_prop] theorem birdStages : Poly (fun a : Unary×DenseSquare => (a.2.step)^[a.1.val] a.2) := by
  have hh := birdState_poly.iterate (64*(TimeBound.variable+1)^4) birdState_iterate_size
  have hs := (show Poly (Prod.snd : DenseSquare×DenseSquare → DenseSquare) from snd).comp
    (hh.comp (show Poly (fun a : Unary×DenseSquare => (a.1,(a.2,a.2))) by fun_prop))
  exact hs.of_eq (by intro a;simp [birdState_iterate])
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma DenseSquare.iterate_of {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    ((DenseSquare.of A).step)^[k] (DenseSquare.of A)=
      DenseSquare.of ((BirdDet.Spec.stepEntry A)^[k] A) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply',ih,DenseSquare.step_of,iterate_succ_apply']

lemma DenseSquare.detAlgorithm_eq (A : DenseSquare) : A.detAlgorithm=A.val.det := by
  obtain ⟨n,A⟩:=A
  change (DenseSquare.of A).detAlgorithm=A.det
  rw [←DeterminantAlgorithm.spec_eq_det]
  cases n with
  | zero => simp [DenseSquare.detAlgorithm,DenseSquare.of,BirdDet.Spec.birdDetSpec_zero]
  | succ k =>
    rw [BirdDet.Spec.birdDetSpec_succ]
    unfold DenseSquare.detAlgorithm
    change (if k+1=0 then (1:ℤ) else (-1:ℤ)^((k+1)-1)*
      (((DenseSquare.of A).step)^[(k+1)-1] (DenseSquare.of A)).get 0 0)=_
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,DenseSquare.iterate_of]
    simp [DenseSquare.get,DenseSquare.of]

namespace Poly
@[fun_prop] theorem denseDet : Poly (fun A : DenseSquare => A.val.det) := by
  have hn := unaryPred.comp denseDim
  have hs := birdStages.comp (hn.pair (show Poly (fun A : DenseSquare => A) from id))
  have he := denseGet.comp (hs.pair (const ((⟨0⟩:Unary),(⟨0⟩:Unary))))
  have hsign := intPow.comp ((const (-1:ℤ)).pair hn)
  have hv := intMul.comp (hsign.pair he)
  have hz := unaryZero.comp denseDim
  exact (hz.cond (const (1:ℤ)) hv).of_eq (by
    intro A
    simpa only [decide_eq_true_eq,DenseSquare.detAlgorithm] using A.detAlgorithm_eq)
end Poly
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.UnaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

lemma unaryMulStep_iterate (a : Unary×Unary) (n : ℕ) :
    (fun a : Unary×Unary => (a.1,Unary.mk (a.2.val+a.1.val)))^[n] a=
      (a.1,Unary.mk (a.2.val+n*a.1.val)) := by
  induction n with
  | zero => cases a; cases ‹Unary› ; simp
  | succ n ih => simp only [iterate_succ_apply',ih];congr 2;simp [Nat.succ_mul,Nat.add_assoc]

namespace Poly
@[fun_prop] theorem unaryMul : Poly (fun a : Unary×Unary => Unary.mk (a.1.val*a.2.val)) := by
  have hs : Poly (fun a : Unary×Unary => (a.1,Unary.mk (a.2.val+a.1.val))) :=
    (show Poly (Prod.fst : Unary×Unary → Unary) from fst).pair
      (unaryAdd.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop))
  have ht := hs.iterate (10*(TimeBound.variable+1)^2) (by
    intro n a i hi
    simp only [unaryMulStep_iterate,prod_code_length,unary_code_length,TimeBound.eval_mul,
      TimeBound.eval_numeral,TimeBound.eval_pow,TimeBound.eval_add,TimeBound.eval_variable,
      pairCode_length,unaryCode_length]
    have hin := Nat.mul_le_mul_right a.1.val hi
    nlinarith only [hin,Nat.zero_le (a.1.val^2),Nat.zero_le (a.2.val^2),Nat.zero_le (n^2)])
  have hm := (show Poly (Prod.snd : Unary×Unary → Unary) from snd).comp
    (ht.comp (show Poly (fun a : Unary×Unary => (a.2,(a.1,(⟨0⟩:Unary)))) by fun_prop))
  exact hm.of_eq (by intro a;simp [unaryMulStep_iterate,Nat.mul_comm])

theorem unaryPow (k : ℕ) : Poly (fun a : Unary => Unary.mk (a.val^k)) := by
  induction k with
  | zero => simpa using (const (A:=Unary) (Unary.mk 1))
  | succ k ih =>
    exact (unaryMul.comp (ih.pair (show Poly (fun a : Unary => a) from id))).of_eq
      (by intro a;simp [pow_succ])

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma divStep_size (a : DivState) : (code (divStep a)).length≤(code a).length+3 := by
  unfold divStep
  split_ifs <;> simp only [prod_code_length,unary_code_length] <;> omega

lemma divStep_iterate_size (a : DivState) (n : ℕ) :
    (code (divStep^[n] a)).length≤(code a).length+3*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    have hh:=divStep_size (divStep^[n] a)
    omega

lemma divStep_expected (d n : ℕ) :
    divStep (⟨d⟩,(⟨n/d⟩,⟨n%d⟩))=(⟨d⟩,(⟨(n+1)/d⟩,⟨(n+1)%d⟩)) := by
  by_cases hd : d=0
  · subst d;simp [divStep]
  have hp : 0<d := by omega
  have hr := Nat.mod_lt n hp
  have he := Nat.div_add_mod n d
  by_cases h : d≤n%d+1
  · have hb : n%d+1=d := by omega
    have hn : n+1=d*(n/d+1) := by linarith only [he,hb]
    have hq : (n+1)/d=n/d+1 := Nat.div_eq_of_eq_mul_right hp hn
    have hm : (n+1)%d=0 := by rw [hn,Nat.mul_mod_right]
    simp [divStep,hp,hq,hm,hb]
  · have hb : n%d+1<d := by omega
    have hq : (n+1)/d=n/d := Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using (show d*(n/d)≤n+1 by omega)) (by linarith only [he,hb])
    have hm : (n+1)%d=n%d+1 := by
      have hh := Nat.div_add_mod (n+1) d
      rw [hq] at hh
      omega
    simp [divStep,h,hq,hm]

lemma divStep_iterate (d : Unary) (n : ℕ) :
    divStep^[n] (d,(⟨0⟩,⟨0⟩))=(d,(⟨n/d.val⟩,⟨n%d.val⟩)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply',ih]
    exact divStep_expected d.val n

namespace Poly
@[fun_prop] theorem divStep_poly : Poly divStep := by
  have hc : Poly (fun a : DivState => decide (0<a.1.val ∧ a.1.val≤a.2.2.val+1)) := by
    have hz := boolNot.comp (unaryZero.comp (show Poly (Prod.fst : DivState → Unary) from fst))
    have hle := unaryLe.comp ((show Poly (Prod.fst : DivState → Unary) from fst).pair
      (unarySucc.comp (show Poly (fun a : DivState => a.2.2) by fun_prop)))
    exact (boolAnd.comp (hz.pair hle)).of_eq (by intro a;simp [Nat.pos_iff_ne_zero])
  have hy : Poly (fun a : DivState => ((⟨a.2.1.val+1⟩:Unary),(⟨a.2.2.val+1-a.1.val⟩:Unary))) :=
    (unarySucc.comp (show Poly (fun a : DivState => a.2.1) by fun_prop)).pair
      (unarySub.comp ((unarySucc.comp (show Poly (fun a : DivState => a.2.2) by fun_prop)).pair
        (show Poly (Prod.fst : DivState → Unary) from fst)))
  have hn : Poly (fun a : DivState => (a.2.1,(⟨a.2.2.val+1⟩:Unary))) :=
    (show Poly (fun a : DivState => a.2.1) by fun_prop).pair
      (unarySucc.comp (show Poly (fun a : DivState => a.2.2) by fun_prop))
  exact ((show Poly (Prod.fst : DivState → Unary) from fst).pair (hc.cond hy hn)).of_eq
    (by intro a;simp [divStep])

@[fun_prop] theorem unaryDivMod : Poly (fun a : Unary×Unary => ((⟨a.1.val/a.2.val⟩:Unary),(⟨a.1.val%a.2.val⟩:Unary))) := by
  have hh := divStep_poly.iterate (4*TimeBound.variable) (by
    intro n a i hi
    have h:=divStep_iterate_size a i
    simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have ho := (show Poly (Prod.snd : DivState → Unary×Unary) from snd).comp
    (hh.comp (show Poly (fun a : Unary×Unary => (a.1,(a.2,((⟨0⟩:Unary),(⟨0⟩:Unary))))) by fun_prop))
  exact ho.of_eq (by intro a;simp [divStep_iterate])

@[fun_prop] theorem unaryDiv : Poly (fun a : Unary×Unary => Unary.mk (a.1.val/a.2.val)) := fst.comp unaryDivMod
@[fun_prop] theorem unaryMod : Poly (fun a : Unary×Unary => Unary.mk (a.1.val%a.2.val)) := snd.comp unaryDivMod
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

namespace Poly
@[fun_prop] theorem bitLength : Poly (fun a : BitWord => Unary.mk a.val.length) :=
  (show Feasible _root_.id unaryCode List.length from ⟨Procedure.wordLength⟩).recode
    _ _ _ BitWord.val (by intro a;rfl) (by intro a;rfl)

@[fun_prop] theorem natBitLength : Poly (fun a : ℕ => Unary.mk a.bits.length) :=
  (show Feasible _root_.id unaryCode List.length from ⟨Procedure.wordLength⟩).recode
    _ _ _ Nat.bits (by intro a;rfl) (by intro a;rfl)

@[fun_prop] theorem natSize : Poly (fun a : ℕ => Unary.mk a.size) :=
  natBitLength.of_eq (fun a => congrArg Unary.mk (Nat.size_eq_bits_len a))
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma doubleBelow_iterate_bound (t v k : ℕ) : (doubleBelow t)^[k] v≤ max v (2*t) := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    rw [iterate_succ_apply']
    change (if (doubleBelow t)^[k] v≤t then (doubleBelow t)^[k] v+(doubleBelow t)^[k] v
      else (doubleBelow t)^[k] v)≤ max v (2*t)
    split_ifs with h
    · exact (show (doubleBelow t)^[k] v+(doubleBelow t)^[k] v≤2*t by omega).trans (le_max_right _ _)
    · exact ih

lemma doubleState_iterate (a : Unary×Unary) (k : ℕ) :
    doubleState^[k] a=(a.1,⟨(doubleBelow a.1.val)^[k] a.2.val⟩) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ_apply',ih,doubleState]

lemma doubleBelow_iterate_pow (t k : ℕ) (hk : k≤t.size) :
    (doubleBelow t)^[k] 1=2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply',ih (by omega)]
    have h : 2^k≤t := by
      by_contra hh
      have hs := Nat.size_le.mpr (show t<2^k by omega)
      omega
    simp [doubleBelow,h,pow_succ,Nat.mul_two]

lemma nat_size_log {t : ℕ} (ht : 0<t) : t.size=Nat.log 2 t+1 := by
  have hle := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1<2) t)
  have hpow := Nat.pow_log_le_self 2 ht.ne'
  have hlo : Nat.log 2 t<t.size := by
    by_contra hh
    have h := Nat.size_le.mp (show t.size≤Nat.log 2 t by omega)
    omega
  omega

namespace Poly
@[fun_prop] theorem doubleState_poly : Poly doubleState := by
  have hc := unaryLe.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop)
  have hs := unaryAdd.comp (show Poly (fun a : Unary×Unary => (a.2,a.2)) by fun_prop)
  exact ((show Poly (Prod.fst : Unary×Unary → Unary) from fst).pair
    (hc.cond hs (show Poly (Prod.snd : Unary×Unary → Unary) from snd))).of_eq
      (by intro a;simp [doubleState,doubleBelow];split_ifs <;> rfl)

@[fun_prop] theorem unaryNextPower : Poly (fun a : Unary => Unary.mk (2^a.val.size)) := by
  have hh := doubleState_poly.iterate (2*TimeBound.variable) (by
    intro n a i hi
    rw [doubleState_iterate]
    have hb := doubleBelow_iterate_bound a.1.val a.2.val i
    simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable,
      pairCode_length,unaryCode_length,prod_code_length,unary_code_length]
    omega)
  have hn := natSize.comp unaryToNat
  have hout := (show Poly (Prod.snd : Unary×Unary → Unary) from snd).comp
    (hh.comp (hn.pair (show Poly (fun a : Unary => (a,(⟨1⟩:Unary))) by fun_prop)))
  exact hout.of_eq (by intro a;simp [doubleState_iterate,doubleBelow_iterate_pow])

@[fun_prop] theorem unaryLogTwo : Poly (fun a : Unary => Unary.mk (Nat.log 2 a.val)) := by
  have hh := unaryPred.comp (natSize.comp unaryToNat)
  refine hh.of_eq ?_
  intro a
  by_cases h : a.val=0
  · simp [h]
  · simp [nat_size_log (show 0<a.val by omega)]

end Poly
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.RationalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

namespace Poly
@[fun_prop] theorem choose : Poly (fun a : Unary×Unary => a.1.val.choose a.2.val) :=
  (show Feasible (pairCode unaryCode unaryCode) Nat.bits (fun a : ℕ×ℕ => a.1.choose a.2) from
    ⟨Procedure.choose⟩).recode _ _ _ (fun a => (a.1.val,a.2.val))
      (by intro a;rfl) (by intro a;rfl)
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

variable {K : Type} [DecidableEq K]

namespace Poly
@[fun_prop] theorem rationalEncodeNZ : Poly (fun a : ℤ×NZInt => BitWord.mk (encodeRat (Rat.divInt a.1 a.2.val))) :=
  (show Feasible (pairCode intCode (fun b : NZInt => intCode b.val)) _root_.id
    (fun a : ℤ×NZInt => encodeRat (Rat.divInt a.1 a.2.val)) from
      ⟨Procedure.rationalEncode⟩).recode _ _ _ _root_.id (by intro a;rfl) (by intro a;rfl)

@[fun_prop] theorem safeDen : Poly (fun b : ℤ => (⟨if b=0 then 1 else b,by split_ifs with h <;> simp_all⟩ : NZInt)) := by
  have hh := intZero.cond (const (1:ℤ)) (show Poly (fun b : ℤ => b) from id)
  have hh' : Poly (fun b : ℤ => if b=0 then 1 else b) := hh.of_eq (by intro b;simp)
  exact hh'.subtypeMk _

@[fun_prop] theorem rationalEncode : Poly (fun a : ℤ×ℤ => BitWord.mk (encodeRat (Rat.divInt a.1 a.2))) := by
  have hz := intZero.comp (show Poly (Prod.snd : ℤ×ℤ → ℤ) from snd)
  have hn := rationalEncodeNZ.comp ((show Poly (Prod.fst : ℤ×ℤ → ℤ) from fst).pair
    (safeDen.comp (show Poly (Prod.snd : ℤ×ℤ → ℤ) from snd)))
  exact (hz.cond (const (BitWord.mk (encodeRat 0))) hn).of_eq (by
    intro a
    by_cases h : a.2=0
    · simp [h,Rat.divInt_eq_div]
    · simp [h])
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Poly
variable {A B : Type} [Coding A] [Coding B]

@[fun_prop] theorem unaryCastInt : Poly (fun a : Unary => (a.val : ℤ)) :=
  natCastInt.comp unaryToNat

 theorem ite {c : A → Prop} [DecidablePred c] {f g : A → B}
    (hc : Poly (fun a => decide (c a))) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => if c a then f a else g a) :=
  (hc.cond hf hg).of_eq (by intro a;simp)

 theorem sumUp {n : A → ℕ} {f : A×Unary → ℤ}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => ((List.range (n a)).map (fun i => f (a,⟨i⟩))).sum) :=
  hf.sumRange.comp (hn.pair (show Poly (fun a : A => a) from id))

end Poly

namespace Poly
@[fun_prop] theorem uAdd : Poly (fun a : Unary×Unary => a.1+a.2) := unaryAdd
@[fun_prop] theorem uSub : Poly (fun a : Unary×Unary => a.1-a.2) := unarySub
@[fun_prop] theorem uMul : Poly (fun a : Unary×Unary => a.1*a.2) := unaryMul
@[fun_prop] theorem uDiv : Poly (fun a : Unary×Unary => a.1/a.2) := unaryDiv
@[fun_prop] theorem uMod : Poly (fun a : Unary×Unary => a.1%a.2) := unaryMod
@[fun_prop] theorem uPow (k : ℕ) : Poly (fun a : Unary => a^k) := unaryPow k
@[fun_prop] theorem uInt : Poly Unary.toInt := unaryCastInt
@[fun_prop] theorem uChoose : Poly (fun a : Unary×Unary => Unary.choose a.1 a.2) :=
  natCastInt.comp choose
@[fun_prop] theorem uPowInt : Poly (fun a : ℤ×Unary => Unary.powInt a.1 a.2) := intPow
@[fun_prop] theorem uEq : Poly (fun a : Unary×Unary => Unary.eqb a.1 a.2) := unaryEq
@[fun_prop] theorem uLt : Poly (fun a : Unary×Unary => Unary.ltb a.1 a.2) := unaryLt

end Poly
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.TaylorComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open scoped BigOperators

lemma range_sum_fin {A : Type} [AddCommMonoid A] (n : ℕ) (f : ℕ → A) :
    ((List.range n).map f).sum=∑ i : Fin n, f i.val := by
  rw [range_map_to_finRange,←List.ofFn_eq_map,List.sum_ofFn]

lemma finEquiv_val {m : ℕ} [NeZero m] (i : Fin m) :
    ((ZMod.finEquiv m) i).val=i.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

lemma finEquiv_symm_val {m : ℕ} [NeZero m] (i : ZMod m) :
    ((ZMod.finEquiv m).symm i).val=i.val := by
  exact (finEquiv_val ((ZMod.finEquiv m).symm i)).symm.trans
    (congrArg ZMod.val ((ZMod.finEquiv m).apply_symm_apply i))

lemma zmod_val_sub {m : ℕ} [NeZero m] (a b : ZMod m) :
    (a-b).val=(a.val+(m-b.val)%m)%m := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val']

lemma coordinate_vals (e : ℕ) (i : Fin (Generator.D e)) :
    (((Generator.coordinate e).symm i).1.val,((Generator.coordinate e).symm i).2.val)=
      (i.val/CyclotomicRing.degree e,i.val % CyclotomicRing.degree e) := by
  change (((ZMod.finEquiv (CyclotomicRing.dimension e))
    (finProdFinEquiv.symm i).1).val,(finProdFinEquiv.symm i).2.val)=_
  rw [finEquiv_val]
  rfl
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open scoped BigOperators

namespace Runtime

lemma taylor_eq (m : ℕ) (a t : ℤ) (i j : Fin m) :
    taylor m a t i.val j.val=IntegralTest.full m a t i j := by
  unfold taylor IntegralTest.full
  rw [range_sum_fin]
  apply Finset.sum_congr rfl
  intro r _
  simp [taylorTerm,Fin.val_rev,Nat.sub_sub,Nat.add_comm]

lemma padded_eq (m N : ℕ) (a t : ℤ) (i j : Fin m) :
    padded m N a t i.val j.val=IntegralTest.padded m N a t i j := by
  simp [padded,IntegralTest.padded,taylor_eq]

@[fun_prop] theorem taylorTerm_poly : Poly (fun a : TaylorArgs×Unary =>
    taylorTerm a.1.1.val a.1.2.1 a.1.2.2.1 a.1.2.2.2.1.val a.1.2.2.2.2.val a.2.val) := by
  change Poly (fun a : TaylorArgs×Unary =>
    (Unary.powInt (-a.1.2.1) (a.1.1-1-a.2-a.1.2.2.2.1)*
      Unary.choose (a.1.1-1-a.2) a.1.2.2.2.1)*
    (Unary.powInt a.1.2.1 (a.1.2.2.2.2-a.2)*Unary.choose a.1.2.2.2.2 a.2)*
    Unary.powInt a.1.2.2.1 a.2)
  fun_prop

@[fun_prop] theorem taylor_poly : Poly (fun a : TaylorArgs =>
    taylor a.1.val a.2.1 a.2.2.1 a.2.2.2.1.val a.2.2.2.2.val) := by
  exact Poly.sumUp (show Poly (fun a : TaylorArgs => a.1) by fun_prop) taylorTerm_poly

@[fun_prop] theorem padded_poly : Poly (fun a : Unary×TaylorArgs =>
    padded a.2.1.val a.1.val a.2.2.1 a.2.2.2.1 a.2.2.2.2.1.val a.2.2.2.2.2.val) := by
  have hc : Poly (fun a : Unary×TaylorArgs => Unary.ltb a.2.2.2.2.2 a.1) := by fun_prop
  have hf : Poly (fun a : Unary×TaylorArgs =>
    taylor a.2.1.val a.2.2.1 a.2.2.2.1 a.2.2.2.2.1.val a.2.2.2.2.2.val) :=
    taylor_poly.comp (show Poly (Prod.snd : Unary×TaylorArgs → TaylorArgs) from Poly.snd)
  exact (hc.cond hf (Poly.const 0)).of_eq (by intro a;simp [padded,Unary.ltb])

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

namespace Poly
@[fun_prop] theorem paramB : Poly Params.BB := by
  change Poly (fun a : Unary => 2*a+1)
  fun_prop
@[fun_prop] theorem paramDelta : Poly Params.DD := by
  change Poly (fun a : Unary×Unary => 2*(a.1+1)^3*(2*a.2+1))
  fun_prop
@[fun_prop] theorem paramThreshold : Poly Params.threshold := by
  unfold Params.threshold
  fun_prop
@[fun_prop] theorem paramM : Poly Params.MM := by
  exact (unaryNextPower.comp paramThreshold).of_eq (by
    intro a
    change Unary.mk (2^(Parameters.B a.2.val*Parameters.delta a.1.val a.2.val).size)=_
    simp only [Params.MM,Parameters.M,Parameters.exponent,
      nat_size_log (Parameters.threshold_pos a.1.val a.2.val)])
@[fun_prop] theorem paramN : Poly Params.NN := by
  change Poly (fun a : Unary×Unary => Params.MM a-Params.DD a)
  fun_prop
@[fun_prop] theorem paramH : Poly Params.HH := by
  change Poly (fun a : Unary×Unary => 1+3*(a.2+2)*Params.BB a.2*(Params.MM a)^3)
  fun_prop
@[fun_prop] theorem paramDegree : Poly Params.QQ := by
  have hh : Poly (fun a : Unary×Unary => Params.MM a/2) := by fun_prop
  exact hh.of_eq (by
    intro a
    change Unary.mk (Parameters.M a.1.val a.2.val/2)=_
    simp [Params.QQ,Parameters.M,CyclotomicRing.degree,pow_succ])
@[fun_prop] theorem params : Poly (fun a : Unary×Unary => Params.of a.1.val a.2.val) := by
  change Poly (fun a : Unary×Unary => (a.1,Params.NN a,Params.MM a,Params.QQ a,Params.HH a))
  fun_prop
end Poly
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.LiftComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open scoped BigOperators
namespace Runtime

@[fun_prop] theorem signed_poly : Poly (fun a : (Unary×Unary)×(Unary×Unary) =>
    signed a.1.1.val a.1.2.val a.2.1.val a.2.2.val) := by
  have hc : Poly (fun a : (Unary×Unary)×(Unary×Unary) =>
    Unary.eqb ((a.1.2+a.2.2)%a.1.1) a.2.1) := by fun_prop
  have hf : Poly (fun a : (Unary×Unary)×(Unary×Unary) =>
    Unary.powInt (-1) ((a.1.2+a.2.2)/a.1.1)) := by fun_prop
  exact (hc.cond hf (Poly.const 0)).of_eq (by intro a;simp only [Unary.eqb,decide_eq_true_eq];rfl)

@[fun_prop] theorem liftTerm_poly : Poly (fun a : LiftTermArgs =>
    liftTerm a.1.1.1.1.1.val a.1.1.1.1.2.1.val a.1.1.1.1.2.2.val
      a.1.1.1.2.1.1 a.1.1.1.2.1.2.1 a.1.1.1.2.1.2.2.1 a.1.1.1.2.1.2.2.2
      a.1.1.1.2.2.1.val a.1.1.1.2.2.2.1.val a.1.1.1.2.2.2.2.1.val a.1.1.1.2.2.2.2.2.val
      a.1.1.2.val a.1.2.val a.2.val) := by
  let pars (a : LiftTermArgs) : Unary×TaylorArgs :=
    (a.1.1.1.1.2.1,a.1.1.1.1.1,a.1.1.1.2.1.1,a.1.1.1.2.1.2.1,a.2,
      (a.2+(a.1.1.1.1.1-a.1.2)%a.1.1.1.1.1)%a.1.1.1.1.1)
  have hpars : Poly pars := by unfold pars;fun_prop
  have ht := padded_poly.comp hpars
  let sp (a : LiftTermArgs) : (Unary×Unary)×(Unary×Unary) :=
    ((a.1.1.1.1.2.2,((a.1.1.1.1.1-(a.1.1.2*a.2)%a.1.1.1.1.1)%a.1.1.1.1.1+
      (a.1.1.2*a.1.1.1.2.2.1)%a.1.1.1.1.1)%a.1.1.1.1.1),
      (a.1.1.1.2.2.2.2.1,a.1.1.1.2.2.2.2.2))
  have hsp : Poly sp := by unfold sp;fun_prop
  have hs := signed_poly.comp hsp
  have hp : Poly (fun a : LiftTermArgs => Unary.powInt a.1.1.1.2.1.2.2.1 a.1.1.2) := by fun_prop
  have hr : Poly (fun a : LiftTermArgs => Unary.powInt a.1.1.1.2.1.2.2.2 a.1.2) := by fun_prop
  have hv := Poly.intMul.comp ((Poly.intMul.comp ((Poly.intMul.comp (ht.pair hs)).pair hp)).pair hr)
  have hc : Poly (fun a : LiftTermArgs =>
    Unary.eqb a.1.1.1.2.2.1 ((a.1.1.1.2.2.2.1+a.1.2)%a.1.1.1.1.1)) := by fun_prop
  exact (hc.cond hv (Poly.const 0)).of_eq (by intro a;simp only [Unary.eqb,decide_eq_true_eq];rfl)

@[fun_prop] theorem lift_poly : Poly (fun a : LiftArgs =>
    lift a.1.1.val a.1.2.1.val a.1.2.2.val
      a.2.1.1 a.2.1.2.1 a.2.1.2.2.1 a.2.1.2.2.2
      a.2.2.1.val a.2.2.2.1.val a.2.2.2.2.1.val a.2.2.2.2.2.val) := by
  have h1 := Poly.sumUp (show Poly (fun a : (LiftArgs×Unary)×Unary => a.1.1.1.1) by fun_prop) liftTerm_poly
  have h2 := Poly.sumUp (show Poly (fun a : LiftArgs×Unary => a.1.1.1) by fun_prop) h1
  exact Poly.sumUp (show Poly (fun a : LiftArgs => a.1.1) by fun_prop) h2

@[fun_prop] theorem entry_poly : Poly (fun a : EntryArgs =>
    entry a.1.1.val a.1.2.1.val a.1.2.2.val
      a.2.1.1 a.2.1.2.1 a.2.1.2.2.1 a.2.1.2.2.2 a.2.2.1.val a.2.2.2.val) := by
  exact lift_poly.comp (show Poly (fun a : EntryArgs =>
    (a.1,a.2.1,(a.2.2.1/a.1.2.2,a.2.2.2/a.1.2.2,a.2.2.1%a.1.2.2,a.2.2.2%a.1.2.2))) by fun_prop)

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open scoped BigOperators

lemma range_sum_zmod_val {A : Type} [AddCommMonoid A] (m : ℕ) [NeZero m] (f : ℕ → A) :
    ((List.range m).map f).sum=∑ z : ZMod m, f z.val := by
  rw [range_sum_fin]
  exact Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ (fun i => by
    change f i.val=f ((ZMod.finEquiv m) i).val
    rw [finEquiv_val])

namespace Runtime
lemma signed_eq (e : ℕ) (z : ZMod (CyclotomicRing.dimension e))
    (i j : Fin (CyclotomicRing.degree e)) :
    signed (CyclotomicRing.degree e) z.val i.val j.val = CyclotomicRing.signedEntry e z i j := rfl

lemma integerTest_apply (N e : ℕ) (a t : ℤ) (i j : ZMod (CyclotomicRing.dimension e)) :
    Generator.integerTest N e a t i j=
      padded (CyclotomicRing.dimension e) N a t i.val j.val := by
  change IntegralTest.padded _ _ _ _ ((ZMod.finEquiv _).symm i) ((ZMod.finEquiv _).symm j)=_
  rw [←padded_eq,finEquiv_symm_val,finEquiv_symm_val]

lemma liftTerm_eq (N e : ℕ) (a t p r : ℤ)
    (u v x y k : ZMod (CyclotomicRing.dimension e)) (i j : Fin (CyclotomicRing.degree e)) :
    liftTerm (CyclotomicRing.dimension e) N (CyclotomicRing.degree e) a t p r
      u.val v.val i.val j.val x.val y.val k.val =
      if u=v+y then Generator.integerTest N e a t k (k-y)*
        CyclotomicRing.signedEntry e (-x*k+x*u) i j*p^x.val*r^y.val else 0 := by
  have hz : (-x*k+x*u).val=
      (((CyclotomicRing.dimension e-(x.val*k.val)%CyclotomicRing.dimension e)%CyclotomicRing.dimension e+
        (x.val*u.val)%CyclotomicRing.dimension e)%CyclotomicRing.dimension e) := by
    rw [neg_mul,ZMod.val_add,ZMod.neg_val',ZMod.val_mul,ZMod.val_mul]
  unfold liftTerm
  simp only [←ZMod.val_add, (ZMod.val_injective _).eq_iff,←hz,←zmod_val_sub,signed_eq,←integerTest_apply]

lemma lift_eq (N e : ℕ) (a t p r : ℤ)
    (u v : ZMod (CyclotomicRing.dimension e)) (i j : Fin (CyclotomicRing.degree e)) :
    lift (CyclotomicRing.dimension e) N (CyclotomicRing.degree e) a t p r
      u.val v.val i.val j.val=
      IntegralLift.entry e (Generator.integerTest N e a t) p r u v i j := by
  unfold lift IntegralLift.entry
  rw [range_sum_zmod_val]
  apply Finset.sum_congr rfl
  intro x _
  rw [range_sum_zmod_val]
  apply Finset.sum_congr rfl
  intro y _
  rw [range_sum_zmod_val]
  apply Finset.sum_congr rfl
  intro k _
  exact liftTerm_eq N e a t p r u v x y k i j

lemma entry_eq (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) (i j : Fin (Generator.D e)) :
    entry (CyclotomicRing.dimension e) N (CyclotomicRing.degree e)
      a.val (x 0) (x 1) (x 2) i.val j.val = Generator.U n N e x a i j := by
  have hi := coordinate_vals e i
  have hj := coordinate_vals e j
  have hi1 := congrArg Prod.fst hi
  have hi2 := congrArg Prod.snd hi
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  simp only [] at hi1 hi2 hj1 hj2
  unfold entry Generator.U
  rw [←hi1,←hi2,←hj1,←hj2]
  exact lift_eq N e a.val (x 0) (x 1) (x 2) _ _ _ _

end Runtime
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.MatrixComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
variable {A : Type} [Coding A]

 lemma flattenStep_code_le (a : List (List A)×List A) :
    (code (flattenStep a)).length≤(code a).length := by
  rcases a with ⟨l,r⟩
  cases l with
  | nil => simp [flattenStep]
  | cons x l =>
    simp only [flattenStep,List.tail_cons,List.headD_cons,prod_code_length]
    change 2*(listCode code l).length+1+(listCode code (r++x)).length≤
      2*(listCode code (x::l)).length+1+(listCode code r).length
    simp only [listCode_cons,listCode_append,List.length_append,codeWord_length]
    change _≤2*(2*(listCode code x).length+1+(listCode code l).length)+1+(listCode code r).length
    omega

 lemma flattenStep_iterate_code (a : List (List A)×List A) (k : ℕ) :
    (code (flattenStep^[k] a)).length≤(code a).length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply'];exact (flattenStep_code_le _).trans ih

 lemma flattenStep_iterate {A : Type} [Coding A] (l : List (List A)) (r : List A) :
    flattenStep^[l.length] (l,r)=([],r++l.flatten) := by
  induction l generalizing r with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons,iterate_succ_apply]
    simp [flattenStep,ih,List.append_assoc]

namespace Poly
@[fun_prop] theorem listFlatten : Poly (List.flatten : List (List A) → List A) := by
  have hs : Poly (flattenStep (A:=A)) := by
    unfold flattenStep
    fun_prop
  have ht := hs.iterate TimeBound.variable (by
    intro n a i hi
    have hh := flattenStep_iterate_code a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have ho := (show Poly (Prod.snd : List (List A)×List A → List A) from snd).comp
    (ht.comp (show Poly (fun a : List (List A) => (Unary.mk a.length,(a,([] : List A)))) by fun_prop))
  exact ho.of_eq (by intro a;simp [flattenStep_iterate])

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma concatStep_code_le (a : List BitWord×BitWord) :
    (code (concatStep a)).length≤(code a).length := by
  rcases a with ⟨l,⟨r⟩⟩
  cases l with
  | nil => simp [concatStep]
  | cons x l =>
    simp only [concatStep,List.tail_cons,List.headD_cons,prod_code_length]
    change 2*(listCode code l).length+1+(r++x.val).length≤
      2*(listCode code (x::l)).length+1+r.length
    simp only [listCode_cons,List.length_append,codeWord_length]
    change _≤2*(2*x.val.length+1+(listCode code l).length)+1+r.length
    omega

lemma concatStep_iterate_code (a : List BitWord×BitWord) (k : ℕ) :
    (code (concatStep^[k] a)).length≤(code a).length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply'];exact (concatStep_code_le _).trans ih

lemma concatStep_iterate (l : List BitWord) (r : List Bool) :
    concatStep^[l.length] (l,⟨r⟩)=([],⟨r++l.flatMap BitWord.val⟩) := by
  induction l generalizing r with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons,iterate_succ_apply]
    simp [concatStep,ih,List.append_assoc]

namespace Poly
@[fun_prop] theorem wordConcat : Poly (fun l : List BitWord => BitWord.mk (l.flatMap BitWord.val)) := by
  have hs : Poly concatStep := by
    have hh : Poly (fun a : List BitWord×BitWord => (a.2,a.1.headD ⟨[]⟩)) := by fun_prop
    exact (listTail.comp fst).pair (wordAppend.comp hh)
  have ht := hs.iterate TimeBound.variable (by
    intro n a i hi
    have hh := concatStep_iterate_code a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have ho := (show Poly (Prod.snd : List BitWord×BitWord → BitWord) from snd).comp
    (ht.comp (show Poly (fun a : List BitWord => (Unary.mk a.length,(a,(⟨[]⟩ : BitWord)))) by fun_prop))
  exact ho.of_eq (by intro a;simp [concatStep_iterate])

@[fun_prop] theorem encodeNat : Poly (fun a : ℕ => BitWord.mk (RationalHitting.encodeNat a)) := by
  exact (show Feasible _root_.id _root_.id StackLanguage.encodedWord from ⟨Procedure.encodeWord⟩).recode
    _ _ _ Nat.bits (by intro a;rfl) (by intro a;exact encodedWord_bits a)

@[fun_prop] theorem encodeUnary : Poly (fun a : Unary => BitWord.mk (RationalHitting.encodeNat a.val)) :=
  encodeNat.comp unaryToNat
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

@[fun_prop] theorem matrix_poly : Poly (fun a : Params×GridPoint×Unary => matrix a.1 a.2.1 a.2.2) := by
  have hn : Poly (fun a : Params×GridPoint×Unary => a.1.2.2.1*a.1.2.2.2.1) := by fun_prop
  have he : Poly (fun a : (Params×GridPoint×Unary)×(Unary×Unary) =>
      ((a.1.1.2.2.1,a.1.1.2.1,a.1.1.2.2.2.1),
      (a.1.2.2.toInt,a.1.2.1.1.toInt,a.1.2.1.2.1.toInt,a.1.2.1.2.2.toInt),a.2)) := by fun_prop
  exact Poly.denseBuild hn (entry_poly.comp he)

lemma matrix_eq (n s : ℕ) (x : GridPoint) (a : Fin (n+1)) :
    matrix (Params.of n s) x ⟨a.val⟩ = DenseSquare.of
      (Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x) a) := by
  apply congrArg (fun A => (⟨Generator.D (Parameters.exponent n s),A⟩ : DenseSquare))
  funext i j
  exact entry_eq n _ _ (gridFn x) a i j

@[fun_prop] theorem cramer_poly : Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) =>
    cramer a.1.1 a.1.2 a.2.1.val a.2.2.val) := by
  have hn : Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) => Unary.mk a.1.1.dim) :=
    Poly.denseDim.comp (by fun_prop)
  have hc : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
    Unary.eqb a.2.2 a.1.2.1) := by fun_prop
  have hv : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
    a.1.1.2.get a.2.1.val a.1.2.2.val) := Poly.denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
      (a.1.1.2,(a.2.1,a.1.2.2))) by fun_prop)
  have hw : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
    a.1.1.1.get a.2.1.val a.2.2.val) := Poly.denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
      (a.1.1.1,(a.2.1,a.2.2))) by fun_prop)
  exact (Poly.denseBuild hn (hc.cond hv hw)).of_eq (by
    intro a
    apply congrArg (fun A => (⟨a.1.1.dim,A⟩ : DenseSquare))
    funext i j
    simp [Unary.eqb])

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage.Runtime

lemma cramer_det_of {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (i j : Fin d) :
    (cramer (DenseSquare.of A) (DenseSquare.of B) i.val j.val).val.det=
      (A.updateCol i (fun r => B r j)).det := by
  unfold cramer DenseSquare.of
  apply congrArg Matrix.det
  funext r c
  simp [DenseSquare.get,Matrix.updateCol_apply,Fin.ext_iff]

lemma cramer_encode_of {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (den : ℤ) (i j : Fin d) :
    encodeRat (Rat.divInt (cramer (DenseSquare.of A) (DenseSquare.of B) i.val j.val).val.det den)=
      encodeRat (Rat.divInt (A.updateCol i (fun r => B r j)).det den) :=
  congrArg (fun z => encodeRat (Rat.divInt z den)) (cramer_det_of A B i j)

end RationalHitting.StackLanguage.Runtime

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.GridComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage

lemma range_flatMap_to_finRange {A : Type} (n : ℕ) (f : ℕ → List A) :
    (List.range n).flatMap f=(List.finRange n).flatMap (fun i => f i.val) := by
  rw [←finRange_map_val,List.flatMap_map]

namespace Poly
variable {A B : Type} [Coding A] [Coding B]

theorem tabulateUp {n : A → ℕ} {f : A×Unary → B}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => (List.range (n a)).map (fun i => f (a,⟨i⟩))) :=
  hf.tabulate.comp (hn.pair (show Poly (fun a : A => a) from id))

theorem flatMapUp {n : A → ℕ} {f : A×Unary → List B}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => (List.range (n a)).flatMap (fun i => f (a,⟨i⟩))) :=
  (listFlatten.comp (tabulateUp hn hf)).of_eq (by intro a;rw [List.flatMap_def])

theorem wordRange {n : A → ℕ} {f : A×Unary → BitWord}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => BitWord.mk ((List.range (n a)).flatMap (fun i => (f (a,⟨i⟩)).val))) :=
  (wordConcat.comp (tabulateUp hn hf)).of_eq (by intro a;simp [List.flatMap_map])
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

@[fun_prop] theorem matrixWord_poly : Poly (fun a : MatrixWordArgs => matrixWord a.1.1 a.1.2 a.2) := by
  have hc : Poly (fun a : (MatrixWordArgs×Unary)×Unary =>
      cramer a.1.1.1.1 a.1.1.1.2 a.1.2.val a.2.val) :=
    cramer_poly.comp (show Poly (fun a : (MatrixWordArgs×Unary)×Unary =>
      (a.1.1.1,(a.1.2,a.2))) by fun_prop)
  have hv := Poly.rationalEncode.comp ((Poly.denseDet.comp hc).pair
    (show Poly (fun a : (MatrixWordArgs×Unary)×Unary => a.1.1.2) by fun_prop))
  have hr := Poly.wordRange (Poly.denseDim.comp (show Poly (fun a : MatrixWordArgs×Unary => a.1.1.1) by fun_prop)) hv
  exact Poly.wordRange (Poly.denseDim.comp (show Poly (fun a : MatrixWordArgs => a.1.1) by fun_prop)) hr

lemma matrixWord_of {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (den : ℤ) :
    (matrixWord (DenseSquare.of A) (DenseSquare.of B) den).val=
      (List.finRange d).flatMap (fun i => (List.finRange d).flatMap (fun j =>
        encodeRat (Rat.divInt (A.updateCol i (fun r => B r j)).det den))) := by
  unfold matrixWord
  change (List.range d).flatMap _ = _
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro i hi
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro j hj
  change Fin d at j
  exact cramer_encode_of A B den i j

@[fun_prop] theorem tupleWord_poly : Poly (fun a : TupleWordArgs => tupleWord a.1.1 a.1.2 a.2.1 a.2.2) := by
  have hm : Poly (fun a : TupleWordArgs×Unary => matrix a.1.1.1 a.1.1.2 (a.2+1)) := by fun_prop
  have hv := matrixWord_poly.comp
    (((show Poly (fun a : TupleWordArgs×Unary => a.1.2.1) by fun_prop).pair hm).pair
      (show Poly (fun a : TupleWordArgs×Unary => a.1.2.2) by fun_prop))
  exact Poly.wordRange (show Poly (fun a : TupleWordArgs => a.1.1.1) by fun_prop) hv

lemma tupleWord_eq (n s : ℕ) (x : GridPoint) (den : ℤ) :
    (tupleWord (Params.of n s) x
      (matrix (Params.of n s) x 0) den).val =
      encodeTuple (ExecutableGenerator.tuple (ExecutableGenerator.normalized
        (ExecutableGenerator.inputTables n (Parameters.N n s) (Parameters.exponent n s) (gridFn x)) den)) := by
  unfold tupleWord encodeTuple
  change (List.range n).flatMap _ = _
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro a ha
  let U := Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x)
  have hzero : matrix (Params.of n s) x 0=DenseSquare.of (U 0) := matrix_eq n s x 0
  have hsucc : matrix (Params.of n s) x ⟨a.val+1⟩=DenseSquare.of (U a.succ) := matrix_eq n s x a.succ
  trans (matrixWord (DenseSquare.of (U 0)) (DenseSquare.of (U a.succ)) den).val
  · exact congrArg₂ (fun A B => (matrixWord A B den).val) hzero hsucc
  rw [matrixWord_of]
  apply List.flatMap_congr
  intro i hi
  apply List.flatMap_congr
  intro j hj
  congr 1
  rw [ExecutableGenerator.tuple_normalized,ExecutableGenerator.normalizedEntry,
    DeterminantAlgorithm.determinant_eq,DeterminantAlgorithm.denote_tabulate,
    ExecutableGenerator.inputTables_denote,ExecutableGenerator.inputTables_denote]

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

@[fun_prop] theorem point_poly : Poly (fun a : Params×GridPoint => point a.1 a.2) := by
  have hf : Poly (fun a : TupleWordArgs =>
    if a.2.2=0 then ([] : List BitWord) else [tupleWord a.1.1 a.1.2 a.2.1 a.2.2]) := by
    apply Poly.ite
    · exact Poly.intZero.comp (show Poly (fun a : TupleWordArgs => a.2.2) by fun_prop)
    · exact Poly.const []
    · exact Poly.listSingleton.comp tupleWord_poly
  have hm : Poly (fun a : Params×GridPoint => matrix a.1 a.2 0) := by fun_prop
  exact hf.comp ((show Poly (fun a : Params×GridPoint => a) from Poly.id).pair
    (hm.pair (Poly.denseDet.comp hm)))

lemma matrix_det_eq (n s : ℕ) (x : GridPoint) (a : Fin (n+1)) :
    (matrix (Params.of n s) x ⟨a.val⟩).val.det=
      (Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x) a).det := by
  apply congrArg Matrix.det
  funext i j
  exact entry_eq n _ _ (gridFn x) a i j

lemma point_eq (n s : ℕ) (x : GridPoint) :
    point (Params.of n s) x=
      ((ExecutableGenerator.atPoint n (Parameters.N n s) (Parameters.exponent n s) (gridFn x)).toList.map
        (fun X => BitWord.mk (encodeTuple X))) := by
  unfold point ExecutableGenerator.atPoint
  simp only [DeterminantAlgorithm.determinant_eq,ExecutableGenerator.inputTables_denote]
  have hd : (matrix (Params.of n s) x 0).val.det=
      (Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x) 0).det :=
    matrix_det_eq n s x 0
  rw [hd]
  split_ifs with hz
  · rfl
  · simp only [Option.toList_some,List.map_cons,List.map_nil,List.cons.injEq, and_true]
    apply congrArg BitWord.mk
    exact tupleWord_eq n s x _

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

lemma map_filterMap_toList {A B C : Type} (l : List A) (f : A → Option B) (g : B → C) :
    (l.filterMap f).map g=l.flatMap (fun a => (f a).toList.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [h,ih]

namespace Runtime

@[fun_prop] theorem words_poly : Poly words := by
  have hp : Poly (fun a : ((Params×Unary)×Unary)×Unary =>
      point a.1.1.1 (a.1.1.2+1,a.1.2+1,a.2+1)) := by fun_prop
  have h1 := Poly.flatMapUp (show Poly (fun a : (Params×Unary)×Unary => a.1.1.2.2.2.2) by fun_prop) hp
  have h2 := Poly.flatMapUp (show Poly (fun a : Params×Unary => a.1.2.2.2.2) by fun_prop) h1
  exact Poly.flatMapUp (show Poly (fun a : Params => a.2.2.2.2) by fun_prop) h2

lemma gridFn_fin {H : ℕ} (t p r : Fin H) :
    gridFn (⟨t.val+1⟩,⟨p.val+1⟩,⟨r.val+1⟩)=fun i => (![t,p,r] i).val+1 := by
  funext i;fin_cases i <;> rfl

lemma words_eq (n s : ℕ) : words (Params.of n s)=
    (ExecutableGenerator.list n s).tuples.map (fun X => BitWord.mk (encodeTuple X)) := by
  unfold words
  rw [show (Params.of n s).H=Parameters.H n s from rfl]
  simp only [ExecutableGenerator.list,ExecutableGenerator.output]
  rw [map_filterMap_toList]
  simp only [Generator.grid,List.flatMap_assoc,List.flatMap_map]
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro t ht
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro p hp
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro r hr
  rw [point_eq,gridFn_fin]

end Runtime
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.OutputComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
namespace Runtime

@[fun_prop] theorem word_poly : Poly word := by
  have hd : Poly (fun p : Params => p.2.2.1*p.2.2.2.1) := by fun_prop
  have hn := Poly.encodeUnary.comp (Poly.listLength.comp words_poly)
  have he := Poly.encodeUnary.comp hd
  exact Poly.wordAppend.comp ((Poly.wordAppend.comp (he.pair hn)).pair
    (Poly.wordConcat.comp words_poly))

lemma word_eq (n s : ℕ) : (word (Params.of n s)).val=ExecutableGenerator.encoded n s := by
  unfold word
  rw [words_eq]
  simp only [List.length_map,List.flatMap_map]
  rfl

lemma word_ext {x y : BitWord} (h : x.val=y.val) : x=y := by
  cases x;cases y;congr

theorem output_poly : Poly (fun a : Unary×Unary =>
    BitWord.mk (ExecutableGenerator.encoded a.1.val a.2.val)) :=
  (word_poly.comp Poly.params).of_eq (by intro a;exact word_ext (word_eq _ _))

/-- Polynomial feasibility of the canonical output construction. -/

theorem raw_feasible : Feasible
    (fun a : ℕ×ℕ => ExecutableGenerator.unaryWord a.1 a.2)
    _root_.id (fun a => (ExecutableGenerator.encoded a.1 a.2).reverse) := by
  have ho : Feasible (code : Unary×Unary → List Bool) _root_.id
      (fun a => ExecutableGenerator.encoded a.1.val a.2.val) :=
    output_poly.recode _ _ _ _root_.id (by intro a;rfl) (by intro a;rfl)
  have hi := (show Feasible _ _ _ from ⟨Procedure.unaryInput⟩)
  have hm := ho.comp hi
  have hr := Feasible.reverseWord.comp hm
  exact hr.of_eq (by intro a;simp only [Function.comp_apply])

end Runtime
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.ExecutableGenerator
open StackLanguage

/-- One fixed finite stack program computes the exact canonical list on literal
unary inputs, with a fixed polynomial bound on all actual stack steps. -/
theorem stack_implementation : StackImplementation := by
  obtain ⟨p⟩ := Runtime.raw_feasible
  let f : p.Registers → Fin (Fintype.card p.Registers+1) :=
    fun a => (Fintype.equivFin p.Registers a).castSucc
  have hf : Function.Injective f := by
    intro a b h
    apply (Fintype.equivFin p.Registers).injective
    exact Fin.castSucc_inj.mp h
  obtain ⟨C,k,hC,hk,hbound⟩ := (p.bound.comp (TimeBound.variable+1)).growth
  refine ⟨Fintype.card p.Registers,p.program.rename f,f p.input,f p.output,C,k,hC,hk,?_⟩
  intro n s hn hs
  obtain ⟨t,ht,he⟩ := p.correct (n,s)
  refine ⟨t,?_,?_⟩
  · have hb := hbound (n+s+1) (by omega)
    simp only [TimeBound.eval_comp,TimeBound.eval_add,TimeBound.eval_variable,
      TimeBound.eval_numeral] at hb
    have hlen : (unaryWord n s).length+1=n+s+1+1 := by simp [unaryWord];omega
    have ht' : t≤p.bound.eval ((unaryWord n s).length+1) := ht
    rw [hlen] at ht'
    exact ht'.trans hb
  · have hh := he.rename_single f hf
    simpa only [single,Function.comp_apply,id_eq] using hh

/-- The finite-state compilation of the uniform stack implementation. -/

theorem implementation_oai : Implementation := implementation_of_stack stack_implementation

end RationalHitting.ExecutableGenerator

end OAI
end

theorem solution : type_of% @OAI.RationalHitting.ExecutableGenerator.implementation_oai := @OAI.RationalHitting.ExecutableGenerator.implementation_oai
