-- Prove2me | solution 1 for OAI.RationalHitting.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:17:39.63055+00:00
-- url     : https://prove2.me/submissions/0ea7e246-9c01-4f7f-95fb-a4cbff0d389d

import Mathlib
import Definitions.Def_RationalHitting
import Definitions.Def_OAIQWRHT000
import Theorems.Thm_OAI_RationalHitting_ExecutableGenerator_implementation
import Theorems.Thm_OAI_RationalHitting_Generator_list_hits

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

/-- The finite-state implementation and list bounds imply the main statement. -/
theorem main_of_implementation (hi : Implementation) : MainStatement := by
  obtain ⟨m,G,C,k,hC,hk,hG⟩ := hi
  refine ⟨m,G,C+256+PolynomialBounds.outputConstant,k+104,by omega,by omega,?_⟩
  intro n s hn hs
  have hm : 1 ≤ n+s+1 := by omega
  obtain ⟨hd,ho,hh⟩ := exact_output n s hn hs
  refine ⟨list n s,?_,?_,?_,hh⟩
  · exact hd.trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hm (by omega)))
  · exact ho.trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hm (by omega)))
  · obtain ⟨t,ht,a,hr,hhalt,hout⟩ := hG n s hn hs
    exact ⟨t,ht.trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hm (by omega))),a,hr,hhalt,hout⟩

end RationalHitting.ExecutableGenerator


/-! Quantitative compilation measured in ordinary TM0 transitions. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting

/-- A rational hitting list preserving every inverse domain, with invertible
values, canonical rational binary output, and polynomial deterministic
finite-state Turing time. -/
theorem main_oai : MainStatement :=
  ExecutableGenerator.main_of_implementation ExecutableGenerator.implementation

end RationalHitting

end OAI
end

theorem solution : type_of% @OAI.RationalHitting.main_oai := @OAI.RationalHitting.main_oai
