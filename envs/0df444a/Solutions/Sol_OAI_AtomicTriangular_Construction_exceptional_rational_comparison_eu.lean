-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.exceptional_rational_comparison_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:27:36.155365+00:00
-- url     : https://prove2.me/submissions/921b5d80-c78d-4890-8e2a-30486ef136ac

import Mathlib
import Definitions.Def_OAIQ334E021
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_exceptional_sign_3_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_frozenTaylorRowBox_mem_eu

section
-- module Solutions.OAIQ334_EU.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Auxiliary_Bernstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Finset
noncomputable section
namespace AtomicTriangular.Bernstein

lemma bernsteinBasis_sum (n : ℕ) (x : ℝ) :
    ∑ d ∈ range (n+1), bernsteinBasis n d x = 1 := by
  calc
    _ = (x+(1-x))^n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [bernsteinBasis]
      ring
    _ = 1 := by simp

lemma bernsteinBasis_nonneg (n d : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    0 ≤ bernsteinBasis n d x := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
    (pow_nonneg (by linarith [hx.2]) _)

lemma choose_ratio (n r d : ℕ) (hr : r ≤ n) (hd : r ≤ d) :
    (d.choose r : ℝ)/(n.choose r : ℝ)*(n.choose d : ℝ) =
      ((n-r).choose (d-r) : ℝ) := by
  have h : (n.choose d : ℝ)*(d.choose r : ℝ) =
      (n.choose r : ℝ)*((n-r).choose (d-r) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n:=n) hd
  have hn : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hr
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hn).mpr
  first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

lemma bernstein_monomial (n r : ℕ) (hr : r ≤ n) (x : ℝ) :
    ∑ d ∈ range (n+1), ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x = x^r := by
  let f : ℕ → ℝ := fun d => ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x
  have hlo : ∑ d ∈ range r, f d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [f, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hd)]
  have heq : ∀ d, r ≤ d →
      f d = x^r * ((n-r).choose (d-r) : ℝ)*x^(d-r)*(1-x)^((n-r)-(d-r)) := by
    intro d hd
    dsimp [f,bernsteinBasis]
    rw [show n-d = (n-r)-(d-r) by omega]
    rw [show d = r+(d-r) by omega, pow_add]
    have hratio := choose_ratio n r d hr hd
    rw [show r+(d-r)=d by omega]
    calc
      _ = (((d.choose r : ℝ)/(n.choose r : ℝ))*(n.choose d : ℝ))*
        x^r*x^(d-r)*(1-x)^((n-r)-(d-r)) := by ring
      _ = _ := by rw [hratio]; ring
  change (∑ d ∈ range (n+1), f d) = _
  rw [← Finset.sum_range_add_sum_Ico f (show r ≤ n+1 by omega), hlo, zero_add]
  rw [Finset.sum_Ico_eq_sum_range]
  have he : n+1-r = n-r+1 := by omega
  rw [he]
  calc
    _ = x^r * ∑ j ∈ range (n-r+1), bernsteinBasis (n-r) j x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [heq _ (by omega)]
      simp only [Nat.add_sub_cancel_left, bernsteinBasis]
      ring
    _ = x^r := by rw [bernsteinBasis_sum, mul_one]

lemma bernstein_polynomial (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (∑ d ∈ range (n+1), bernsteinCoefficient n c d * bernsteinBasis n d x) =
      ∑ r ∈ range (n+1), c r * x^r := by
  unfold bernsteinCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = c r * ∑ d ∈ range (n+1),
        ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [bernstein_monomial n r (by simpa using Nat.le_of_lt_succ (mem_range.mp hr))]

lemma bernstein_polynomial_lower (n : ℕ) (c : ℕ → ℝ) (m : ℝ)
    (hc : ∀ d < n+1, m ≤ bernsteinCoefficient n c d)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    m ≤ ∑ r ∈ range (n+1), c r*x^r := by
  rw [← bernstein_polynomial]
  calc
    m = ∑ d ∈ range (n+1), m*bernsteinBasis n d x := by
      rw [← Finset.mul_sum, bernsteinBasis_sum, mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (hc d (mem_range.mp hd)) (bernsteinBasis_nonneg n d hx)

lemma strict_bernstein_bound (n : ℕ) (c : ℕ → ℝ) (m : ℝ)
    (hc : ∀ d < n+1, m < bernsteinCoefficient n c d)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    m < ∑ r ∈ range (n+1), c r*x^r := by
  let b := (range (n+1)).inf' (by simp) (bernsteinCoefficient n c)
  have hb : m < b := by
    dsimp [b]
    exact (Finset.lt_inf'_iff _).mpr (fun d hd => hc d (mem_range.mp hd))
  exact hb.trans_le (bernstein_polynomial_lower n c b (by
    intro d hd
    exact Finset.inf'_le _ (mem_range.mpr hd)) hx)

end AtomicTriangular.Bernstein
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Auxiliary_PolynomialShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.PolynomialShift
lemma shift_sum {N M d : ℕ} (hd : N+d≤M) (a : ℕ → ℝ) (τ : ℝ) :
    (∑ l : Fin (M+1), (if d≤l.val ∧ l.val-d≤N then a (l.val-d) else 0)*τ^l.val) =
      τ^d * ∑ i : Fin (N+1), a i.val*τ^i.val := by
  have he (l : Fin (M+1)) :
      (if d≤l.val ∧ l.val-d≤N then a (l.val-d) else 0) =
        ∑ i : Fin (N+1), if l.val=i.val+d then a i.val else 0 := by
    by_cases hl : d≤l.val ∧ l.val-d≤N
    · rw [ite_eq_left hl]
      symm
      rw [Finset.sum_eq_single (⟨l.val-d,by omega⟩ : Fin (N+1))]
      · simp only [Nat.sub_add_cancel hl.1,ite_true, if_true]
      · intro b _ hb
        rw [ite_eq_right]
        intro h
        apply hb
        apply Fin.ext
        change b.val = l.val-d
        omega
      · simp
    · rw [ite_eq_right hl]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [ite_eq_right]
      omega
  simp_rw [he,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  trans ∑ i : Fin (N+1), a i.val*τ^(i.val+d)
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (⟨i.val+d,by omega⟩ : Fin (M+1))]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro h
      exact hb (Fin.ext h)
    · simp
  · simp_rw [pow_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
end AtomicTriangular.PolynomialShift
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

lemma RI.mem_pow {a : RI} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [RI.pow] using RI.mem_point 1
  | succ n ih => simpa [RI.pow,pow_succ] using RI.mem_mul ih hx

noncomputable section
open scoped BigOperators

lemma RI.mem_min {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.imin b).Mem (min x y) := by
  constructor
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.1 hy.1
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.2 hy.2

end
end AtomicTriangular.Interval

end
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_Polytope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma box_linear_lower {B x c : ℝ} (_hB : 0 ≤ B) (hx : 0 ≤ x) (hxB : x ≤ B) :
    B * min 0 c ≤ c*x := by
  by_cases hc : 0 ≤ c
  · rw [min_eq_left hc]
    simpa using mul_nonneg hc hx
  · rw [min_eq_right (le_of_not_ge hc)]
    nlinarith

lemma triangle_linear_lower {B Z u a v c : ℝ} (_hB : 0 ≤ B) (hu : 0 ≤ u)
    (huB : u ≤ B) (ha : 0 ≤ a) (haZ : a ≤ Z*u) :
    B * min 0 (min v (v+Z*c)) ≤ v*u+c*a := by
  let q := min 0 (min v (v+Z*c))
  have hq0 : q ≤ 0 := min_le_left _ _
  have hqv : q ≤ v := (min_le_right _ _).trans (min_le_left _ _)
  have hqc : q ≤ v+Z*c := (min_le_right _ _).trans (min_le_right _ _)
  have hqu : B*q ≤ u*q := mul_le_mul_of_nonpos_right huB hq0
  change B*q ≤ _
  by_cases hc : 0 ≤ c
  · have h1 := mul_le_mul_of_nonneg_right hqv hu
    have h2 := mul_nonneg hc ha
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_right hqc hu
    have h2 := mul_le_mul_of_nonpos_left haZ (le_of_not_ge hc)
    nlinarith

lemma rowLower_le (row e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    rowLower row ≤ ∑ j : Fin 8, row j*e j := by
  rcases he with ⟨z,w,d,u,a,r,p,hz,hzB,hw,hwB,hd,hdB,hu,huB,ha,haB,hr,hrB,hp,hpB,rfl⟩
  have h1 := box_linear_lower (by norm_num [Z] : 0 ≤ Z) hz hzB (c := row 0)
  have h2 := box_linear_lower (by norm_num [DeltaStar] : 0 ≤ DeltaStar) hd hdB (c := -row 2)
  have h3 := box_linear_lower (by norm_num [Wstar] : 0 ≤ Wstar) hw hwB (c := row 3+Z*row 2)
  have h4 := triangle_linear_lower (by norm_num [Ustar] : 0 ≤ Ustar) hu huB ha haB (v := row 5) (c := row 4)
  have h5 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hr hrB (c := row 6)
  have h6 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hp hpB (c := row 7)
  norm_num [Fin.sum_univ_succ, Fin.succ]
  change rowLower row ≤ row 0*z + (row 1 + (row 2*(Z*w-d) + (row 3*w + (row 4*a + (row 5*u + (row 6*r + row 7*p))))))
  unfold rowLower
  nlinarith [h1,h2,h3,h4,h5,h6]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ZBox_mem : ZBox.Mem Z := RI.mem_divNat (RI.mem_point 391) (by norm_num)
lemma WstarBox_mem : WstarBox.Mem Wstar := RI.mem_divNat (RI.mem_point 61) (by norm_num)
lemma DeltaStarBox_mem : DeltaStarBox.Mem DeltaStar := RI.mem_divNat (RI.mem_point 18) (by norm_num)
lemma UstarBox_mem : UstarBox.Mem Ustar := RI.mem_divNat (RI.mem_point 48) (by norm_num)
lemma PstarBox_mem : PstarBox.Mem Pstar := RI.mem_divNat (RI.mem_point 3) (by norm_num)
lemma rowLowerBox_mem {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ i, (a i).Mem (v i)) : (rowLowerBox a).Mem (rowLower v) := by
  have hz : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
  unfold rowLowerBox rowLower
  apply RI.mem_add
  · apply RI.mem_add
    · apply RI.mem_add
      · apply RI.mem_add
        · exact RI.mem_add (hv 1) (RI.mem_mul ZBox_mem (RI.mem_min hz (hv 0)))
        · exact RI.mem_mul DeltaStarBox_mem (RI.mem_min hz (RI.mem_neg (hv 2)))
      · exact RI.mem_mul WstarBox_mem (RI.mem_min hz (RI.mem_add (hv 3) (RI.mem_mul ZBox_mem (hv 2))))
    · exact RI.mem_mul UstarBox_mem (RI.mem_min hz (RI.mem_min (hv 5) (RI.mem_add (hv 5) (RI.mem_mul ZBox_mem (hv 4)))))
  · exact RI.mem_mul PstarBox_mem (RI.mem_add (RI.mem_min hz (hv 6)) (RI.mem_min hz (hv 7)))
end AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction
open Bernstein

lemma bernsteinRows_dot (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ)
    (d : Fin (n+1)) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8, bernsteinRows n a d r*e r) =
      ∑ l : Fin (n+1), ((d.val.choose l.val:ℝ)/(n.choose l.val:ℝ))*(∑ r : Fin 8, a l r*e r) := by
  simp only [bernsteinRows,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
lemma polytope_polynomial_lower (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ) (m : ℝ)
    (hm : ∀ d, m < rowLower (bernsteinRows n a d))
    (e : Fin 8 → ℝ) (he : ParameterPolytope e) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    m < ∑ l : Fin (n+1), (∑ r : Fin 8, a l r*e r)*τ^l.val := by
  let c : ℕ → ℝ := fun l => if hl : l<n+1 then ∑ r : Fin 8, a ⟨l,hl⟩ r*e r else 0
  have hb : ∀ d < n+1, m < bernsteinCoefficient n c d := by
    intro d hd
    have hh := (hm ⟨d,hd⟩).trans_le (rowLower_le (bernsteinRows n a ⟨d,hd⟩) e he)
    rw [bernsteinRows_dot] at hh
    have heq : bernsteinCoefficient n c d =
        ∑ l : Fin (n+1), ((d.choose l.val:ℝ)/(n.choose l.val:ℝ))*(∑ r : Fin 8, a l r*e r) := by
      unfold bernsteinCoefficient
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [c,dite_eq_left l.isLt]
    rwa [heq]
  have hh := strict_bernstein_bound n c m hb hτ
  rw [← Fin.sum_univ_eq_sum_range] at hh
  simpa only [c,Fin.is_lt,dite_eq_left] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_Exceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma polytope_one (e : Fin 8 → ℝ) (he : ParameterPolytope e) : e 1=1 := by
  rcases he with ⟨z,w,d,u,a,r,p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩
  rfl
lemma frozenTaylorRow_eval (z : ℝ) (l : ℕ) (e : Fin 8 → ℝ) (he : e 1=1) :
    (∑ r : Fin 8, frozenTaylorRow z l r*e r) =
      -∑ r : Fin 8, taylorRow 0 1 1 l r*freezeParameter z e r := by
  simp only [frozenTaylorRow,freezeParameter,Fin.sum_univ_succ,Fin.val_zero,
    ite_true, if_true,Fin.val_succ,Fin.succ_zero_eq_one]
  norm_num
  rw [he]
  ring

lemma frozenTaylor_eq (z : ℝ) (e : Fin 8 → ℝ) (he : e 1=1) (τ : ℝ) :
    frozenTaylor z e τ = -finiteTaylor 0 1 1 (freezeParameter z e) τ := by
  simp_rw [frozenTaylor,frozenTaylorRow_eval z _ e he,neg_mul,Finset.sum_neg_distrib]
  rw [finiteTaylor,←Fin.sum_univ_eq_sum_range]

lemma exceptionalRow_eval (test : Fin 4) (e : Fin 8 → ℝ) (he : e 1=1) (τ : ℝ) :
    (∑ l : Fin 23, (∑ r : Fin 8, exceptionalRow test l r*e r)*τ^l.val) =
      exceptionalValue test e τ := by
  have hoff : (∑ l : Fin 23, (∑ r : Fin 8, exceptionalOffset test l.val r*e r)*τ^l.val) =
      (if test.val=0 then Q 1 else Q 1*(τ+test.val*Z)) := by
    simp only [exceptionalOffset,ite_mul,zero_mul]
    fin_cases test <;> norm_num [Fin.sum_univ_succ,Fin.succ,he] <;> ring
  have hshift (ep : Fin 2) (j : Fin 3) :
      (∑ l : Fin 23, (∑ r : Fin 8,
        (if j.val≤l.val ∧ l.val-j.val<21 then
          exceptionalWeight test ep j*frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0)*e r)*τ^l.val) =
        exceptionalWeight test ep j*τ^j.val*frozenTaylor (if ep.val=0 then 0 else Z) e τ := by
    simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp_rw [mul_assoc,←Finset.mul_sum]
    have hh := PolynomialShift.shift_sum (N:=20) (M:=22) (d:=j.val) (by omega)
      (fun l => ∑ r : Fin 8, frozenTaylorRow (if ep.val=0 then 0 else Z) l r*e r) τ
    have hcond (l : Fin 23) : (j.val≤l.val ∧ l.val-j.val<21) ↔ (j.val≤l.val ∧ l.val-j.val≤20) := by omega
    have hfac (c : Prop) [Decidable c] (x : ℝ) :
        (if c then exceptionalWeight test ep j*x else 0) =
          exceptionalWeight test ep j*(if c then x else 0) := by split_ifs <;> simp
    simp only [hcond,hfac, mul_assoc,←Finset.mul_sum]
    simp only [ite_mul,zero_mul] at hh
    rw [hh]
    rfl
  simp only [exceptionalRow,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  simp only [Finset.sum_mul] at hoff
  rw [hoff]
  have hex : (∑ l : Fin 23, (∑ r : Fin 8, ∑ ep : Fin 2, ∑ j : Fin 3,
      (if j.val≤l.val ∧ l.val-j.val<21 then
          exceptionalWeight test ep j*frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0)*e r)*τ^l.val) =
      ∑ ep : Fin 2, ∑ j : Fin 3,
        exceptionalWeight test ep j*τ^j.val*frozenTaylor (if ep.val=0 then 0 else Z) e τ := by
    simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Fin 8)) (t:=Finset.univ (α:=Fin 2)),
      Finset.sum_comm (s:=Finset.univ (α:=Fin 8)) (t:=Finset.univ (α:=Fin 3)),Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ep _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Finset.sum_mul] using hshift ep j
  simp only [Finset.sum_mul] at hex
  rw [hex]
  fin_cases test <;> norm_num [exceptionalValue,exceptionalWeight,Fin.sum_univ_succ,Fin.succ] <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma bernsteinRowsBox_mem (n : ℕ) {a : Fin (n+1) → Fin 8 → RI}
    {v : Fin (n+1) → Fin 8 → ℝ} (hv : ∀ l r, (a l r).Mem (v l r))
    (d : Fin (n+1)) (r : Fin 8) :
    (bernsteinRowsBox n a d r).Mem (bernsteinRows n v d r) := by
  apply RI.mem_sum
  intro l
  apply RI.mem_mul _ (hv l r)
  have hh := RI.mem_divNat (RI.mem_point (d.val.choose l.val))
    (Nat.choose_pos (show l.val≤n by omega))
  simpa only [Int.cast_natCast] using hh
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ep0 : (RI.point 0).Mem (0 : ℝ) := by simpa using RI.mem_point 0
lemma ep1 : (RI.point 1).Mem (1 : ℝ) := by simpa using RI.mem_point 1
lemma ep2 : (RI.point 2).Mem (2 : ℝ) := by simpa using RI.mem_point 2
lemma ep4 : (RI.point 4).Mem (4 : ℝ) := by simpa using RI.mem_point 4
lemma ep6 : (RI.point 6).Mem (6 : ℝ) := by simpa using RI.mem_point 6

lemma exceptionalWeightBox_mem (test : Fin 4) (ep : Fin 2) (j : Fin 3) :
    (exceptionalWeightBox test ep j).Mem (exceptionalWeight test ep j) := by
  unfold exceptionalWeightBox exceptionalWeight
  split_ifs
  all_goals first
    | exact ep0
    | exact ep1
    | exact RI.mem_divNat ep1 (by norm_num)
    | exact RI.mem_divNat ep2 (by norm_num)
    | exact RI.mem_divNat (RI.mem_mul ep4 ZBox_mem) (by norm_num)
    | exact RI.mem_mul ep2 (RI.mem_pow ZBox_mem 2)
    | exact RI.mem_mul ep6 (RI.mem_pow ZBox_mem 2)
    | exact RI.mem_mul ep4 ZBox_mem

lemma exceptionalOffsetBox_mem (test : Fin 4) (l : ℕ) (r : Fin 8) :
    (exceptionalOffsetBox test l r).Mem (exceptionalOffset test l r) := by
  unfold exceptionalOffsetBox exceptionalOffset
  split_ifs
  · exact RI.mem_mul QBox1_mem ep1
  · exact RI.mem_mul QBox1_mem (RI.mem_mul (by simpa using RI.mem_point (test.val:ℤ)) ZBox_mem)
  · exact QBox1_mem
  · exact ep0
  · exact ep0

lemma exceptionalRowBox_mem (test : Fin 4) (l : Fin 23) (r : Fin 8) :
    (exceptionalRowBox test l r).Mem (exceptionalRow test l r) := by
  unfold exceptionalRowBox exceptionalRow
  apply RI.mem_add (exceptionalOffsetBox_mem test l.val r)
  apply RI.mem_sum
  intro ep
  apply RI.mem_sum
  intro j
  split
  · apply RI.mem_mul (exceptionalWeightBox_mem test ep j)
    apply frozenTaylorRowBox_mem_eu
    split_ifs
    · exact ep0
    · exact ZBox_mem
  · exact ep0
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0r0_calc (r : Fin 8) : exceptionalRowBox 0 0 r = ex0r0 r := by
  revert r
  decide +kernel
lemma ex0r1_calc (r : Fin 8) : exceptionalRowBox 0 1 r = ex0r1 r := by
  revert r
  decide +kernel
lemma ex0r2_calc (r : Fin 8) : exceptionalRowBox 0 2 r = ex0r2 r := by
  revert r
  decide +kernel
lemma ex0r3_calc (r : Fin 8) : exceptionalRowBox 0 3 r = ex0r3 r := by
  revert r
  decide +kernel
lemma ex0r4_calc (r : Fin 8) : exceptionalRowBox 0 4 r = ex0r4 r := by
  revert r
  decide +kernel
lemma ex0r5_calc (r : Fin 8) : exceptionalRowBox 0 5 r = ex0r5 r := by
  revert r
  decide +kernel
lemma ex0r6_calc (r : Fin 8) : exceptionalRowBox 0 6 r = ex0r6 r := by
  revert r
  decide +kernel
lemma ex0r7_calc (r : Fin 8) : exceptionalRowBox 0 7 r = ex0r7 r := by
  revert r
  decide +kernel
lemma ex0r8_calc (r : Fin 8) : exceptionalRowBox 0 8 r = ex0r8 r := by
  revert r
  decide +kernel
lemma ex0r9_calc (r : Fin 8) : exceptionalRowBox 0 9 r = ex0r9 r := by
  revert r
  decide +kernel
lemma ex0r10_calc (r : Fin 8) : exceptionalRowBox 0 10 r = ex0r10 r := by
  revert r
  decide +kernel
lemma ex0r11_calc (r : Fin 8) : exceptionalRowBox 0 11 r = ex0r11 r := by
  revert r
  decide +kernel
lemma ex0r12_calc (r : Fin 8) : exceptionalRowBox 0 12 r = ex0r12 r := by
  revert r
  decide +kernel
lemma ex0r13_calc (r : Fin 8) : exceptionalRowBox 0 13 r = ex0r13 r := by
  revert r
  decide +kernel
lemma ex0r14_calc (r : Fin 8) : exceptionalRowBox 0 14 r = ex0r14 r := by
  revert r
  decide +kernel
lemma ex0r15_calc (r : Fin 8) : exceptionalRowBox 0 15 r = ex0r15 r := by
  revert r
  decide +kernel
lemma ex0r16_calc (r : Fin 8) : exceptionalRowBox 0 16 r = ex0r16 r := by
  revert r
  decide +kernel
lemma ex0r17_calc (r : Fin 8) : exceptionalRowBox 0 17 r = ex0r17 r := by
  revert r
  decide +kernel
lemma ex0r18_calc (r : Fin 8) : exceptionalRowBox 0 18 r = ex0r18 r := by
  revert r
  decide +kernel
lemma ex0r19_calc (r : Fin 8) : exceptionalRowBox 0 19 r = ex0r19 r := by
  revert r
  decide +kernel
lemma ex0r20_calc (r : Fin 8) : exceptionalRowBox 0 20 r = ex0r20 r := by
  revert r
  decide +kernel
lemma ex0r21_calc (r : Fin 8) : exceptionalRowBox 0 21 r = ex0r21 r := by
  revert r
  decide +kernel
lemma ex0r22_calc (r : Fin 8) : exceptionalRowBox 0 22 r = ex0r22 r := by
  revert r
  decide +kernel
lemma ex0r_mem (l : Fin 23) (r : Fin 8) : (ex0r l r).Mem (exceptionalRow 0 l r) := by
  have he : exceptionalRowBox 0 l r = ex0r l r := by
    fin_cases l
    · exact ex0r0_calc r
    · exact ex0r1_calc r
    · exact ex0r2_calc r
    · exact ex0r3_calc r
    · exact ex0r4_calc r
    · exact ex0r5_calc r
    · exact ex0r6_calc r
    · exact ex0r7_calc r
    · exact ex0r8_calc r
    · exact ex0r9_calc r
    · exact ex0r10_calc r
    · exact ex0r11_calc r
    · exact ex0r12_calc r
    · exact ex0r13_calc r
    · exact ex0r14_calc r
    · exact ex0r15_calc r
    · exact ex0r16_calc r
    · exact ex0r17_calc r
    · exact ex0r18_calc r
    · exact ex0r19_calc r
    · exact ex0r20_calc r
    · exact ex0r21_calc r
    · exact ex0r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 0 l r
lemma ex0b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 0 r = ex0b0 r := by
  revert r
  decide +kernel
lemma ex0b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 1 r = ex0b1 r := by
  revert r
  decide +kernel
lemma ex0b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 2 r = ex0b2 r := by
  revert r
  decide +kernel
lemma ex0b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 3 r = ex0b3 r := by
  revert r
  decide +kernel
lemma ex0b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 4 r = ex0b4 r := by
  revert r
  decide +kernel
lemma ex0b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 5 r = ex0b5 r := by
  revert r
  decide +kernel
lemma ex0b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 6 r = ex0b6 r := by
  revert r
  decide +kernel
lemma ex0b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 7 r = ex0b7 r := by
  revert r
  decide +kernel
lemma ex0b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 8 r = ex0b8 r := by
  revert r
  decide +kernel
lemma ex0b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 9 r = ex0b9 r := by
  revert r
  decide +kernel
lemma ex0b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 10 r = ex0b10 r := by
  revert r
  decide +kernel
lemma ex0b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 11 r = ex0b11 r := by
  revert r
  decide +kernel
lemma ex0b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 12 r = ex0b12 r := by
  revert r
  decide +kernel
lemma ex0b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 13 r = ex0b13 r := by
  revert r
  decide +kernel
lemma ex0b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 14 r = ex0b14 r := by
  revert r
  decide +kernel
lemma ex0b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 15 r = ex0b15 r := by
  revert r
  decide +kernel
lemma ex0b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 16 r = ex0b16 r := by
  revert r
  decide +kernel
lemma ex0b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 17 r = ex0b17 r := by
  revert r
  decide +kernel
lemma ex0b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 18 r = ex0b18 r := by
  revert r
  decide +kernel
lemma ex0b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 19 r = ex0b19 r := by
  revert r
  decide +kernel
lemma ex0b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 20 r = ex0b20 r := by
  revert r
  decide +kernel
lemma ex0b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 21 r = ex0b21 r := by
  revert r
  decide +kernel
lemma ex0b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 22 r = ex0b22 r := by
  revert r
  decide +kernel
lemma ex0b_mem (l : Fin 23) (r : Fin 8) : (ex0b l r).Mem (bernsteinRows 22 (exceptionalRow 0) l r) := by
  have he : bernsteinRowsBox 22 ex0r l r = ex0b l r := by
    fin_cases l
    · exact ex0b0_calc r
    · exact ex0b1_calc r
    · exact ex0b2_calc r
    · exact ex0b3_calc r
    · exact ex0b4_calc r
    · exact ex0b5_calc r
    · exact ex0b6_calc r
    · exact ex0b7_calc r
    · exact ex0b8_calc r
    · exact ex0b9_calc r
    · exact ex0b10_calc r
    · exact ex0b11_calc r
    · exact ex0b12_calc r
    · exact ex0b13_calc r
    · exact ex0b14_calc r
    · exact ex0b15_calc r
    · exact ex0b16_calc r
    · exact ex0b17_calc r
    · exact ex0b18_calc r
    · exact ex0b19_calc r
    · exact ex0b20_calc r
    · exact ex0b21_calc r
    · exact ex0b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex0r_mem l r
lemma ex0b_lower (d : Fin 23) : (46/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 0) d) := by
  have hc : ∀ d : Fin 23, (46:ℤ)*scale < 1000*(rowLowerBox (ex0b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex0b_mem d)).1
  have hnum : (46:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex0b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_0 (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (46/1000:ℝ) < exceptionalValue 0 e τ := by
  rw [←exceptionalRow_eval 0 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 0) _ ex0b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex1r0_calc (r : Fin 8) : exceptionalRowBox 1 0 r = ex1r0 r := by
  revert r
  decide +kernel
lemma ex1r1_calc (r : Fin 8) : exceptionalRowBox 1 1 r = ex1r1 r := by
  revert r
  decide +kernel
lemma ex1r2_calc (r : Fin 8) : exceptionalRowBox 1 2 r = ex1r2 r := by
  revert r
  decide +kernel
lemma ex1r3_calc (r : Fin 8) : exceptionalRowBox 1 3 r = ex1r3 r := by
  revert r
  decide +kernel
lemma ex1r4_calc (r : Fin 8) : exceptionalRowBox 1 4 r = ex1r4 r := by
  revert r
  decide +kernel
lemma ex1r5_calc (r : Fin 8) : exceptionalRowBox 1 5 r = ex1r5 r := by
  revert r
  decide +kernel
lemma ex1r6_calc (r : Fin 8) : exceptionalRowBox 1 6 r = ex1r6 r := by
  revert r
  decide +kernel
lemma ex1r7_calc (r : Fin 8) : exceptionalRowBox 1 7 r = ex1r7 r := by
  revert r
  decide +kernel
lemma ex1r8_calc (r : Fin 8) : exceptionalRowBox 1 8 r = ex1r8 r := by
  revert r
  decide +kernel
lemma ex1r9_calc (r : Fin 8) : exceptionalRowBox 1 9 r = ex1r9 r := by
  revert r
  decide +kernel
lemma ex1r10_calc (r : Fin 8) : exceptionalRowBox 1 10 r = ex1r10 r := by
  revert r
  decide +kernel
lemma ex1r11_calc (r : Fin 8) : exceptionalRowBox 1 11 r = ex1r11 r := by
  revert r
  decide +kernel
lemma ex1r12_calc (r : Fin 8) : exceptionalRowBox 1 12 r = ex1r12 r := by
  revert r
  decide +kernel
lemma ex1r13_calc (r : Fin 8) : exceptionalRowBox 1 13 r = ex1r13 r := by
  revert r
  decide +kernel
lemma ex1r14_calc (r : Fin 8) : exceptionalRowBox 1 14 r = ex1r14 r := by
  revert r
  decide +kernel
lemma ex1r15_calc (r : Fin 8) : exceptionalRowBox 1 15 r = ex1r15 r := by
  revert r
  decide +kernel
lemma ex1r16_calc (r : Fin 8) : exceptionalRowBox 1 16 r = ex1r16 r := by
  revert r
  decide +kernel
lemma ex1r17_calc (r : Fin 8) : exceptionalRowBox 1 17 r = ex1r17 r := by
  revert r
  decide +kernel
lemma ex1r18_calc (r : Fin 8) : exceptionalRowBox 1 18 r = ex1r18 r := by
  revert r
  decide +kernel
lemma ex1r19_calc (r : Fin 8) : exceptionalRowBox 1 19 r = ex1r19 r := by
  revert r
  decide +kernel
lemma ex1r20_calc (r : Fin 8) : exceptionalRowBox 1 20 r = ex1r20 r := by
  revert r
  decide +kernel
lemma ex1r21_calc (r : Fin 8) : exceptionalRowBox 1 21 r = ex1r21 r := by
  revert r
  decide +kernel
lemma ex1r22_calc (r : Fin 8) : exceptionalRowBox 1 22 r = ex1r22 r := by
  revert r
  decide +kernel
lemma ex1r_mem (l : Fin 23) (r : Fin 8) : (ex1r l r).Mem (exceptionalRow 1 l r) := by
  have he : exceptionalRowBox 1 l r = ex1r l r := by
    fin_cases l
    · exact ex1r0_calc r
    · exact ex1r1_calc r
    · exact ex1r2_calc r
    · exact ex1r3_calc r
    · exact ex1r4_calc r
    · exact ex1r5_calc r
    · exact ex1r6_calc r
    · exact ex1r7_calc r
    · exact ex1r8_calc r
    · exact ex1r9_calc r
    · exact ex1r10_calc r
    · exact ex1r11_calc r
    · exact ex1r12_calc r
    · exact ex1r13_calc r
    · exact ex1r14_calc r
    · exact ex1r15_calc r
    · exact ex1r16_calc r
    · exact ex1r17_calc r
    · exact ex1r18_calc r
    · exact ex1r19_calc r
    · exact ex1r20_calc r
    · exact ex1r21_calc r
    · exact ex1r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 1 l r
lemma ex1b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 0 r = ex1b0 r := by
  revert r
  decide +kernel
lemma ex1b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 1 r = ex1b1 r := by
  revert r
  decide +kernel
lemma ex1b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 2 r = ex1b2 r := by
  revert r
  decide +kernel
lemma ex1b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 3 r = ex1b3 r := by
  revert r
  decide +kernel
lemma ex1b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 4 r = ex1b4 r := by
  revert r
  decide +kernel
lemma ex1b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 5 r = ex1b5 r := by
  revert r
  decide +kernel
lemma ex1b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 6 r = ex1b6 r := by
  revert r
  decide +kernel
lemma ex1b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 7 r = ex1b7 r := by
  revert r
  decide +kernel
lemma ex1b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 8 r = ex1b8 r := by
  revert r
  decide +kernel
lemma ex1b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 9 r = ex1b9 r := by
  revert r
  decide +kernel
lemma ex1b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 10 r = ex1b10 r := by
  revert r
  decide +kernel
lemma ex1b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 11 r = ex1b11 r := by
  revert r
  decide +kernel
lemma ex1b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 12 r = ex1b12 r := by
  revert r
  decide +kernel
lemma ex1b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 13 r = ex1b13 r := by
  revert r
  decide +kernel
lemma ex1b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 14 r = ex1b14 r := by
  revert r
  decide +kernel
lemma ex1b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 15 r = ex1b15 r := by
  revert r
  decide +kernel
lemma ex1b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 16 r = ex1b16 r := by
  revert r
  decide +kernel
lemma ex1b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 17 r = ex1b17 r := by
  revert r
  decide +kernel
lemma ex1b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 18 r = ex1b18 r := by
  revert r
  decide +kernel
lemma ex1b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 19 r = ex1b19 r := by
  revert r
  decide +kernel
lemma ex1b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 20 r = ex1b20 r := by
  revert r
  decide +kernel
lemma ex1b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 21 r = ex1b21 r := by
  revert r
  decide +kernel
lemma ex1b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 22 r = ex1b22 r := by
  revert r
  decide +kernel
lemma ex1b_mem (l : Fin 23) (r : Fin 8) : (ex1b l r).Mem (bernsteinRows 22 (exceptionalRow 1) l r) := by
  have he : bernsteinRowsBox 22 ex1r l r = ex1b l r := by
    fin_cases l
    · exact ex1b0_calc r
    · exact ex1b1_calc r
    · exact ex1b2_calc r
    · exact ex1b3_calc r
    · exact ex1b4_calc r
    · exact ex1b5_calc r
    · exact ex1b6_calc r
    · exact ex1b7_calc r
    · exact ex1b8_calc r
    · exact ex1b9_calc r
    · exact ex1b10_calc r
    · exact ex1b11_calc r
    · exact ex1b12_calc r
    · exact ex1b13_calc r
    · exact ex1b14_calc r
    · exact ex1b15_calc r
    · exact ex1b16_calc r
    · exact ex1b17_calc r
    · exact ex1b18_calc r
    · exact ex1b19_calc r
    · exact ex1b20_calc r
    · exact ex1b21_calc r
    · exact ex1b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex1r_mem l r
lemma ex1b_lower (d : Fin 23) : (56/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 1) d) := by
  have hc : ∀ d : Fin 23, (56:ℤ)*scale < 1000*(rowLowerBox (ex1b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex1b_mem d)).1
  have hnum : (56:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex1b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_1 (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (56/1000:ℝ) < exceptionalValue 1 e τ := by
  rw [←exceptionalRow_eval 1 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 1) _ ex1b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_ExceptionalSign2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex2r0_calc (r : Fin 8) : exceptionalRowBox 2 0 r = ex2r0 r := by
  revert r
  decide +kernel
lemma ex2r1_calc (r : Fin 8) : exceptionalRowBox 2 1 r = ex2r1 r := by
  revert r
  decide +kernel
lemma ex2r2_calc (r : Fin 8) : exceptionalRowBox 2 2 r = ex2r2 r := by
  revert r
  decide +kernel
lemma ex2r3_calc (r : Fin 8) : exceptionalRowBox 2 3 r = ex2r3 r := by
  revert r
  decide +kernel
lemma ex2r4_calc (r : Fin 8) : exceptionalRowBox 2 4 r = ex2r4 r := by
  revert r
  decide +kernel
lemma ex2r5_calc (r : Fin 8) : exceptionalRowBox 2 5 r = ex2r5 r := by
  revert r
  decide +kernel
lemma ex2r6_calc (r : Fin 8) : exceptionalRowBox 2 6 r = ex2r6 r := by
  revert r
  decide +kernel
lemma ex2r7_calc (r : Fin 8) : exceptionalRowBox 2 7 r = ex2r7 r := by
  revert r
  decide +kernel
lemma ex2r8_calc (r : Fin 8) : exceptionalRowBox 2 8 r = ex2r8 r := by
  revert r
  decide +kernel
lemma ex2r9_calc (r : Fin 8) : exceptionalRowBox 2 9 r = ex2r9 r := by
  revert r
  decide +kernel
lemma ex2r10_calc (r : Fin 8) : exceptionalRowBox 2 10 r = ex2r10 r := by
  revert r
  decide +kernel
lemma ex2r11_calc (r : Fin 8) : exceptionalRowBox 2 11 r = ex2r11 r := by
  revert r
  decide +kernel
lemma ex2r12_calc (r : Fin 8) : exceptionalRowBox 2 12 r = ex2r12 r := by
  revert r
  decide +kernel
lemma ex2r13_calc (r : Fin 8) : exceptionalRowBox 2 13 r = ex2r13 r := by
  revert r
  decide +kernel
lemma ex2r14_calc (r : Fin 8) : exceptionalRowBox 2 14 r = ex2r14 r := by
  revert r
  decide +kernel
lemma ex2r15_calc (r : Fin 8) : exceptionalRowBox 2 15 r = ex2r15 r := by
  revert r
  decide +kernel
lemma ex2r16_calc (r : Fin 8) : exceptionalRowBox 2 16 r = ex2r16 r := by
  revert r
  decide +kernel
lemma ex2r17_calc (r : Fin 8) : exceptionalRowBox 2 17 r = ex2r17 r := by
  revert r
  decide +kernel
lemma ex2r18_calc (r : Fin 8) : exceptionalRowBox 2 18 r = ex2r18 r := by
  revert r
  decide +kernel
lemma ex2r19_calc (r : Fin 8) : exceptionalRowBox 2 19 r = ex2r19 r := by
  revert r
  decide +kernel
lemma ex2r20_calc (r : Fin 8) : exceptionalRowBox 2 20 r = ex2r20 r := by
  revert r
  decide +kernel
lemma ex2r21_calc (r : Fin 8) : exceptionalRowBox 2 21 r = ex2r21 r := by
  revert r
  decide +kernel
lemma ex2r22_calc (r : Fin 8) : exceptionalRowBox 2 22 r = ex2r22 r := by
  revert r
  decide +kernel
lemma ex2r_mem (l : Fin 23) (r : Fin 8) : (ex2r l r).Mem (exceptionalRow 2 l r) := by
  have he : exceptionalRowBox 2 l r = ex2r l r := by
    fin_cases l
    · exact ex2r0_calc r
    · exact ex2r1_calc r
    · exact ex2r2_calc r
    · exact ex2r3_calc r
    · exact ex2r4_calc r
    · exact ex2r5_calc r
    · exact ex2r6_calc r
    · exact ex2r7_calc r
    · exact ex2r8_calc r
    · exact ex2r9_calc r
    · exact ex2r10_calc r
    · exact ex2r11_calc r
    · exact ex2r12_calc r
    · exact ex2r13_calc r
    · exact ex2r14_calc r
    · exact ex2r15_calc r
    · exact ex2r16_calc r
    · exact ex2r17_calc r
    · exact ex2r18_calc r
    · exact ex2r19_calc r
    · exact ex2r20_calc r
    · exact ex2r21_calc r
    · exact ex2r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 2 l r
lemma ex2b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 0 r = ex2b0 r := by
  revert r
  decide +kernel
lemma ex2b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 1 r = ex2b1 r := by
  revert r
  decide +kernel
lemma ex2b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 2 r = ex2b2 r := by
  revert r
  decide +kernel
lemma ex2b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 3 r = ex2b3 r := by
  revert r
  decide +kernel
lemma ex2b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 4 r = ex2b4 r := by
  revert r
  decide +kernel
lemma ex2b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 5 r = ex2b5 r := by
  revert r
  decide +kernel
lemma ex2b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 6 r = ex2b6 r := by
  revert r
  decide +kernel
lemma ex2b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 7 r = ex2b7 r := by
  revert r
  decide +kernel
lemma ex2b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 8 r = ex2b8 r := by
  revert r
  decide +kernel
lemma ex2b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 9 r = ex2b9 r := by
  revert r
  decide +kernel
lemma ex2b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 10 r = ex2b10 r := by
  revert r
  decide +kernel
lemma ex2b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 11 r = ex2b11 r := by
  revert r
  decide +kernel
lemma ex2b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 12 r = ex2b12 r := by
  revert r
  decide +kernel
lemma ex2b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 13 r = ex2b13 r := by
  revert r
  decide +kernel
lemma ex2b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 14 r = ex2b14 r := by
  revert r
  decide +kernel
lemma ex2b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 15 r = ex2b15 r := by
  revert r
  decide +kernel
lemma ex2b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 16 r = ex2b16 r := by
  revert r
  decide +kernel
lemma ex2b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 17 r = ex2b17 r := by
  revert r
  decide +kernel
lemma ex2b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 18 r = ex2b18 r := by
  revert r
  decide +kernel
lemma ex2b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 19 r = ex2b19 r := by
  revert r
  decide +kernel
lemma ex2b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 20 r = ex2b20 r := by
  revert r
  decide +kernel
lemma ex2b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 21 r = ex2b21 r := by
  revert r
  decide +kernel
lemma ex2b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 22 r = ex2b22 r := by
  revert r
  decide +kernel
lemma ex2b_mem (l : Fin 23) (r : Fin 8) : (ex2b l r).Mem (bernsteinRows 22 (exceptionalRow 2) l r) := by
  have he : bernsteinRowsBox 22 ex2r l r = ex2b l r := by
    fin_cases l
    · exact ex2b0_calc r
    · exact ex2b1_calc r
    · exact ex2b2_calc r
    · exact ex2b3_calc r
    · exact ex2b4_calc r
    · exact ex2b5_calc r
    · exact ex2b6_calc r
    · exact ex2b7_calc r
    · exact ex2b8_calc r
    · exact ex2b9_calc r
    · exact ex2b10_calc r
    · exact ex2b11_calc r
    · exact ex2b12_calc r
    · exact ex2b13_calc r
    · exact ex2b14_calc r
    · exact ex2b15_calc r
    · exact ex2b16_calc r
    · exact ex2b17_calc r
    · exact ex2b18_calc r
    · exact ex2b19_calc r
    · exact ex2b20_calc r
    · exact ex2b21_calc r
    · exact ex2b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex2r_mem l r
lemma ex2b_lower (d : Fin 23) : (24/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 2) d) := by
  have hc : ∀ d : Fin 23, (24:ℤ)*scale < 1000*(rowLowerBox (ex2b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex2b_mem d)).1
  have hnum : (24:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex2b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_2 (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (24/1000:ℝ) < exceptionalValue 2 e τ := by
  rw [←exceptionalRow_eval 2 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 2) _ ex2b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_ExceptionalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma frozenTaylor_affine (z : ℝ) (e : Fin 8 → ℝ) (v : ℝ) :
    frozenTaylor z e v=(1-z/Z)*frozenTaylor 0 e v+(z/Z)*frozenTaylor Z e v := by
  unfold frozenTaylor
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [←mul_assoc,Finset.mul_sum]
  rw [←add_mul,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  unfold frozenTaylorRow
  split_ifs <;> (try omega) <;> norm_num [Z] <;> ring
lemma frozenTaylor_actual (e : Fin 8 → ℝ) (he : e 1=1) (v : ℝ) :
    frozenTaylor (e 0) e v= -finiteTaylor 0 1 1 e v := by
  have heq : freezeParameter (e 0) e=e := by
    ext r
    unfold freezeParameter
    split_ifs with hr
    · rw [show r=0 from Fin.ext hr]
    · rfl
  rw [frozenTaylor_eq _ _ he,heq]
lemma exceptional_adjusted_nonneg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {v z : ℝ} (hv : v∈Icc 0 1) (hz : 0 ≤ z) (hzB : z ≤ Z) :
    0 ≤ Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*
      ((1-z/Z)*(frozenTaylor 0 e v-3/1000)+(z/Z)*(frozenTaylor Z e v-3/1000)) := by
  let A := frozenTaylor 0 e v
  let D := frozenTaylor Z e v
  let B0 := v^2
  let B1 := v^2+2*Z*v
  let B2 := v^2+4*Z*v+6*Z^2
  have h0 := exceptional_sign_0 e he hv
  have h1 := exceptional_sign_1 e he hv
  have h2 := exceptional_sign_2 e he hv
  have h3 := exceptional_sign_3_eu e he hv
  change 46/1000 < Q 1+v*A at h0
  change 56/1000 < Q 1*(v+Z)+(2*B1*A+B0*D)/3 at h1
  change 24/1000 < Q 1*(v+2*Z)+(B2*A+2*B1*D)/3 at h2
  change 27/1000 < Q 1*(v+3*Z)+B2*D at h3
  have hv2 : v^2 ≤ 1 := by nlinarith [hv.1,hv.2]
  have hB0 : B0 ≤ 7/2 := by dsimp[B0] <;> linarith
  have hB1 : B1 ≤ 7/2 := by dsimp[B1,Z] <;> nlinarith [hv.1,hv.2]
  have hB2 : B2 ≤ 7/2 := by dsimp[B2,Z] <;> nlinarith [hv.1,hv.2]
  let b0 := v*(Q 1+v*(A-3/1000))
  let b1 := Q 1*(v+Z)+(2*B1*(A-3/1000)+B0*(D-3/1000))/3
  let b2 := Q 1*(v+2*Z)+(B2*(A-3/1000)+2*B1*(D-3/1000))/3
  let b3 := Q 1*(v+3*Z)+B2*(D-3/1000)
  have hb0 : 0 ≤ b0 := by dsimp[b0]; apply mul_nonneg hv.1; nlinarith [hv.2]
  have hb1 : 0 ≤ b1 := by dsimp[b1] <;> nlinarith
  have hb2 : 0 ≤ b2 := by dsimp[b2] <;> nlinarith
  have hb3 : 0 ≤ b3 := by dsimp[b3] <;> nlinarith
  let t := z/Z
  have ht0 : 0 ≤ t := div_nonneg hz (by norm_num[Z])
  have ht1 : t ≤ 1 := (div_le_one (by norm_num[Z])).mpr hzB
  have hzt : z=t*Z := by dsimp[t]; rw [div_mul_cancel₀ _ (by norm_num[Z] : Z≠0)]
  have hid : Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*
      ((1-z/Z)*(A-3/1000)+(z/Z)*(D-3/1000)) =
      b0*(1-t)^3+3*b1*t*(1-t)^2+3*b2*t^2*(1-t)+b3*t^3 := by
    change Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*((1-t)*(A-3/1000)+t*(D-3/1000))=_
    rw[hzt]
    dsimp[b0,b1,b2,b3,B0,B1,B2]
    ring
  change 0 ≤ Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*((1-z/Z)*(A-3/1000)+(z/Z)*(D-3/1000))
  rw[hid]
  positivity
lemma exceptional_rational_comparison_eu_oai (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {v : ℝ} (hv : v∈Icc 0 1) (hz : 0<e 0) (hzB : e 0 ≤ Z) :
    finiteTaylor 0 1 1 e v+3/1000 ≤ Q 1*((3*(e 0)+v)/(6*(e 0)^2+4*(e 0)*v+v^2)) := by
  have hh := exceptional_adjusted_nonneg e he hv hz.le hzB
  have ha := frozenTaylor_affine (e 0) e v
  rw [frozenTaylor_actual e (polytope_one e he)] at ha
  have hv0 := hv.1
  have hd : 0<6*(e 0)^2+4*(e 0)*v+v^2 := by positivity
  rw [←mul_div_assoc,le_div_iff₀ hd]
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.exceptional_rational_comparison_eu_oai := @OAI.AtomicTriangular.Construction.exceptional_rational_comparison_eu_oai
