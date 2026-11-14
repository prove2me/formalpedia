-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.exceptional_sign_3_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:27:41.76622+00:00
-- url     : https://prove2.me/submissions/e392cc49-2c9a-430b-af9a-cb52ff3323e0

import Mathlib
import Definitions.Def_OAIQ334E021
import Definitions.Def_OAIQ334E023
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
-- module Solutions.OAIQ334_EU.Triangular_Signs_ExceptionalSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex3r0_calc (r : Fin 8) : exceptionalRowBox 3 0 r = ex3r0 r := by
  revert r
  decide +kernel
lemma ex3r1_calc (r : Fin 8) : exceptionalRowBox 3 1 r = ex3r1 r := by
  revert r
  decide +kernel
lemma ex3r2_calc (r : Fin 8) : exceptionalRowBox 3 2 r = ex3r2 r := by
  revert r
  decide +kernel
lemma ex3r3_calc (r : Fin 8) : exceptionalRowBox 3 3 r = ex3r3 r := by
  revert r
  decide +kernel
lemma ex3r4_calc (r : Fin 8) : exceptionalRowBox 3 4 r = ex3r4 r := by
  revert r
  decide +kernel
lemma ex3r5_calc (r : Fin 8) : exceptionalRowBox 3 5 r = ex3r5 r := by
  revert r
  decide +kernel
lemma ex3r6_calc (r : Fin 8) : exceptionalRowBox 3 6 r = ex3r6 r := by
  revert r
  decide +kernel
lemma ex3r7_calc (r : Fin 8) : exceptionalRowBox 3 7 r = ex3r7 r := by
  revert r
  decide +kernel
lemma ex3r8_calc (r : Fin 8) : exceptionalRowBox 3 8 r = ex3r8 r := by
  revert r
  decide +kernel
lemma ex3r9_calc (r : Fin 8) : exceptionalRowBox 3 9 r = ex3r9 r := by
  revert r
  decide +kernel
lemma ex3r10_calc (r : Fin 8) : exceptionalRowBox 3 10 r = ex3r10 r := by
  revert r
  decide +kernel
lemma ex3r11_calc (r : Fin 8) : exceptionalRowBox 3 11 r = ex3r11 r := by
  revert r
  decide +kernel
lemma ex3r12_calc (r : Fin 8) : exceptionalRowBox 3 12 r = ex3r12 r := by
  revert r
  decide +kernel
lemma ex3r13_calc (r : Fin 8) : exceptionalRowBox 3 13 r = ex3r13 r := by
  revert r
  decide +kernel
lemma ex3r14_calc (r : Fin 8) : exceptionalRowBox 3 14 r = ex3r14 r := by
  revert r
  decide +kernel
lemma ex3r15_calc (r : Fin 8) : exceptionalRowBox 3 15 r = ex3r15 r := by
  revert r
  decide +kernel
lemma ex3r16_calc (r : Fin 8) : exceptionalRowBox 3 16 r = ex3r16 r := by
  revert r
  decide +kernel
lemma ex3r17_calc (r : Fin 8) : exceptionalRowBox 3 17 r = ex3r17 r := by
  revert r
  decide +kernel
lemma ex3r18_calc (r : Fin 8) : exceptionalRowBox 3 18 r = ex3r18 r := by
  revert r
  decide +kernel
lemma ex3r19_calc (r : Fin 8) : exceptionalRowBox 3 19 r = ex3r19 r := by
  revert r
  decide +kernel
lemma ex3r20_calc (r : Fin 8) : exceptionalRowBox 3 20 r = ex3r20 r := by
  revert r
  decide +kernel
lemma ex3r21_calc (r : Fin 8) : exceptionalRowBox 3 21 r = ex3r21 r := by
  revert r
  decide +kernel
lemma ex3r22_calc (r : Fin 8) : exceptionalRowBox 3 22 r = ex3r22 r := by
  revert r
  decide +kernel
lemma ex3r_mem (l : Fin 23) (r : Fin 8) : (ex3r l r).Mem (exceptionalRow 3 l r) := by
  have he : exceptionalRowBox 3 l r = ex3r l r := by
    fin_cases l
    · exact ex3r0_calc r
    · exact ex3r1_calc r
    · exact ex3r2_calc r
    · exact ex3r3_calc r
    · exact ex3r4_calc r
    · exact ex3r5_calc r
    · exact ex3r6_calc r
    · exact ex3r7_calc r
    · exact ex3r8_calc r
    · exact ex3r9_calc r
    · exact ex3r10_calc r
    · exact ex3r11_calc r
    · exact ex3r12_calc r
    · exact ex3r13_calc r
    · exact ex3r14_calc r
    · exact ex3r15_calc r
    · exact ex3r16_calc r
    · exact ex3r17_calc r
    · exact ex3r18_calc r
    · exact ex3r19_calc r
    · exact ex3r20_calc r
    · exact ex3r21_calc r
    · exact ex3r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 3 l r
lemma ex3b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 0 r = ex3b0 r := by
  revert r
  decide +kernel
lemma ex3b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 1 r = ex3b1 r := by
  revert r
  decide +kernel
lemma ex3b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 2 r = ex3b2 r := by
  revert r
  decide +kernel
lemma ex3b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 3 r = ex3b3 r := by
  revert r
  decide +kernel
lemma ex3b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 4 r = ex3b4 r := by
  revert r
  decide +kernel
lemma ex3b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 5 r = ex3b5 r := by
  revert r
  decide +kernel
lemma ex3b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 6 r = ex3b6 r := by
  revert r
  decide +kernel
lemma ex3b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 7 r = ex3b7 r := by
  revert r
  decide +kernel
lemma ex3b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 8 r = ex3b8 r := by
  revert r
  decide +kernel
lemma ex3b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 9 r = ex3b9 r := by
  revert r
  decide +kernel
lemma ex3b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 10 r = ex3b10 r := by
  revert r
  decide +kernel
lemma ex3b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 11 r = ex3b11 r := by
  revert r
  decide +kernel
lemma ex3b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 12 r = ex3b12 r := by
  revert r
  decide +kernel
lemma ex3b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 13 r = ex3b13 r := by
  revert r
  decide +kernel
lemma ex3b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 14 r = ex3b14 r := by
  revert r
  decide +kernel
lemma ex3b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 15 r = ex3b15 r := by
  revert r
  decide +kernel
lemma ex3b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 16 r = ex3b16 r := by
  revert r
  decide +kernel
lemma ex3b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 17 r = ex3b17 r := by
  revert r
  decide +kernel
lemma ex3b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 18 r = ex3b18 r := by
  revert r
  decide +kernel
lemma ex3b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 19 r = ex3b19 r := by
  revert r
  decide +kernel
lemma ex3b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 20 r = ex3b20 r := by
  revert r
  decide +kernel
lemma ex3b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 21 r = ex3b21 r := by
  revert r
  decide +kernel
lemma ex3b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 22 r = ex3b22 r := by
  revert r
  decide +kernel
lemma ex3b_mem (l : Fin 23) (r : Fin 8) : (ex3b l r).Mem (bernsteinRows 22 (exceptionalRow 3) l r) := by
  have he : bernsteinRowsBox 22 ex3r l r = ex3b l r := by
    fin_cases l
    · exact ex3b0_calc r
    · exact ex3b1_calc r
    · exact ex3b2_calc r
    · exact ex3b3_calc r
    · exact ex3b4_calc r
    · exact ex3b5_calc r
    · exact ex3b6_calc r
    · exact ex3b7_calc r
    · exact ex3b8_calc r
    · exact ex3b9_calc r
    · exact ex3b10_calc r
    · exact ex3b11_calc r
    · exact ex3b12_calc r
    · exact ex3b13_calc r
    · exact ex3b14_calc r
    · exact ex3b15_calc r
    · exact ex3b16_calc r
    · exact ex3b17_calc r
    · exact ex3b18_calc r
    · exact ex3b19_calc r
    · exact ex3b20_calc r
    · exact ex3b21_calc r
    · exact ex3b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex3r_mem l r
lemma ex3b_lower (d : Fin 23) : (27/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 3) d) := by
  have hc : ∀ d : Fin 23, (27:ℤ)*scale < 1000*(rowLowerBox (ex3b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex3b_mem d)).1
  have hnum : (27:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex3b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_3_eu_oai (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (27/1000:ℝ) < exceptionalValue 3 e τ := by
  rw [←exceptionalRow_eval 3 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 3) _ ex3b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.exceptional_sign_3_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.exceptional_sign_3_eu_oai
