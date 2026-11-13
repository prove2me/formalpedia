-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_0_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:30:06.953844+00:00
-- url     : https://prove2.me/submissions/4a355558-c664-4217-b666-20f0fa7a02fb

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Definitions.Def_OAIQ257X022
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_4_0_mem_x

section
-- module Solutions.OAIQ250_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_Bernstein
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
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

lemma RI.mem_invPos {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo) :
    a.invPos.Mem x⁻¹ := by
  have halo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hsx : 0 < (scale:ℝ)*x := halo.trans_le hx.1
  have hahi : (0:ℝ) < a.hi := hsx.trans_le hx.2
  have hahi' : (0:ℤ) < a.hi := by exact_mod_cast hahi
  have hl := (div_floor_bounds (scale^2) a.hi hahi').1
  have hu := (div_floor_bounds (scale^2) a.lo ha).2
  push_cast at hl hu
  have hlow : (((scale^2/a.hi:ℤ):ℝ)) ≤ (scale:ℝ)^2/((scale:ℝ)*x) := by
    exact ((le_div_iff₀ hahi).mpr hl).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hsx hx.2)
  have hupp : (scale:ℝ)^2/((scale:ℝ)*x) ≤ (((scale^2/a.lo+1:ℤ):ℝ)) := by
    exact (div_le_div_of_nonneg_left (sq_nonneg _) halo hx.1).trans
      ((div_le_iff₀ halo).mpr (by simpa only [Int.cast_add,Int.cast_one] using hu))
  have heq : (scale:ℝ)^2/((scale:ℝ)*x) = (scale:ℝ)*x⁻¹ := by
    field_simp [ne_of_gt scale_pos]
  simpa only [heq,RI.Mem,RI.invPos] using And.intro hlow hupp

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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Polytope
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_PolytopeInterval
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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRowsBase
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
-- module Solutions.OAIQ250_TR.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma ordinarySignValue_eq (side : Fin 2) (n : Fin 7) (y : Fin 2) (e : Fin 8 → ℝ) (τ : ℝ) :
    ordinarySignValue side n y e τ =
      ∑ l : Fin 21, (∑ r : Fin 8, ordinarySignRow side n y l r*e r)*τ^l.val := by
  have ht : (∑ l : Fin 21, (∑ r : Fin 8,
      taylorRow side (nearNode n) (nearDisplacement n y) l.val r*e r)*τ^l.val) =
      finiteTaylor side (nearNode n) (nearDisplacement n y) e τ := by
    rw [finiteTaylor,← Fin.sum_univ_eq_sum_range]
  unfold ordinarySignValue ordinarySignRow
  split_ifs with h
  · simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul,
      Finset.sum_ite_irrel,ht,Finset.sum_const_zero]
    congr 1
    symm
    rw [Finset.sum_eq_single (0:Fin 21)]
    · simp
    · intro b hb hb0
      have hne : b.val ≠ 0 := by intro hh; apply hb0; exact Fin.ext hh
      simp [hne]
    · simp
  · exact ht.symm
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ordinaryOffsetBox_mem (n : Fin 7) (r : Fin 8) :
    (ordinaryOffsetBox n r).Mem (ordinaryOffset n r) := by
  unfold ordinaryOffsetBox ordinaryOffset
  split_ifs
  · rw [div_eq_mul_inv]
    exact RI.mem_mul QBox1_mem (RI.mem_invPos (RI.mem_mul (RI.mem_point 2) ZBox_mem) (by decide +kernel))
  · exact RI.mem_mul (RI.mem_divNat (RI.mem_point 4) (by norm_num)) QBox1_mem
  · simpa using RI.mem_point 0

lemma ordinarySignRowBox_mem (side : Fin 2) (n : Fin 7) (y : Fin 2)
    {a : Fin 21 → Fin 8 → RI}
    (ha : ∀ l r, (a l r).Mem (taylorRow side (nearNode n) (nearDisplacement n y) l.val r))
    (l : Fin 21) (r : Fin 8) :
    (ordinarySignRowBox side n a l r).Mem (ordinarySignRow side n y l r) := by
  unfold ordinarySignRowBox ordinarySignRow
  split_ifs
  · exact RI.mem_sub (ordinaryOffsetBox_mem n r) (ha l r)
  · exact RI.mem_sub (by simpa using RI.mem_point 0) (ha l r)
  · exact ha l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_4_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 0 r = bs1_4_0_0 r := by
  revert r
  decide +kernel
lemma bs1_4_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 1 r = bs1_4_0_1 r := by
  revert r
  decide +kernel
lemma bs1_4_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 2 r = bs1_4_0_2 r := by
  revert r
  decide +kernel
lemma bs1_4_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 3 r = bs1_4_0_3 r := by
  revert r
  decide +kernel
lemma bs1_4_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 4 r = bs1_4_0_4 r := by
  revert r
  decide +kernel
lemma bs1_4_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 5 r = bs1_4_0_5 r := by
  revert r
  decide +kernel
lemma bs1_4_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 6 r = bs1_4_0_6 r := by
  revert r
  decide +kernel
lemma bs1_4_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 7 r = bs1_4_0_7 r := by
  revert r
  decide +kernel
lemma bs1_4_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 8 r = bs1_4_0_8 r := by
  revert r
  decide +kernel
lemma bs1_4_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 9 r = bs1_4_0_9 r := by
  revert r
  decide +kernel
lemma bs1_4_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 10 r = bs1_4_0_10 r := by
  revert r
  decide +kernel
lemma bs1_4_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 11 r = bs1_4_0_11 r := by
  revert r
  decide +kernel
lemma bs1_4_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 12 r = bs1_4_0_12 r := by
  revert r
  decide +kernel
lemma bs1_4_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 13 r = bs1_4_0_13 r := by
  revert r
  decide +kernel
lemma bs1_4_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 14 r = bs1_4_0_14 r := by
  revert r
  decide +kernel
lemma bs1_4_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 15 r = bs1_4_0_15 r := by
  revert r
  decide +kernel
lemma bs1_4_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 16 r = bs1_4_0_16 r := by
  revert r
  decide +kernel
lemma bs1_4_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 17 r = bs1_4_0_17 r := by
  revert r
  decide +kernel
lemma bs1_4_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 18 r = bs1_4_0_18 r := by
  revert r
  decide +kernel
lemma bs1_4_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 19 r = bs1_4_0_19 r := by
  revert r
  decide +kernel
lemma bs1_4_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 20 r = bs1_4_0_20 r := by
  revert r
  decide +kernel
lemma bs1_4_0_mem (d : Fin 21) (r : Fin 8) : (bs1_4_0 d r).Mem (bernsteinRows 20 (ordinarySignRow 1 4 0) d r) := by
  have he : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) d r = bs1_4_0 d r := by
    fin_cases d
    · exact bs1_4_0_0_calc r
    · exact bs1_4_0_1_calc r
    · exact bs1_4_0_2_calc r
    · exact bs1_4_0_3_calc r
    · exact bs1_4_0_4_calc r
    · exact bs1_4_0_5_calc r
    · exact bs1_4_0_6_calc r
    · exact bs1_4_0_7_calc r
    · exact bs1_4_0_8_calc r
    · exact bs1_4_0_9_calc r
    · exact bs1_4_0_10_calc r
    · exact bs1_4_0_11_calc r
    · exact bs1_4_0_12_calc r
    · exact bs1_4_0_13_calc r
    · exact bs1_4_0_14_calc r
    · exact bs1_4_0_15_calc r
    · exact bs1_4_0_16_calc r
    · exact bs1_4_0_17_calc r
    · exact bs1_4_0_18_calc r
    · exact bs1_4_0_19_calc r
    · exact bs1_4_0_20_calc r
  rw [← he]
  exact bernsteinRowsBox_mem 20 (ordinarySignRowBox_mem 1 4 0 tr1_4_0_mem_x) d r
lemma bs1_4_0_lower (d : Fin 21) : (3900/1000000:ℝ) < rowLower (bernsteinRows 20 (ordinarySignRow 1 4 0) d) := by
  have hc : ∀ d : Fin 21, (3900:ℤ)*scale < 1000000*(rowLowerBox (bs1_4_0 d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (bs1_4_0_mem d)).1
  have hnum : (3900:ℝ)*(scale:ℝ) < 1000000*((rowLowerBox (bs1_4_0 d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma ordinary_sign_1_4_0_x_oai (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (3900/1000000:ℝ) < ordinarySignValue 1 4 0 e τ := by
  rw [ordinarySignValue_eq]
  exact polytope_polynomial_lower 20 (ordinarySignRow 1 4 0) _ bs1_4_0_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_0_x_oai := @OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_0_x_oai
