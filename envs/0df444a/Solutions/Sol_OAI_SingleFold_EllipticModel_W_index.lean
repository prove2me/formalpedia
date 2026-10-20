-- Prove2me | solution 1 for OAI.SingleFold.EllipticModel.W_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:28:52.640455+00:00
-- url     : https://prove2.me/submissions/ab8694ec-a393-4ff7-9e8e-06e7e8c46b2e

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticGrowth.lean:L88-L99
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.EllipticModel.W_index. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Theorems.Thm_OAI_SingleFold_DuplicationBound_height_dup_gt_five
import Theorems.Thm_OAI_SingleFold_DuplicationBound_height_dup_strict

-- ---- from OAI.NumberTheory.SingleFold.Duplication ----
namespace OAI

namespace SingleFold.DuplicationBound

lemma height_y_zero {x y : ℚ} (he : y^2=x^3-25*x) (hy : y = 0) : height x ≤ 5 := by
  have h : x*(x-5)*(x+5)=0 := by rw [hy] at he; linear_combination -he
  rcases mul_eq_zero.mp h with h|h
  · rcases mul_eq_zero.mp h with h|h
    · subst x; decide
    · have : x=5 := by linarith
      subst x; decide
  · have : x= -5 := by linarith
    subst x; decide

end SingleFold.DuplicationBound

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Torsion ----
namespace OAI

namespace SingleFold.Torsion
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma equation {x y : ℚ} (h : E.Nonsingular x y) : y^2=x^3-25*x := by
  simpa [WeierstrassCurve.Affine.equation_iff,sub_eq_add_neg] using h.1

lemma duplication {x y : ℚ} (h : E.Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : E.Nonsingular ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)),
      (2:ℕ) • some x y h = some ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)) h' := by
  have hy' : y ≠ E.negY x y := by simpa [WeierstrassCurve.Affine.negY] using (show y ≠ -y by intro hh; apply hy; linarith)
  have hs : E.slope x x y y = (3*x^2-25)/(2*y) := by
    rw [slope_of_Y_ne rfl hy']
    simp
    congr 1 <;> ring
  have hx' : E.addX x x (E.slope x x y y) = (x^2+25)^2/(4*y^2) := by
    rw [WeierstrassCurve.Affine.addX,hs]
    dsimp
    field_simp
    have he := equation h
    linear_combination -32*x*he
  rw [two_smul,add_self_of_Y_ne hy']
  have he := E.nonsingular_add h h (by simpa using hy')
  rw [hx'] at he
  exact ⟨he,by simp only [hx']⟩

open DuplicationBound

lemma double_nondegenerate (P : E.Point) (h : Nondegenerate P) :
    Nondegenerate ((2:ℕ) • P) ∧ H P < H ((2:ℕ) • P) := by
  obtain ⟨x,y,hp,hy,rfl⟩ := h
  obtain ⟨h',hh⟩ := duplication hp hy
  have he := equation hp
  have hx : (x^2+25)^2/(4*y^2) = dupX x := by
    dsimp [dupX]
    congr 1
    linear_combination 4*he
  rw [hh]
  have hu : E.addY x x y (E.slope x x y y) ≠ 0 := by
    intro hz
    have hb := height_y_zero (equation h') hz
    rw [hx] at hb
    exact (not_lt_of_ge hb) (height_dup_gt_five he hy)
  exact ⟨⟨_,_,h',hu,rfl⟩,by simpa only [H,hx] using height_dup_strict he hy⟩

lemma nondegenerate_nontorsion (P : E.Point) (h : Nondegenerate P) : ¬IsOfFinAddOrder P := by
  have hd (n : ℕ) : Nondegenerate ((2^n:ℕ) • P) := by
    induction n with
    | zero => simpa using h
    | succ n hn => simpa [pow_succ',mul_smul] using (double_nondegenerate _ hn).1
  have hmono : StrictMono (fun n : ℕ => H ((2^n:ℕ) • P)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simpa only [pow_succ',mul_smul] using (double_nondegenerate _ (hd n)).2
  have hi : Function.Injective (fun n : ℕ => (2^n:ℕ) • P) := by
    intro n m he
    exact hmono.injective (congrArg H he)
  intro ht
  have hf : (Set.range (fun n : ℕ => (2^n:ℕ) • P)).Finite :=
    ht.finite_multiples.subset (by rintro _ ⟨n,rfl⟩; exact ⟨2^n,rfl⟩)
  exact (Set.infinite_range_of_injective hi) hf

theorem torsion_doubled (P : E.Point) (h : IsOfFinAddOrder P) : (2:ℕ) • P = 0 := by
  cases P with
  | zero => simp only [←zero_def,nsmul_zero]
  | some x y hp =>
    have hy : y=0 := by
      by_contra hn
      exact nondegenerate_nontorsion _ ⟨x,y,hp,hn,rfl⟩ h
    rw [two_smul,add_self_of_Y_eq (by simp [WeierstrassCurve.Affine.negY,hy])]

theorem torsion_iff (P : E.Point) : IsOfFinAddOrder P ↔ (2:ℕ) • P = 0 := by
  refine ⟨torsion_doubled P,fun h => ?_⟩
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2,by norm_num,h⟩

end SingleFold.Torsion

end OAI

-- ---- from OAI.NumberTheory.SingleFold.EllipticGrowth ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.EllipticModel
open WeierstrassCurve.Affine.Point
lemma Hx_neg (Q : E.Point) : Hx (-Q)=Hx Q := by
  cases Q with
  | zero => rfl
  | some x y h => rfl

variable {T : Type} [AddCommGroup T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
lemma point_add (n m : ℤ) (t s : T) : point f (n+m) (t+s)=point f n t+point f m s := by
  apply f.injective
  simp [point]
  rfl
lemma point_zero : point f 0 0=0 := by
  apply f.injective
  simp [point]
  rfl
lemma point_int (n : ℤ) : point f n 0=n • P f := by
  apply f.injective
  simp [point,P]
  funext i; simp
lemma point_split (n : ℤ) (t : T) : point f n t=n • P f+point f 0 t := by
  rw [←point_int,←point_add,add_zero,zero_add]
lemma point_nsmul (n : ℤ) (t : T) (m : ℕ) : m • point f n t=point f (m*n) (m • t) := by
  apply f.injective
  simp [point]
  rfl
lemma point_torsion [Finite T] (t : T) : IsOfFinAddOrder (point f 0 t) := by
  have h := isOfFinAddOrder_of_finite t
  obtain ⟨n,hn,hnt⟩ := h.exists_nsmul_eq_zero
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n,hn,?_⟩
  rw [point_nsmul,hnt,mul_zero,point_zero]
lemma double_torsion [Finite T] (t : T) : (2:ℕ) • point f 0 t=0 :=
  (Torsion.torsion_iff _).mp (point_torsion f t)
lemma normal_form (Q : E.Point) : Q=point f (index f Q) (f Q).2 := by
  apply f.injective
  simp only [point,AddEquiv.apply_symm_apply,index]
  apply Prod.ext
  · funext i
    exact congrArg (fun j => (f Q).1 j) (Subsingleton.elim _ _)
  · rfl

lemma W_neg (m : ℕ) (Q : E.Point) : W m (-Q)=W m Q := by
  change Hx (m • (-Q))=Hx (m • Q)
  rw [show m • (-Q)= -(m • Q) from (nsmulAddMonoidHom (α:=E.Point) m).map_neg Q,Hx_neg]
lemma W_point [Finite T] (m : ℕ) (hm : Even m) (n : ℤ) (t : T) : W m (point f n t)=W m (n • P f) := by
  obtain ⟨d,hd⟩ := hm
  have ht : m • point f 0 t=0 := by
    rw [hd,show d+d=2*d by omega,mul_comm,mul_smul,double_torsion,nsmul_zero]
  rw [point_split,W,nsmul_add,ht,add_zero]
  rfl
lemma W_index [Finite T] (m : ℕ) (hm : Even m) (Q : E.Point) : W m Q=sequence f m (index f Q).natAbs := by
  calc
    W m Q = W m ((index f Q) • P f) := by
      conv_lhs => rw [normal_form f Q]
      exact W_point f m hm _ _
    _ = sequence f m (index f Q).natAbs := by
      by_cases h : 0 ≤ index f Q
      · have hn : ((index f Q).natAbs:ℤ)=index f Q := by rw [Int.natCast_natAbs,abs_of_nonneg h]
        rw [sequence,←natCast_zsmul,hn]
      · have hn : index f Q= -((index f Q).natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge h),neg_neg]
        conv_lhs => rw [hn,neg_smul,W_neg,natCast_zsmul]
        rfl
end SingleFold.EllipticModel

namespace SingleFold.GrowthCompilation
open Compiler PointCompiler
section
variable {T α : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
variable {Q R : (α → ℕ) → E.Point}
end

section
variable {T : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
end

end SingleFold.GrowthCompilation

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.EllipticModel
open WeierstrassCurve.Affine.Point


theorem solution : type_of% @_root_.OAI.SingleFold.EllipticModel.W_index := @_root_.OAI.SingleFold.EllipticModel.W_index
