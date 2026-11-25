-- Prove2me | solution 1 for IntersectionBounds.separator_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:54:16.770505+00:00
-- url     : https://prove2.me/submissions/aa4f10d6-5fcf-4081-93a0-807ba321f16b

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Theorems.Thm_IntersectionBounds_separator_self
public import Theorems.Thm_IntersectionBounds_separator_off_diagonal
public import Theorems.Thm_IntersectionBounds_indicator_empty
attribute [local simp] IntersectionBounds.indicator_empty



set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V)) (L : Finset K)
open Classical
namespace IntersectionBounds
theorem _root_.solution
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    LinearIndependent K (fun A : F => separator F L A.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc A
  have h := congrFun hc A
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have hz (B : F) (hBA : B ≠ A) : separator F L B.val A = 0 :=
    separator_off_diagonal F L B A
      (hinter B.val B.property A.val A.property (fun heq => hBA (Subtype.ext heq)))
  rw [Finset.sum_eq_single A (fun B _ hBA => by rw [hz B hBA, mul_zero]) (by simp)] at h
  have hdiag : separator F L A.val A ≠ 0 := by
    rw [separator_self]
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    apply sub_ne_zero.mpr
    intro heq
    exact hself A.val A.property (heq ▸ hl)
  exact (mul_eq_zero.mp h).resolve_right hdiag
end IntersectionBounds
