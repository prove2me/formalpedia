-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.addEq_encode
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:59:27.940989+00:00
-- url     : https://prove2.me/submissions/e3a2b1e5-1f8e-4e9b-acf0-954660acf587

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean:L157-L196
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.addEq_encode. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Theorems.Thm_OAI_SingleFold_PointCompiler_line_iff

-- ---- from OAI.NumberTheory.SingleFold.EllipticCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PointCompiler

section
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma encode_toPoint (P : E.Point) : (encode P).toPoint (encode_valid P)=P := by
  cases P with
  | zero => simp [Code.toPoint,encode,←zero_def]
  | some x y h => simp [Code.toPoint,encode,RationalCode.encode_value]
lemma line_chord {x₁ x₂ y₁ y₂ x₃ y₃ : ℚ}
    (h₁ : E.Nonsingular x₁ y₁) (h₂ : E.Nonsingular x₂ y₂) (h₃ : E.Nonsingular x₃ y₃)
    (hx : x₁≠x₂) :
    Line (x₁-x₂) (y₁-y₂) x₁ x₂ y₁ x₃ y₃ ↔ some x₁ y₁ h₁+some x₂ y₂ h₂=some x₃ y₃ h₃ := by
  rw [line_iff (sub_ne_zero.mpr hx),add_of_X_ne hx,some.injEq,slope_of_X_ne hx,E_addX,E_addY]
  constructor
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [←hx]; exact hy.symm⟩
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [hx] at hy; exact hy.symm⟩
lemma line_tangent {x y x₃ y₃ : ℚ}
    (h : E.Nonsingular x y) (h₃ : E.Nonsingular x₃ y₃) (hy : y≠0) :
    Line (2*y) (3*x^2-25) x x y x₃ y₃ ↔ some x y h+some x y h=some x₃ y₃ h₃ := by
  have hyn : y≠E.negY x y := by rw [E_negY]; intro he; apply hy; linarith
  have hs : E.slope x x y y=(3*x^2-25)/(2*y) := by
    rw [slope_of_Y_ne rfl hyn,E_negY]
    simp only [E]
    congr 1 <;> ring
  rw [line_iff (mul_ne_zero (by norm_num) hy),add_self_of_Y_ne hyn,some.injEq,hs,E_addX,E_addY]
  constructor
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [←hx]; exact hy.symm⟩
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [hx] at hy; exact hy.symm⟩

lemma encode_injective : Function.Injective encode := by
  intro p q he
  have he' : (⟨encode p,encode_valid p⟩ : {c : Code // c.Valid})=⟨encode q,encode_valid q⟩ := Subtype.ext he
  have hh := congrArg (fun c : {c : Code // c.Valid} => c.1.toPoint c.2) he'
  simpa only [encode_toPoint] using hh

lemma addEq_encode (P Q R : E.Point) : AddEq (encode P) (encode Q) (encode R) ↔ P+Q=R := by
  cases P with
  | zero =>
    simp only [AddEq,encode,one_ne_zero,false_and,true_and,or_false]
    change (encode R=encode Q) ↔ (0:E.Point)+Q=R
    simp only [zero_add,encode_injective.eq_iff,eq_comm]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      simp only [AddEq,encode,zero_ne_one,false_and,true_and,false_or,one_ne_zero]
      change (encode R=encode (some x₁ y₁ h₁)) ∨ False ↔ some x₁ y₁ h₁+(0:E.Point)=R
      simp only [or_false,add_zero,encode_injective.eq_iff,eq_comm]
    | some x₂ y₂ h₂ =>
      have hv := (equation_iff _ _).mp h₁
      have hw := (equation_iff _ _).mp h₂
      by_cases hx : x₁=x₂
      · subst x₂
        by_cases hy : y₁+y₂=0
        · have he : y₁=E.negY x₁ y₂ := by rw [E_negY]; linarith
          rw [add_of_Y_eq rfl he]
          cases R <;> simp [AddEq,encode,RationalCode.encode_value,hy,←zero_def]
        · have hy' : y₁=y₂ := by
            rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hv.trans hw.symm) with hh|hh
            · exact hh
            · exact False.elim (hy (by linarith))
          subst y₂
          have hyn : y₁≠0 := by intro he; simp [he] at hy
          cases R with
          | zero =>
            have hn : y₁≠E.negY x₁ y₁ := by rw [E_negY]; intro he; apply hyn; linarith
            rw [add_self_of_Y_ne hn]
            simp [AddEq,encode,RationalCode.encode_value,hy,←zero_def]
          | some x₃ y₃ h₃ =>
            simpa [AddEq,encode,RationalCode.encode_value,hy] using line_tangent h₁ h₃ hyn
      · cases R with
        | zero =>
          rw [add_of_X_ne hx]
          simp [AddEq,encode,RationalCode.encode_value,hx,←zero_def]
        | some x₃ y₃ h₃ =>
          simpa [AddEq,encode,RationalCode.encode_value,hx] using line_chord h₁ h₂ h₃ hx

variable {ι : Type} [Finite ι]
end

open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

variable {α : Type}
end SingleFold.PointCompiler

namespace SingleFold.Compiler.Semi
variable {α : Type}
end SingleFold.Compiler.Semi

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

end SingleFold.PointCompiler

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.addEq_encode := @_root_.OAI.SingleFold.PointCompiler.addEq_encode
