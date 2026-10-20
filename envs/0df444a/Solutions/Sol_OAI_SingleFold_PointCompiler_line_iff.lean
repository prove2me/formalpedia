-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.line_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:57:51.044881+00:00
-- url     : https://prove2.me/submissions/89c1df30-3177-4e4d-b3bc-fec4ae9613d9

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean:L102-L115
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.line_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates

-- ---- from OAI.NumberTheory.SingleFold.EllipticCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PointCompiler

section
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma line_iff {d n x₁ x₂ y₁ x₃ y₃ : ℚ} (hd : d≠0) :
    Line d n x₁ x₂ y₁ x₃ y₃ ↔
      x₃=(n/d)^2-x₁-x₂ ∧ y₃=n/d*(x₁-x₃)-y₁ := by
  unfold Line
  constructor
  · rintro ⟨hx,hy⟩
    constructor
    · field_simp
      nlinarith only [hx]
    · field_simp
      nlinarith only [hy]
  · rintro ⟨hx,hy⟩
    field_simp at hx hy
    constructor <;> nlinarith only [hx,hy]

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


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.line_iff := @_root_.OAI.SingleFold.PointCompiler.line_iff
