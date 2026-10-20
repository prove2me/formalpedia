-- Prove2me | solution 1 for OAI.SingleFold.CurveRank.representatives_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:11:56.452461+00:00
-- url     : https://prove2.me/submissions/83e1f4fd-0791-4f02-93e9-765441e398cb

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/FiniteGeneration.lean:L78-L90
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.CurveRank.representatives_card. The node keeps its source
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

-- ---- from OAI.NumberTheory.SingleFold.FiniteGeneration ----
namespace OAI

namespace SingleFold.HeightDescent

universe u

variable {A : Type u} [AddCommGroup A]

end SingleFold.HeightDescent

namespace SingleFold.CurveRank
open Descent

lemma representatives_card : representatives.card ≤ 8 := by
  classical
  have hu := Finset.card_union_le ({0,T0,T5,T0+T5} : Finset E.Point)
    (({0,T0,T5,T0+T5} : Finset E.Point).image (· + G))
  have hi := Finset.card_image_le (s := ({0,T0,T5,T0+T5} : Finset E.Point)) (f := (· + G))
  have hc : ({0,T0,T5,T0+T5} : Finset E.Point).card ≤ 4 := by
    exact (Finset.card_insert_le ..).trans (by
      have h1 := Finset.card_insert_le T0 ({T5,T0+T5} : Finset E.Point)
      have h2 := Finset.card_insert_le T5 ({T0+T5} : Finset E.Point)
      simp only [Finset.card_singleton] at h2
      omega)
  unfold representatives
  omega

end SingleFold.CurveRank

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.CurveRank
open Descent


theorem solution : type_of% @_root_.OAI.SingleFold.CurveRank.representatives_card := @_root_.OAI.SingleFold.CurveRank.representatives_card
