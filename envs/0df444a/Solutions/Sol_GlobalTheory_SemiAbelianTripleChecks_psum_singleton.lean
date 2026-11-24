-- Prove2me | solution 1 for GlobalTheory.SemiAbelianTripleChecks.psum_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:42:48.236706+00:00
-- url     : https://prove2.me/submissions/cc0b1172-6993-4996-b4d0-927ae19ba730

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_CubeMapTripleProductUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SemiAbelianTripleChecks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
namespace GlobalTheory.SemiAbelianTripleChecks
theorem _root_.solution (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (x : Fin 3 → (T ⟶ G)) (i : Fin 3) :
    psum G x {i} = x i := by
  have h : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by
    fin_cases i <;> decide
  unfold psum
  rw [h]
  have : padd G (x i) (pzero G T) = x i * 1 := rfl
  simp only [List.foldr_cons, List.foldr_nil]
  rw [this, _root_.mul_one]
end GlobalTheory.SemiAbelianTripleChecks
