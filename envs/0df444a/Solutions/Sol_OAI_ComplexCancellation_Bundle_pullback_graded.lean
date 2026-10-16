-- Prove2me | solution 1 for OAI.ComplexCancellation.Bundle.pullback_graded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:28:31.53681+00:00
-- url     : https://prove2.me/submissions/939d84f6-a9e2-4ab1-a8e3-56bf7d156077

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/BundleGrading.lean:L33-L52
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Bundle.pullback_graded. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler
import Definitions.Def_OAI_Algebra_AffineCancellation_Intertwining
import Theorems.Thm_OAI_ComplexCancellation_GradedMap_mvpolynomial

-- ---- from OAI.Algebra.AffineCancellation.ModificationGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma coefficient_mem (r : R) : algebraMap R (T R v) r ∈ pieces R v 0 :=
  ⟨C r,isWeightedHomogeneous_C _ _,(π R v).commutes r⟩
lemma τ_mem : τ R v ∈ pieces R v (-1) := ⟨X 0,isWeightedHomogeneous_X R weight 0,rfl⟩
lemma V_mem : V R v ∈ pieces R v 2 := ⟨X 1,isWeightedHomogeneous_X R weight 1,rfl⟩
end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.BundleGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Bundle
open Determinant
lemma j_mem (r : T) : j r ∈ valuationPieces 0 := AffineModification.coefficient_mem T v r
lemma τ_mem : τ ∈ valuationPieces (-1) := AffineModification.τ_mem T v
lemma V_mem : V ∈ valuationPieces 2 := AffineModification.V_mem T v
lemma pullback_graded (i : ℤ) (r : Degeneration.G) (hr : r ∈ Degeneration.pieces i) :
    pullback r ∈ valuationPieces i := by
  obtain ⟨p,hp,rfl⟩ := hr
  change pullback (Degeneration.π p) ∈ valuationPieces i
  rw [pullback_π]
  apply GradedMap.mvpolynomial valuationPieces Degeneration.weight eval _ hp
  intro z
  fin_cases z
  · change eval (MvPolynomial.X 0) ∈ valuationPieces (-1)
    simpa only [eval,MvPolynomial.aeval_X,values,Matrix.cons_val_zero] using τ_mem
  · change eval (MvPolynomial.X 1) ∈ valuationPieces 0
    simpa only [eval,MvPolynomial.aeval_X,values,Matrix.cons_val_one,Matrix.cons_val_zero] using j_mem (inclusion Quadric.s)
  · change eval (MvPolynomial.X 2) ∈ valuationPieces 0
    simpa only [eval,MvPolynomial.aeval_X,values,Matrix.cons_val] using j_mem Determinant.u
  · change eval (MvPolynomial.X 3) ∈ valuationPieces 2
    have h := SetLike.mul_mem_graded (j_mem C₁) V_mem
    simpa only [zero_add,eval,MvPolynomial.aeval_X,values,Matrix.cons_val] using h
  · change eval (MvPolynomial.X 4) ∈ valuationPieces 2
    have h := SetLike.mul_mem_graded (j_mem (b^2)) V_mem
    simpa only [zero_add,eval,MvPolynomial.aeval_X,values,Matrix.cons_val] using h
end ComplexCancellation.Bundle

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Bundle
open Determinant


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Bundle.pullback_graded := @_root_.OAI.ComplexCancellation.Bundle.pullback_graded
