-- Prove2me | solution 1 for OAI.ComplexCancellation.Bundle.fiberEuler_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:25:29.441014+00:00
-- url     : https://prove2.me/submissions/5c65c363-8b15-4e8e-b153-92e0c75a3d35

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/BundleGrading.lean:L16-L32
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Bundle.fiberEuler_homogeneous. The node keeps its source
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
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_derivation_zero_of_generators

-- ---- from OAI.Algebra.AffineCancellation.GradedLND ----
namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
open DirectSum
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]

lemma proj_mem (i : ℤ) (r : R) : proj G i r ∈ G i :=
  (decompose G r i).property

lemma proj_of_mem {r : R} {i : ℤ} (hr : r ∈ G i) : proj G i r = r :=
  decompose_of_mem_same G hr

lemma component_of_mem (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r = proj G (i+j) (D r) :=
  componentLinear_of_mem G D.toLinearMap j hr

lemma component_homogeneous (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r ∈ G (i+j) := by
  rw [component_of_mem G D j hr]
  exact proj_mem G _ _

end ComplexCancellation.GradedLND

end

end OAI

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
lemma fiberEuler_j (r : T) : fiberEuler (j r)=j (Euler r) := AffineModification.euler_coefficient _ _ _ r
lemma fiberEuler_τ : fiberEuler τ=0 := AffineModification.euler_τ _ _ _
lemma fiberEuler_V : fiberEuler V=2*V := AffineModification.euler_V _ _ _
lemma j_mem (r : T) : j r ∈ valuationPieces 0 := AffineModification.coefficient_mem T v r
lemma τ_mem : τ ∈ valuationPieces (-1) := AffineModification.τ_mem T v
lemma V_mem : V ∈ valuationPieces 2 := AffineModification.V_mem T v
lemma fiberEuler_homogeneous (i : ℤ) (r : B) (hr : r ∈ valuationPieces i) :
    fiberEuler r ∈ valuationPieces i := by
  have he : fiberEuler=GradedLND.component valuationPieces fiberEuler 0 := by
    apply sub_eq_zero.mp
    apply AffineModification.derivation_zero_of_generators v
    · intro a
      change fiberEuler (j a)-GradedLND.component valuationPieces fiberEuler 0 (j a)=0
      rw [GradedLND.component_of_mem valuationPieces fiberEuler 0 (j_mem a),add_zero,
        fiberEuler_j,GradedLND.proj_of_mem valuationPieces (j_mem _),sub_self]
    · change fiberEuler τ-GradedLND.component valuationPieces fiberEuler 0 τ=0
      rw [GradedLND.component_of_mem valuationPieces fiberEuler 0 τ_mem,fiberEuler_τ,map_zero,sub_self]
    · change fiberEuler V-GradedLND.component valuationPieces fiberEuler 0 V=0
      rw [GradedLND.component_of_mem valuationPieces fiberEuler 0 V_mem,add_zero,fiberEuler_V]
      have hm : 2*V ∈ valuationPieces 2 := by simpa only [two_mul] using add_mem V_mem V_mem
      rw [GradedLND.proj_of_mem valuationPieces hm,sub_self]
  rw [he]
  simpa only [add_zero] using GradedLND.component_homogeneous valuationPieces fiberEuler 0 hr
end ComplexCancellation.Bundle

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Bundle
open Determinant


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Bundle.fiberEuler_homogeneous := @_root_.OAI.ComplexCancellation.Bundle.fiberEuler_homogeneous
