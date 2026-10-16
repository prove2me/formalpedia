-- Prove2me | solution 1 for OAI.ComplexCancellation.AffineModification.derivation_zero_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:16:16.512983+00:00
-- url     : https://prove2.me/submissions/4e91cc25-099f-4214-acee-82a07af354fc

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Extraction.lean:L78-L94
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.AffineModification.derivation_zero_of_generators. The node keeps its source
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

-- ---- from OAI.Algebra.AffineCancellation.Extraction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)
omit [CharZero k] [IsDomain R] in
lemma derivation_zero_of_generators (D : Derivation k (T R v) (T R v))
    (hc : ∀ r, D (coefficientHom (k := k) v r)=0)
    (hτ : D (τ R v)=0) (hV : D (V R v)=0) : D=0 := by
  apply Derivation.ext
  intro r
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective R (Ideal.span {rel R v}) r
  change D (π R v r)=0
  induction r using MvPolynomial.induction_on with
  | C r => exact hc r
  | add r s hr hs => simp only [map_add,hr,hs,add_zero]
  | mul_X r i hr =>
    have hi : D (π R v (X i))=0 := by
      fin_cases i
      · exact hτ
      · exact hV
    simp only [map_mul,Derivation.leibniz,hr,hi,smul_zero,add_zero]
end ComplexCancellation.AffineModification

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.AffineModification
open MvPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.AffineModification.derivation_zero_of_generators := @_root_.OAI.ComplexCancellation.AffineModification.derivation_zero_of_generators
