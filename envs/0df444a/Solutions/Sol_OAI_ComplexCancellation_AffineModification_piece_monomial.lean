-- Prove2me | solution 1 for OAI.ComplexCancellation.AffineModification.piece_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:14:37.394269+00:00
-- url     : https://prove2.me/submissions/372a3a2f-81e7-49b0-8ef5-c32d892c5fc9

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ModificationGrading.lean:L113-L125
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.AffineModification.piece_monomial. The node keeps its source
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
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_even
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_negative
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_odd

-- ---- from OAI.Algebra.AffineCancellation.ModificationGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma degree_cases (e : ℤ) :
    (∃ n : ℕ, e=-(n+1:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)+1) := by
  by_cases hn : e < 0
  · exact Or.inl ⟨(-e-1).toNat,by omega⟩
  · by_cases hm : e%2=0
    · exact Or.inr (Or.inl ⟨(e/2).toNat,by omega⟩)
    · exact Or.inr (Or.inr ⟨(e/2).toNat,by omega⟩)
lemma piece_monomial (e : ℤ) : ∃ i h : ℕ, ∀ r ∈ pieces R v e,
    ∃ s : R, r=τ R v^i*V R v^h*algebraMap R (T R v) s := by
  rcases degree_cases e with ⟨n,rfl⟩ | ⟨n,rfl⟩ | ⟨n,rfl⟩
  · refine ⟨n+1,0,?_⟩
    intro r hr
    have hr' : r ∈ pieces R v (-((n+1:ℕ):ℤ)) := by simpa using hr
    simpa using piece_negative R v (n+1) hr'
  · refine ⟨0,n,?_⟩
    intro r hr
    simpa using piece_even R v n hr
  · refine ⟨1,n+1,?_⟩
    intro r hr
    simpa using piece_odd R v n hr
end ComplexCancellation.AffineModification

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.AffineModification
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra


theorem solution : type_of% @_root_.OAI.ComplexCancellation.AffineModification.piece_monomial := @_root_.OAI.ComplexCancellation.AffineModification.piece_monomial
