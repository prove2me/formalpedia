-- Prove2me | solution 1 for OAI.ComplexCancellation.Torsor.frameMap_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:23:35.092186+00:00
-- url     : https://prove2.me/submissions/70b36292-879f-4703-bde1-f2007420bc2e

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/TorsorEuler.lean:L13-L28
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Torsor.frameMap_intertwining. The node keeps its source
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

-- ---- from OAI.Algebra.AffineCancellation.Intertwining ----
namespace OAI

noncomputable section

namespace ComplexCancellation.DerivationIntertwining
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
lemma mvPolynomial (f : R →ₐ[k] S) (D : Derivation k R R) (E : Derivation k S S)
    {ι : Type*} (q : MvPolynomial ι k →ₐ[k] R) (p : MvPolynomial ι k)
    (hX : ∀ i, E (f (q (MvPolynomial.X i)))=f (D (q (MvPolynomial.X i)))) : E (f (q p))=f (D (q p)) := by
  change q p ∈ subalgebra f D E
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.C_eq_algebraMap,q.commutes]; exact (subalgebra f D E).algebraMap_mem c
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | mul_X r i hr => rw [map_mul]; exact mul_mem hr (hX i)
end ComplexCancellation.DerivationIntertwining

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.TorsorEuler ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ)
lemma frameMap_intertwining (r : Determinant.T) :
    LaurentEuler.derivation (k := ℂ) (frameMap ρ Q r)=frameMap ρ Q (Determinant.Euler r) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {Determinant.relation}) r
  apply DerivationIntertwining.mvPolynomial (frameMap ρ Q) Determinant.Euler LaurentEuler.derivation Determinant.π p
  intro i
  fin_cases i
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.a)=frameMap ρ Q (Determinant.Euler Determinant.a)
    rw [Determinant.Euler_a,frameMap_a,LaurentEuler.monomial,one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.d)=frameMap ρ Q (Determinant.Euler Determinant.d)
    rw [Determinant.Euler_d,frameMap_d,LaurentEuler.monomial,one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.b)=frameMap ρ Q (Determinant.Euler Determinant.b)
    rw [Determinant.Euler_b,map_neg,frameMap_b,LaurentEuler.monomial,neg_one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.c)=frameMap ρ Q (Determinant.Euler Determinant.c)
    rw [Determinant.Euler_c,map_neg,frameMap_c,LaurentEuler.monomial,neg_one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.u)=frameMap ρ Q (Determinant.Euler Determinant.u)
    rw [Determinant.Euler_u,map_zero,frameMap_u,LaurentEuler.coefficient]
variable [IsDomain P]
end ComplexCancellation.Torsor

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Torsor
open LaurentPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Torsor.frameMap_intertwining := @_root_.OAI.ComplexCancellation.Torsor.frameMap_intertwining
