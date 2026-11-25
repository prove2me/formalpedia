-- Prove2me | solution 1 for GlobalTheory.ZM.SegreCoord.mem_graphIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:55.809317+00:00
-- url     : https://prove2.me/submissions/774441e1-ccf1-4b31-b123-56e73ac78fae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SegreCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SegreCoord
open GlobalTheory.ZM.RepBC GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y} {σ₁ σ₂ : Type}
  (s : σ₁ → H.Sec) (t : σ₂ → K.Sec)
namespace GlobalTheory.ZM.SegreCoord
theorem _root_.solution {R : Type} [CommRing R] (f : P ⟶ Sp R) (F : MvPolynomial (σ₁ × σ₂) R) :
    F ∈ graphIdeal f H s p K t q ↔ ∀ (T : Type) [CommRing T] (β : R →+* T) (y : Sp T ⟶ P) (a : σ₁ → T) (b : σ₂ → T),
      y ≫ f = spMap β → SecCoord H s (y ≫ p) a → SecCoord K t (y ≫ q) b →
        MvPolynomial.eval₂ β (fun i : σ₁ × σ₂ => a i.1 * b i.2) F = 0 := by
  simp only [graphIdeal, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, and_imp]
end GlobalTheory.ZM.SegreCoord
