-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.exists_evalPt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:54.604809+00:00
-- url     : https://prove2.me/submissions/de808376-92a2-4a1f-b78b-852348b9b621

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spec_fromSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (ψ : Γ(X, U) →+* R) :
    ∃ (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), evalPt x U h = ψ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, h, ?_⟩
  have := eq_spec_fromSpec hU _ h
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm
end GlobalTheory.TangentOrigin
