-- Prove2me | solution 1 for GlobalTheory.BoundedRegular.exists_point_norm_valF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:58.462871+00:00
-- url     : https://prove2.me/submissions/3c81007f-cfc2-4c29-afb3-522285fdef2d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Theorems.Thm_GlobalTheory_BoundedRegular_valF_spMap_comp_eq
import Theorems.Thm_GlobalTheory_isLocalHom_integralClosureToPadicAlgClIntegers
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open GlobalTheory.BoundedRegular
namespace GlobalTheory.BoundedRegular
theorem _root_.solution {X : Scheme.{0}} {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ X) (U : X.Opens)
    (hy : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y) ⁻¹ᵁ U)
    (φ : Γ(X, U)) :
    ∃ y' : Sp (OO p) ⟶ X, y' (cPt p) = y (IsLocalRing.closedPoint (integralClosure ℤ_[p] K)) ∧
      Set.range (gPt p ≫ y') ⊆ U ∧
      valF (gPt p ≫ y') U φ = (((Scheme.ΓSpecIso (.of K)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE
          U ⊤ hy φ) : K) : PadicAlgCl p) := by
  haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
  have e : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) ≫ y =
      spMap K.val.toRingHom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  refine ⟨spMap (integralClosureToPadicAlgClIntegers K) ≫ y, ?_, ?_, ?_⟩
  · refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg y ?_)
    exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
  · rw [e]
    rintro _ ⟨q, rfl⟩
    exact hy (Set.mem_univ (spMap K.val.toRingHom q))
  · rw [e, valF_spMap_comp_eq _ _ U hy]
    rfl
end GlobalTheory.BoundedRegular
