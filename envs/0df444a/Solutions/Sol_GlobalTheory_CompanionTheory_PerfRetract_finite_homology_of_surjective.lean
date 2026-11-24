-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfRetract.finite_homology_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:03.32825+00:00
-- url     : https://prove2.me/submissions/bd314845-a1bf-403e-9494-36cac82e86f8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfRetract
variable {R : Type} [CommRing R] {E : ℕ → Type} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]
namespace GlobalTheory.CompanionTheory.PerfRetract
theorem _root_.solution (C : CochainComplex (ModuleCat.{0} R) ℕ) (i j k : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : W →ₗ[R] (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype))
    (hf : Function.Surjective f) : Module.Finite R (C.homology j) := by
  have e := (C.homologyIsoSc' i j k hi hk ≪≫ (C.sc' i j k).moduleCatHomologyIso).toLinearEquiv
  have h1 : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype) :=
    Module.Finite.of_surjective f hf
  have h2 : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      LinearMap.range (C.sc' i j k).moduleCatToCycles) := by
    refine Module.Finite.equiv (Submodule.quotEquivOfEq
      ((LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype)
      (LinearMap.range (C.sc' i j k).moduleCatToCycles) ?_)
    ext x
    exact ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩, fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩⟩
  have h3 : Module.Finite R (C.sc' i j k).moduleCatLeftHomologyData.H := h2
  exact Module.Finite.equiv e.symm
end GlobalTheory.CompanionTheory.PerfRetract
