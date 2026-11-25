-- Prove2me | solution 1 for GlobalTheory.AbCoh.coneExact_baseChange_of_quasiIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:26.653958+00:00
-- url     : https://prove2.me/submissions/becfb4ef-f50b-48b0-8920-5fddc4f5fc9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
import Theorems.Thm_GlobalTheory_quasiIso_iff_coneExact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] [inst : Algebra R R']
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    GlobalTheory.ConeExact (K := fun p => R' ⊗[R] K.X p) (C := fun p => R' ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.baseChange R') (fun p => (C.d p (p + 1)).hom.baseChange R')
      (fun p => (φ.f p).hom.baseChange R') := by
  have key := (GlobalTheory.quasiIso_iff_coneExact _).1 h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key
end GlobalTheory.AbCoh
