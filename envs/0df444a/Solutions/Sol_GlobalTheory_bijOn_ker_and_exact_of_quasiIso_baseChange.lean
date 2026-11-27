-- Prove2me | solution 1 for GlobalTheory.bijOn_ker_and_exact_of_quasiIso_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:47.876195+00:00
-- url     : https://prove2.me/submissions/998d1872-6338-4214-abc2-9c83f617ae13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_BijOnKerAndExactOfQuasiIsoBaseChange
import Theorems.Thm_GlobalTheory_bijOn_ker_and_exact_of_quasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R R' : Type) [CommRing R] [CommRing R']
    [inst : Algebra R R'] (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C)
    (h : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    Set.BijOn ((φ.f 0).hom.baseChange R') (LinearMap.ker ((K.d 0 1).hom.baseChange R'))
        (LinearMap.ker ((C.d 0 1).hom.baseChange R')) ∧
      (Function.Exact ((C.d 0 1).hom.baseChange R') ((C.d 1 2).hom.baseChange R') →
        Function.Exact ((K.d 0 1).hom.baseChange R') ((K.d 1 2).hom.baseChange R')) := by
  have key := bijOn_ker_and_exact_of_quasiIso _ h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key
end GlobalTheory
