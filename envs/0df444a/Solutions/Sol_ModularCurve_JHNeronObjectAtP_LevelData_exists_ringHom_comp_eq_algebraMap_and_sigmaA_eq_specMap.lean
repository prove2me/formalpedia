-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.LevelData.exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c942fe9a-58ae-5060-9663-0bed11488695

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JHNeronObjectAtP.LevelData p M H hpM A) :
    ∃ ρ : baseRing p →+* ↥A, A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ) ∧ Λ.σA = Spec.map (CommRingCat.ofHom ρ) := by
  refine ⟨(Spec.preimage Λ.σA).hom, ?_, ?_⟩
  · have h := Λ.hσA
    rw [← Spec.map_preimage Λ.σA] at h
    change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (Spec.preimage Λ.σA) =
      Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (AlgebraicClosure ℚ))) at h
    rw [← Spec.map_comp] at h
    have h2 := Spec.map_injective h
    have h3 := congrArg CommRingCat.Hom.hom h2
    simpa using h3
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]

end S_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap (solution)
