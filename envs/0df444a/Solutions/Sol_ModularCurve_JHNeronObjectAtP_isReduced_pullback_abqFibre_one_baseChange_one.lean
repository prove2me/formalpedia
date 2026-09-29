-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.isReduced_pullback_abqFibre_one_baseChange_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2b23668b-3555-5cc4-b3ae-464fc167bcfd

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
import Theorems.Thm_AlgebraicGeometry_smooth_pullbackFst_comp_of_forall_iff_exists_torus_of_flat
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_isReduced_pullback_abqFibre_one_baseChange_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve ModularCurve.JHNeronObjectAtP in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM A) (O : ModularCurve.JHNeronObjectAtP p M H hpM A hA Λ) :
    IsReduced (Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1) := by

  let κ := ResidueField ↥A
  let r := resPt A ≫ Λ.σA
  let sG := RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g
  let sB := RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f
  have hq : (O.abqFibre 0).1 ≫ sB = (O.abqFibre 1).1 ≫ sB := (O.abqFibre 0).2.trans (O.abqFibre 1).2.symm
  let q := pullback.lift (O.abqFibre 0).1 (O.abqFibre 1).1 hq

  haveI := O.smooth
  haveI := O.quasiCompact
  haveI := O.locallyOfFiniteType
  haveI hsm : Smooth sG := MorphismProperty.pullback_snd (P := @Smooth) O.g (resPt A ≫ Λ.σA) inferInstance
  haveI : LocallyOfFiniteType sG := MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) O.g (resPt A ≫ Λ.σA) inferInstance
  haveI : IsLocallyNoetherian (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g) := LocallyOfFiniteType.isLocallyNoetherian sG
  haveI : CompactSpace ↑(RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g) := inferInstance
  haveI : IsNoetherian (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g) := {}
  haveI : IsReduced (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g) := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian sG

  haveI : Surjective sB := ⟨fun y => ⟨((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1.base y, by
    rw [← Scheme.Hom.comp_apply, ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).2]
    rfl⟩⟩
  haveI : Flat q := O.abqFibre_flat
  haveI : Surjective q := O.abqFibre_surjective
  haveI : Flat (pullback.fst sB sB) := MorphismProperty.pullback_fst (P := @Flat) sB sB inferInstance
  haveI : Surjective (pullback.fst sB sB) := MorphismProperty.pullback_fst (P := @Surjective) sB sB inferInstance
  have hq0 : q ≫ pullback.fst sB sB = (O.abqFibre 0).1 := pullback.lift_fst _ _ _
  haveI : Flat (O.abqFibre 0).1 := by rw [← hq0]; infer_instance
  haveI : Surjective (O.abqFibre 0).1 := by rw [← hq0]; infer_instance
  haveI : IsReduced (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) := AlgebraicGeometry.isReduced_of_flat_of_surjective (O.abqFibre 0).1
  haveI : IsLocallyNoetherian (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) := AlgebraicGeometry.isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact (O.abqFibre 0).1

  haveI : Smooth (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫ (O.abqFibre 0).1) :=
    AlgebraicGeometry.smooth_pullbackFst_comp_of_forall_iff_exists_torus_of_flat sG sB (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) hsm O.abqFibre O.abqFibre_mul
      O.abqFibre_flat O.abqFibre_surjective inferInstance O.toricRank O.torusFibre O.torusFibre_isClosedImmersion O.abqFibre_eq_one_iff
  exact AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫ (O.abqFibre 0).1)

end S_ModularCurve_JHNeronObjectAtP_isReduced_pullback_abqFibre_one_baseChange_one
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_isReduced_pullback_abqFibre_one_baseChange_one (solution)
