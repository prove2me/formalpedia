-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.comp_degeneracyHom_eq_degeneracyHom_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d3f4e025-f772-56e5-8ebe-bd8267887ebf

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_comp_degeneracyHom_eq_degeneracyHom_comp

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (t t' : HeckeAlg)
    (φ : SchemeHomOver O.g O.g)
    (hφt : letI := heckeModuleBar (N₀ * p); ∀ x : JZero (N₀ * p), (O.pts (t • x)).1 = (O.pts x).1 ≫ φ.1)
    (φ' : SchemeHomOver Λ.f Λ.f)
    (hφ't : letI := heckeModuleBar N₀; ∀ x : JZero N₀, (Λ.pts (t' • x)).1 = (Λ.pts x).1 ≫ φ'.1)
    (hdeg : ∀ x : JZero (N₀ * p),
      degeneracyPushforwardPair N₀ p i (letI := heckeModuleBar (N₀ * p); t • x) =
        (letI := heckeModuleBar N₀; t' • degeneracyPushforwardPair N₀ p i x)) :
    φ.1 ≫ (O.degeneracyHom i).1 = (O.degeneracyHom i).1 ≫ φ'.1 := by
  haveI : IsProper Λ.f := hΛ.1.proper
  haveI : Smooth O.g := O.smooth
  haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
  haveI : IsDiscreteValuationRing (baseRing p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsReduced O.G := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian O.g
  haveI : IsFractionRing (baseRing p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  have key := AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := baseRing p) ℚ (AlgebraicClosure ℚ) (gY := O.g) (gX := Λ.f)
      (NeronModelInfra.schemeHomOverComp φ (O.degeneracyHom i))
      (NeronModelInfra.schemeHomOverComp (O.degeneracyHom i) φ') ?_
  · exact congrArg Subtype.val key
  intro z
  obtain ⟨x, rfl⟩ := O.pts.surjective z
  have e1 : (O.pts x).1 ≫ φ.1 = (O.pts (letI := heckeModuleBar (N₀ * p); t • x)).1 := (hφt x).symm
  have e2 : (O.pts (letI := heckeModuleBar (N₀ * p); t • x)).1 ≫ (O.degeneracyHom i).1 =
      (Λ.pts (degeneracyPushforwardPair N₀ p i (letI := heckeModuleBar (N₀ * p); t • x))).1 :=
    (O.degeneracyHom_pts i _).symm
  have e3 : (O.pts x).1 ≫ (O.degeneracyHom i).1 = (Λ.pts (degeneracyPushforwardPair N₀ p i x)).1 :=
    (O.degeneracyHom_pts i x).symm
  simp only [NeronModelInfra.schemeHomOverComp_coe]
  calc (O.pts x).1 ≫ φ.1 ≫ (O.degeneracyHom i).1
      = (O.pts (letI := heckeModuleBar (N₀ * p); t • x)).1 ≫ (O.degeneracyHom i).1 := by
        rw [← Category.assoc, e1]
    _ = (Λ.pts (degeneracyPushforwardPair N₀ p i (letI := heckeModuleBar (N₀ * p); t • x))).1 := e2
    _ = (Λ.pts (letI := heckeModuleBar N₀; t' • degeneracyPushforwardPair N₀ p i x)).1 := by rw [hdeg x]
    _ = (Λ.pts (degeneracyPushforwardPair N₀ p i x)).1 ≫ φ'.1 := hφ't _
    _ = (O.pts x).1 ≫ (O.degeneracyHom i).1 ≫ φ'.1 := by rw [← Category.assoc, e3]

end S_ModularCurve_JZeroNeronObjectAtP_comp_degeneracyHom_eq_degeneracyHom_comp
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_comp_degeneracyHom_eq_degeneracyHom_comp (solution)
