-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.schemeHomOver_ext_of_forall_pts_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/81365e55-6412-5bd2-b5b6-973bb9e9d19a

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

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOver_ext_of_forall_pts_comp_eq

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (ψ₁ ψ₂ : SchemeHomOver O.g Λ.f)
    (h : ∀ x : JZero (N₀ * p), (O.pts x).1 ≫ ψ₁.1 = (O.pts x).1 ≫ ψ₂.1) :
    ψ₁ = ψ₂ := by
  haveI : IsProper Λ.f := hΛ.1.proper
  haveI : Smooth O.g := O.smooth
  haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
  haveI : IsDiscreteValuationRing (baseRing p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsReduced O.G := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian O.g
  haveI : IsFractionRing (baseRing p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := baseRing p) ℚ (AlgebraicClosure ℚ) (gY := O.g) (gX := Λ.f) ψ₁ ψ₂ ?_
  intro z
  obtain ⟨x, rfl⟩ := O.pts.surjective z
  exact h x

end S_ModularCurve_JZeroNeronObjectAtP_schemeHomOver_ext_of_forall_pts_comp_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOver_ext_of_forall_pts_comp_eq (solution)
