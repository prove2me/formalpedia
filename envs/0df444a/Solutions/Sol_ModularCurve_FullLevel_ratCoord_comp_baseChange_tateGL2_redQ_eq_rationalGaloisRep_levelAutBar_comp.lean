-- Prove2me | solution 1 for ModularCurve.FullLevel.ratCoord_comp_baseChange_tateGL2_redQ_eq_rationalGaloisRep_levelAutBar_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ce4c0f82-b2bb-59d5-9315-85112378e6c8

import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_ratCoord_comp_baseChange_tateGL2_redQ_eq_rationalGaloisRep_levelAutBar_comp

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open ModularCurve ModularCurve.FullLevel

namespace CoordLevel

set_option maxHeartbeats 3200000 in

theorem tateEnd_levelOp_apply (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (ζ : Idx q) (γ : SL(2, ℤ)) (y : TateModule lam (jacComp q M')) :
    JH.tateEnd (q ^ 2 * M') (levelH q M') lam (levelOp q M' ζ γ) y =
      TateModule.rep lam (AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (AlgebraicCurve.SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ)) y :=
  Subtype.ext (funext fun n => by
    rw [JH.tateEnd_apply_coe, TateModule.rep_apply]
    exact levelOp_apply q M' ζ γ _)

set_option maxHeartbeats 3200000 in

theorem coord_tateGL2_redQ (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (hGL : GL2Laws q M')
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (hΨ : ∀ (γ : SL(2, ℤ)) (x : TateModule lam (Jac q M')) (ζ : Idx q),
      Ψ (tateEnd q M' lam (slJac q M' γ) x) ζ =
        JH.tateEnd (q ^ 2 * M') (levelH q M') lam (levelOp q M' ζ γ⁻¹) (Ψ x ζ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (ζ : Idx q) (x : TateModule lam (Jac q M')) :
    Ψ (tateGL2 q M' lam (redQ q γ) x) ζ =
      TateModule.rep lam (AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (AlgebraicCurve.SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)) (Ψ x ζ) := by
  have h1 : tateGL2 q M' lam (redQ q γ) x = tateEnd q M' lam (slJac q M' γ) x := by
    show tateEnd q M' lam (gl2Jac q M' (redQ q γ)) x = _
    rw [gl2Jac_redQ hGL γ hγ]
  rw [h1, hΨ, tateEnd_levelOp_apply]

end CoordLevel

set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (hGL : GL2Laws q M')
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (hΨ : ∀ (γ : SL(2, ℤ)) (x : TateModule lam (Jac q M')) (ζ : Idx q),
      Ψ (tateEnd q M' lam (slJac q M' γ) x) ζ =
        JH.tateEnd (q ^ 2 * M') (levelH q M') lam (levelOp q M' ζ γ⁻¹) (Ψ x ζ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (ζ : Idx q) :
    ratCoord q M' lam Ψ ζ ∘ₗ (tateGL2 q M' lam (redQ q γ)).baseChange ℚ_[lam] =
      ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (AlgebraicCurve.SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)) ∘ₗ ratCoord q M' lam Ψ ζ := by
  refine TensorProduct.AlgebraTensorModule.ext fun a x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, ratCoord_tmul, ratCoord_tmul,
    ModularCurve.rationalGaloisRep_apply, LinearMap.baseChange_tmul,
    CoordLevel.coord_tateGL2_redQ q M' lam hGL Ψ hΨ γ hγ ζ x]

end S_ModularCurve_FullLevel_ratCoord_comp_baseChange_tateGL2_redQ_eq_rationalGaloisRep_levelAutBar_comp
end P2MW
export P2MW.S_ModularCurve_FullLevel_ratCoord_comp_baseChange_tateGL2_redQ_eq_rationalGaloisRep_levelAutBar_comp (solution)
