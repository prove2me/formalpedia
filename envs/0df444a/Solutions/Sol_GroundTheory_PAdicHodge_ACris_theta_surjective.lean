-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.theta_surjective
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:28:13.378798+00:00
-- url     : https://prove2.me/submissions/a15b93e2-ffef-4f76-9f82-2a3c201d10ba

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

open GroundTheory.PAdicHodge.ACris in
theorem solution : Function.Surjective (theta K p) := by
  intro y
  obtain ⟨x, hx⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) (p := p) y
  refine ⟨algebraMap (AInf K p) (ACris K p) x, ?_⟩
  rw [IsScalarTower.algebraMap_apply (AInf K p) (ACrisZero K p) (ACris K p)]
  have hθ0 (z : ACrisZero K p) :
      theta K p (algebraMap (ACrisZero K p) (ACris K p) z) = thetaZero K p z := by
    rw [show theta K p = AdicCompletion.extendRingHom
        (Ideal.span {(p : ACrisZero K p)}) (Ideal.span {(p : 𝒪)})
        (thetaZero K p) span_p_le_comap_thetaZero from rfl]
    rw [IsHausdorff.eq_iff_smodEq (I := (Ideal.span {(p : 𝒪)} : Ideal 𝒪))]
    simp only [smul_eq_mul, Ideal.mul_top]
    intro n
    change Ideal.Quotient.mk (Ideal.span {(p : 𝒪)} ^ n) _ =
      Ideal.Quotient.mk (Ideal.span {(p : 𝒪)} ^ n) _
    rw [AdicCompletion.extendRingHom, IsAdicComplete.mk_liftRingHom]
    simp only [AdicCompletion.extendFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    have heval :
        (AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) n)
          (algebraMap (ACrisZero K p) (ACris K p) z) =
        Ideal.Quotient.mk _ z := by
      rw [AlgHom.commutes]
      rfl
    rw [heval, Ideal.quotientMap_mk]
  rw [hθ0]
  refine Subtype.ext ?_
  change (thetaAway K p) (algebraMap (AInf K p) 𝔸 x) = (y : K)
  rw [thetaAway_algebraMap, hx]
