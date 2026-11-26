-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phi_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:21:04.002988+00:00
-- url     : https://prove2.me/submissions/30f27392-a313-4005-b493-ace825b46bd8

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
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

open GroundTheory.PAdicHodge.ACris in
theorem solution (x : AInf K p) :
    phi K p (algebraMap (AInf K p) (ACris K p) x) =
      algebraMap (AInf K p) (ACris K p) (φ x) := by
  rw [IsScalarTower.algebraMap_apply (AInf K p) (ACrisZero K p) (ACris K p)]
  rw [IsScalarTower.algebraMap_apply (AInf K p) (ACrisZero K p) (ACris K p)]
  have h0 : phiZero K p (algebraMap (AInf K p) (ACrisZero K p) x) =
      algebraMap (AInf K p) (ACrisZero K p) (φ x) := by
    refine Subtype.ext ?_
    change phiAway K p (algebraMap (AInf K p) 𝔸 x) =
      algebraMap (AInf K p) 𝔸 (φ x)
    exact phiAway_algebraMap x
  rw [show phi K p = AdicCompletion.extendRingHom
      (Ideal.span {(p : ACrisZero K p)}) (Ideal.span {(p : ACris K p)})
      ((algebraMap (ACrisZero K p) (ACris K p)).comp (phiZero K p))
      span_p_le_comap_phiZero from rfl]
  rw [IsHausdorff.eq_iff_smodEq
    (I := (Ideal.span {(p : ACris K p)} : Ideal (ACris K p)))]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro n
  change Ideal.Quotient.mk (Ideal.span {(p : ACris K p)} ^ n) _ =
    Ideal.Quotient.mk (Ideal.span {(p : ACris K p)} ^ n) _
  rw [AdicCompletion.extendRingHom, IsAdicComplete.mk_liftRingHom]
  simp only [AdicCompletion.extendFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  have heval (y : ACrisZero K p) :
      (AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) n)
        (algebraMap (ACrisZero K p) (ACris K p) y) =
      Ideal.Quotient.mk _ y := by
    rw [AlgHom.commutes]
    rfl
  rw [heval]
  rw [Ideal.quotientMap_mk, RingHom.comp_apply, h0]
