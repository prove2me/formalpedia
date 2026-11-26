-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phi_algebraMap_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:32:31.235043+00:00
-- url     : https://prove2.me/submissions/b87349f7-50c0-4458-84df-e0c559c7f758

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}

open GroundTheory.PAdicHodge.ACris in
theorem solution (y : ACrisZero K p) :
    phi K p (algebraMap (ACrisZero K p) (ACris K p) y) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y) := by
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
  have heval (z : ACrisZero K p) :
      (AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) n)
        (algebraMap (ACrisZero K p) (ACris K p) z) =
      Ideal.Quotient.mk _ z := by
    rw [AlgHom.commutes]
    rfl
  rw [heval, Ideal.quotientMap_mk, RingHom.comp_apply]
