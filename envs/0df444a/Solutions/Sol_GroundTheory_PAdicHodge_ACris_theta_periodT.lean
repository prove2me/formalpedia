-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.theta_periodT
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:26:14.179662+00:00
-- url     : https://prove2.me/submissions/841c8941-a9a9-41ec-909f-0c3e13aa4801

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
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
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
variable [CharZero K]

open GroundTheory.PAdicHodge.ACris in
theorem solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : theta K p (periodT hε) = 0 := by
  have hx : AInf.mu (K := K) ε ∈ RingHom.ker θ := mu_mem_ker hε
  have hs : IsAdicSum 𝔭 (logTerm hx) (log hx) := (exists_isAdicSum_logTerm hx).choose_spec
  have hf : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta K p) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have hθ0 (y : ACrisZero K p) :
      theta K p (algebraMap (ACrisZero K p) (ACris K p) y) = thetaZero K p y := by
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
          (algebraMap (ACrisZero K p) (ACris K p) y) =
        Ideal.Quotient.mk _ y := by
      rw [AlgHom.commutes]
      rfl
    rw [heval, Ideal.quotientMap_mk]
  have hterm (n : ℕ) : theta K p (logTerm hx n) = 0 := by
    rw [logTerm, hθ0]
    refine Subtype.ext ?_
    change (thetaAway K p) (logTermZero hx n : 𝔸) = 0
    simp only [logTermZero, dpowZero, Subalgebra.coe_mul, Subalgebra.coe_pow,
      Subalgebra.coe_neg, map_mul, map_pow, map_neg]
    rw [thetaAway_dpow hx (Nat.succ_ne_zero n)]
    simp
  have hmap : IsAdicSum (Ideal.span {(p : 𝒪)}) (fun n => theta K p (logTerm hx n))
      (theta K p (log hx)) := IsAdicSum.map (theta K p) hf hs
  have hzero : IsAdicSum (Ideal.span {(p : 𝒪)}) (fun _ => (0 : 𝒪)) (theta K p (log hx)) := by
    convert hmap using 1
    funext n
    exact (hterm n).symm
  change theta K p (log hx) = 0
  rw [IsHausdorff.eq_iff_smodEq (I := (Ideal.span {(p : 𝒪)} : Ideal 𝒪))]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro k
  obtain ⟨N, hN⟩ := hzero k
  have h := hN N le_rfl
  rw [Finset.sum_const_zero, sub_zero] at h
  exact SModEq.zero.mpr h
