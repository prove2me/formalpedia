-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phi_logTerm
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:37:04.636871+00:00
-- url     : https://prove2.me/submissions/5a249fad-81ce-4393-a797-15b30b27b3a9

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
theorem solution (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) (n : ℕ) :
    phi K p (logTerm hx n) = logTerm hφ n := by
  have hθ0 (y : ACrisZero K p) :
      phi K p (algebraMap (ACrisZero K p) (ACris K p) y) =
        algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y) := by
    rw [show phi K p = AdicCompletion.extendRingHom
        (Ideal.span {(p : ACrisZero K p)}) (Ideal.span {(p : ACris K p)})
        ((algebraMap (ACrisZero K p) (ACris K p)).comp (phiZero K p))
        span_p_le_comap_phiZero from rfl]
    rw [IsHausdorff.eq_iff_smodEq
      (I := (Ideal.span {(p : ACris K p)} : Ideal (ACris K p)))]
    simp only [smul_eq_mul, Ideal.mul_top]
    intro k
    change Ideal.Quotient.mk (Ideal.span {(p : ACris K p)} ^ k) _ =
      Ideal.Quotient.mk (Ideal.span {(p : ACris K p)} ^ k) _
    rw [AdicCompletion.extendRingHom, IsAdicComplete.mk_liftRingHom]
    simp only [AdicCompletion.extendFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    have heval (z : ACrisZero K p) :
        (AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) k)
          (algebraMap (ACrisZero K p) (ACris K p) z) =
        Ideal.Quotient.mk _ z := by
      rw [AlgHom.commutes]
      rfl
    rw [heval, Ideal.quotientMap_mk, RingHom.comp_apply]
  rw [logTerm, logTerm, hθ0]
  congr 1
  refine Subtype.ext ?_
  change (phiAway K p) (logTermZero hx n : 𝔸) = (logTermZero hφ n : 𝔸)
  simp only [logTermZero, dpowZero, Subalgebra.coe_mul, Subalgebra.coe_pow,
    Subalgebra.coe_neg, map_mul, map_pow, map_neg]
  rw [phiAway_dpow]
  simp [map_one, map_natCast]
