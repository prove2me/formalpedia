-- Prove2me | solution 1 for ModularCurve.heckeDivBar_cuspidalDivisor_self_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1b2a9c36-07fc-56ce-af66-ea8410420c40

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single_of_forall_restrictAlong_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_sum

open AlgebraicCurve ModularCurve

noncomputable section

theorem solution (p : ℕ) [NeZero p] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))] (Winf : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))) (hfibInf : ∀ W', W' ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ (cuspInftyBar p) ↔ W' = Winf) (hWinf : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) Winf * Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα Winf = p) (hrWinf : Winf.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα = cuspInftyBar p) (Vzero : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))) (Smid : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p)))) (hVzero : Vzero ∉ Smid) (hfibZero : ∀ V, V ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ (cuspZeroBar p) ↔ V = Vzero ∨ V ∈ Smid) (hVzero1 : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) Vzero * Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα Vzero = 1) (hrVzero : Vzero.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα = cuspZeroBar p) (hsumSmid : ∑ V ∈ Smid, Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) V * Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα V = p - 1) (hrSmid : ∀ V ∈ Smid, V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα = cuspInftyBar p) : heckeDivBar hα hβ (cuspidalDivisor p) = cuspidalDivisor p := by
  classical
  set β := heckeBetaBar (AlgebraicClosure ℚ) p p
  set α := heckeAlphaBar (AlgebraicClosure ℚ) p p

  have hfibI : Place.fiberAlong β hβ (cuspInftyBar p) = {Winf} :=
    Finset.ext fun W' => by rw [hfibInf W', Finset.mem_singleton]
  have hinf : heckeDivBar hα hβ (Finsupp.single (cuspInftyBar p) 1)
      = Finsupp.single (cuspInftyBar p) (p : ℤ) := by
    have hcoll : ∀ w ∈ Place.fiberAlong β hβ (cuspInftyBar p), w.restrictAlong α hα = cuspInftyBar p := by
      intro w hw; rw [(hfibInf w).mp hw]; exact hrWinf
    unfold heckeDivBar
    rw [Divisor.correspondence_single_of_forall_restrictAlong_eq β α hβ hα _ hcoll 1, hfibI,
      Finset.sum_singleton]
    have h1 : (1 : ℤ) * ((Place.ramificationIndexAlong β Winf : ℤ) * (Place.inertiaDegAlong α hα Winf : ℤ)) = p := by
      rw [one_mul]; exact_mod_cast hWinf
    rw [h1]

  have hfibZ : Place.fiberAlong β hβ (cuspZeroBar p) = insert Vzero Smid :=
    Finset.ext fun V => by rw [hfibZero V, Finset.mem_insert]
  have hzero : heckeDivBar hα hβ (Finsupp.single (cuspZeroBar p) 1)
      = Finsupp.single (cuspZeroBar p) 1 + Finsupp.single (cuspInftyBar p) ((p : ℤ) - 1) := by
    unfold heckeDivBar
    rw [Divisor.correspondence_single β α hβ hα _ 1, hfibZ, Finset.sum_insert hVzero, hrVzero]
    have h0 : (1 : ℤ) * (Place.ramificationIndexAlong β Vzero : ℤ) * (Place.inertiaDegAlong α hα Vzero : ℤ) = 1 := by
      rw [one_mul]; exact_mod_cast hVzero1
    have hsum : ∑ w ∈ Smid, Finsupp.single (w.restrictAlong α hα)
        ((1 : ℤ) * (w.ramificationIndexAlong β : ℤ) * (w.inertiaDegAlong α hα : ℤ))
        = Finsupp.single (cuspInftyBar p) ((p : ℤ) - 1) := by
      rw [Finset.sum_congr rfl fun w hw => by rw [hrSmid w hw], ← Finsupp.single_finsetSum]
      congr 1
      have hp : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
        have : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
        push_cast [Nat.cast_sub this]; ring
      rw [← hp, ← hsumSmid]; push_cast
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [h0, hsum]
  rw [cuspidalDivisor_def, map_sub, hinf, hzero]

  rw [add_sub_assoc, ← Finsupp.single_sub, sub_eq_add_neg (Finsupp.single (cuspZeroBar p) (1 : ℤ)),
    ← Finsupp.single_neg]
  congr 2; ring

end

end S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_sum
end P2MW
export P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_sum (solution)
