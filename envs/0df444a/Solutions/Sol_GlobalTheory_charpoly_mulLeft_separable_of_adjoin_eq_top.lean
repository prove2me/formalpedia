-- Prove2me | solution 1 for GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:11.042891+00:00
-- url     : https://prove2.me/submissions/6b878258-77b7-4b2d-bbdf-583250d7e8a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A]
    [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A →
    (LinearMap.mulLeft E y).charpoly.Separable := by
  intro E A _ _ _ _ _ y htop hred
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hfin : Module.finrank E A = (minpoly E y).natDegree := pb.finrank
  have hmin : minpoly E (LinearMap.mulLeft E y) = minpoly E y := by
    have h := minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective (R := E) (A := A)) y
    rw [← h]
    rfl
  have hdvd : minpoly E y ∣ (LinearMap.mulLeft E y).charpoly :=
    hmin ▸ LinearMap.minpoly_dvd_charpoly _
  have heq : (LinearMap.mulLeft E y).charpoly = minpoly E y :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) hdvd
      (by rw [LinearMap.charpoly_natDegree, hfin])
  rw [heq]
  have hsq : Squarefree (minpoly E y) := (minpoly.isRadical E y).squarefree (minpoly.ne_zero hint)
  exact PerfectField.separable_iff_squarefree.mpr hsq
end GlobalTheory
