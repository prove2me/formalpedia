-- Prove2me | solution 1 for O3.Stage2RouteB.conjugateSmoothness_implies_belowGeometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:24.901861+00:00
-- url     : https://prove2.me/submissions/eaba01ba-36b9-4d7e-b9cc-b444eede32fa

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_pairing_dualityMap_self
import Theorems.Thm_O3_Stage2RouteB_squaredLpEnergy_eq_quadraticRegularizer
import Theorems.Thm_O3_Stage2RouteB_conjugate_constant_cancel
import Theorems.Thm_O3_Stage2RouteB_lpNorm_dualityMap
import Theorems.Thm_O3_Stage2RouteB_dualityMap_conjugate_comp
import Theorems.Thm_O3_Stage2RouteB_lpNorm_scalar_mul
import Theorems.Thm_O3_Stage2RouteB_squaredLpEnergy_dualityMap
import Theorems.Thm_O3_Stage2RouteB_fenchelYoung_lower
import Theorems.Thm_P2M_O3_Stage2RouteB_pairing_add_left__aa498a6aacda
import Theorems.Thm_O3_Stage2RouteB_pairing_scalar_left
import Theorems.Thm_P2M_O3_Stage2RouteB_pairing_add_right__1f4cec1cfddf
import Theorems.Thm_O3_Stage2RouteB_pairing_scalar_right
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_one_lt_conjugateExponent
import Theorems.Thm_O3_pairing_comm
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution
    (hsmooth : ConjugateSmoothnessStatement) : BelowGeometryStatement := by
  intro p hp hp2 d x y
  let h : Point d := y - x
  let u : Point d := dualityMap p x
  let jh : Point d := dualityMap p h
  let v : Point d := u + fun i ↦ (p - 1) * jh i
  have hs := hsmooth p hp hp2 d u v
  have hvsub : v - u = (fun i ↦ (p - 1) * jh i) := by
    funext i
    simp only [v, Pi.sub_apply, Pi.add_apply]
    ring
  have hJqu : dualityMap (conjugateExponent p) u = x := by
    exact dualityMap_conjugate_comp hp x
  have hEu : squaredLpEnergy (conjugateExponent p) u = squaredLpEnergy p x := by
    exact squaredLpEnergy_dualityMap hp x
  have hnormjh : lpNorm (conjugateExponent p) jh = lpNorm p h :=
    lpNorm_dualityMap hp h
  rw [hvsub, hJqu, hEu] at hs
  rw [lpNorm_scalar_mul (lt_trans zero_lt_one (one_lt_conjugateExponent hp))] at hs
  rw [abs_of_pos (by linarith : 0 < p - 1), hnormjh] at hs
  have hconst : ((conjugateExponent p - 1) / 2) *
      ((p - 1) * lpNorm p h) ^ (2 : ℕ) =
      ((p - 1) / 2) * (lpNorm p h) ^ (2 : ℕ) := by
    have hc := conjugate_constant_cancel hp
    nlinarith
  rw [hconst] at hs
  have hfenchel := fenchelYoung_lower hp v y
  have hpairjx : pairing (dualityMap p x) x = (lpNorm p x) ^ (2 : ℕ) :=
    pairing_dualityMap_self hp x
  have hpairjh : pairing (dualityMap p h) h = (lpNorm p h) ^ (2 : ℕ) :=
    pairing_dualityMap_self hp h
  have hxy : y = x + h := by
    funext i
    simp only [h, Pi.add_apply, Pi.sub_apply]
    ring
  rw [show quadraticRegularizer p 0 y = squaredLpEnergy p y by
    exact (squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p) y).symm]
  rw [show quadraticRegularizer p 0 x = squaredLpEnergy p x by
    exact (squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p) x).symm]
  change squaredLpEnergy p x + pairing (dualityMap p x) h +
      (p - 1) / 2 * lpNorm p h ^ (2 : ℕ) ≤ squaredLpEnergy p y
  have hvpair : pairing v y = pairing u y + (p - 1) * pairing jh y := by
    change pairing (u + fun i ↦ (p - 1) * jh i) y = _
    rw [pairing_add_left', pairing_scalar_left]
  rw [hvpair] at hfenchel
  rw [hxy] at hfenchel
  rw [pairing_add_right'] at hfenchel
  simp only [u, jh] at hs hfenchel
  rw [pairing_add_right'] at hfenchel
  rw [pairing_scalar_right] at hs
  rw [pairing_comm x (dualityMap p h)] at hs
  rw [hpairjx, hpairjh] at hfenchel
  rw [hxy]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)] at hs hfenchel ⊢
  simp only [quadraticRegularizer, sub_zero] at hs hfenchel ⊢
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)]
  simp only [quadraticRegularizer, sub_zero]
  nlinarith
end O3.Stage2RouteB
