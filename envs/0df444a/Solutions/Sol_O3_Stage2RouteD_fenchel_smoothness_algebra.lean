-- Prove2me | solution 1 for O3.Stage2RouteD.fenchel_smoothness_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:47.406818+00:00
-- url     : https://prove2.me/submissions/7c7408f3-8e2e-43c6-b506-b598b6afbaa8

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_pairing_add_left
import Theorems.Thm_O3_Stage2RouteD_pairing_add_right
import Theorems.Thm_O3_Stage2RouteD_pairing_smul_left
import Theorems.Thm_O3_Stage2RouteD_pairing_smul_right
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_quadratic_fenchel_lower
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_comm
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.Stage2RouteD.dualityMap_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {p q σ : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x h a c : Point d)
    (_hσ : 0 ≤ σ)
    (hconst : (q - 1) * σ = 1)
    (hfenchelX :
      pairing a x - quadraticRegularizer q 0 a = quadraticRegularizer p 0 x)
    (hpairC : pairing c h = (lpNorm p h) ^ (2 : ℕ))
    (hnormStep : lpNorm q (σ • c) = σ * lpNorm p h)
    (hsmooth :
      quadraticRegularizer q 0 (a + σ • c) ≤
        quadraticRegularizer q 0 a + pairing x (σ • c) +
          ((q - 1) / 2) * (lpNorm q (σ • c)) ^ (2 : ℕ)) :
    quadraticRegularizer p 0 (x + h) ≥
      quadraticRegularizer p 0 x + pairing a h +
        (σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by
  have hfy := quadratic_fenchel_lower hpq (x + h) (a + σ • c)
  rw [pairing_add_left, pairing_add_right, pairing_add_right,
    pairing_smul_left] at hfy
  rw [hnormStep] at hsmooth
  have hcx : σ * pairing c x = pairing x (σ • c) := by
    rw [pairing_smul_right, pairing_comm]
  have hcoef :
      ((q - 1) / 2) * (σ * lpNorm p h) ^ (2 : ℕ) =
        (σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by
    calc
      ((q - 1) / 2) * (σ * lpNorm p h) ^ (2 : ℕ) =
          (((q - 1) * σ) * σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by ring
      _ = (σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by rw [hconst]; ring
  simp only [quadraticRegularizer, sub_zero] at hfenchelX hfy hsmooth ⊢
  rw [hcx, pairing_smul_left, hpairC] at hfy
  rw [hcoef] at hsmooth
  nlinarith
end O3.Stage2RouteD
