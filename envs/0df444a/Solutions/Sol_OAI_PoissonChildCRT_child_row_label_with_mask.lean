-- Prove2me | solution 1 for OAI.PoissonChildCRT.child_row_label_with_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:39.888557+00:00
-- url     : https://prove2.me/submissions/e2c7ff27-b5c1-464a-963d-2fdd8ac9e1f5

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_PoissonChildCRT_child_row_label_identity
import Theorems.Thm_OAI_PoissonChildCRT_mask_mul
import Theorems.Thm_OAI_PoissonChildCRT_mask_absorb_inv_char

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
namespace OAI.PoissonChildCRT
theorem _root_.solution (hχ : χ ^ 6 = 1)
    (b0 t g e r d k J C v : ℕ) (hg : g = e * r) :
    mask n (b0 * t) * mask n g *
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4)
      = mask n (b0 * t * r) *
        (χ ((d * e * k : ℕ) : ZMod n) *
          (χ ((J * C * e * v : ℕ) : ZMod n)) ^ 4) := by
  rw [hg, mask_mul n e r]
  have hmask : mask n (b0 * t) * (mask n e * mask n r) =
      mask n (b0 * t * r) * mask n e := by
    rw [mask_mul n (b0 * t) r]
    ring
  rw [hmask]
  have hprior : mask n e *
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) =
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) := by
    calc
      mask n e * ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
          (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4)
          = (mask n e * (χ (e : ZMod n))⁻¹) *
              (χ (d : ZMod n) * χ (k : ZMod n) *
                (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) := by ring
      _ = _ := by rw [mask_absorb_inv_char n χ e]; ring
  rw [mul_assoc, hprior, child_row_label_identity n χ hχ d e k J C v]
end OAI.PoissonChildCRT
