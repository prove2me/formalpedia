-- Prove2me | solution 1 for OAI.PoissonChildCRT.sum_child_row_label_with_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:23.301268+00:00
-- url     : https://prove2.me/submissions/b6de1d46-c3de-414b-a95e-a44c22f58ac7

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_PoissonChildCRT_child_row_label_with_mask

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
theorem _root_.solution
    (S : Finset ℕ) (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ)
    (b0 t g e r d k J C v : ℕ) (hg : g = e * r) :
    (∑ n ∈ S, a n *
      (mask n (b0 * t) * mask n g *
        ((χ n (e : ZMod n))⁻¹ * χ n (d : ZMod n) * χ n (k : ZMod n) *
          (χ n ((J * C : ℕ) : ZMod n)) ^ 4 *
          (χ n (v : ZMod n)) ^ 4))) =
    (∑ n ∈ S, a n *
      (mask n (b0 * t * r) *
        (χ n ((d * e * k : ℕ) : ZMod n) *
          (χ n ((J * C * e * v : ℕ) : ZMod n)) ^ 4))) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [child_row_label_with_mask n (χ n) (hχ n) b0 t g e r d k J C v hg]
end OAI.PoissonChildCRT
