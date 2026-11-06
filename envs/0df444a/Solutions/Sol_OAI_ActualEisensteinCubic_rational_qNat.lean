-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_qNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:47:47.286168+00:00
-- url     : https://prove2.me/submissions/af345e02-9202-4155-8512-89a0ee38a47c

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span


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
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (r : ℕ) (hr : r ≠ 0) :
    qNat (r : O) = r ^ 2 := by
  calc
    qNat (r : O) = Ideal.absNorm (Ideal.span {(r : O)}) :=
      qNat_eq_absNorm_span _
    _ = Nat.card (O ⧸ Ideal.span {(r : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = r ^ 2 := rational_modulus_card r hr
end OAI.ActualEisensteinCubic
