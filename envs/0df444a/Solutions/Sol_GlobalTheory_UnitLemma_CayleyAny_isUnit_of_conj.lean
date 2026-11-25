-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyAny.isUnit_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:25.191142+00:00
-- url     : https://prove2.me/submissions/27c4689d-1021-41ac-9e08-5939aaae983e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyAny
open GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyAny
theorem _root_.solution (K : UQ) (x y : K.O) (h : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hy : IsUnit y) : IsUnit x := by
  obtain ⟨u, rfl⟩ := hy
  obtain ⟨w, hw⟩ := K.c_int (↑u⁻¹ : K.O)
  have h1 : K.c (algebraMap K.O K.E (u : K.O)) = algebraMap K.O K.E x := by rw [← h, K.c_c]
  have h2 : algebraMap K.O K.E (x * w) = 1 := by
    rw [map_mul, ← h1, ← hw, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [← map_one (algebraMap K.O K.E)] at h2
  exact IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective K.O K.E h2)
end GlobalTheory.UnitLemma.CayleyAny
