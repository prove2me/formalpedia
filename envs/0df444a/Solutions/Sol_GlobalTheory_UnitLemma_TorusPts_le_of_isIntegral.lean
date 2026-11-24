-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TorusPts.le_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:14.553797+00:00
-- url     : https://prove2.me/submissions/78a60a9a-a3a6-4831-a50e-da3663a8c94f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TorusPts
namespace GlobalTheory.UnitLemma.TorusPts
theorem _root_.solution {K : UQ} {a : K.O} (ha : K.Small a) (n m : ℕ)
    (h : IsIntegral K.O (((algebraMap K.O K.E a) ^ n)⁻¹ * (algebraMap K.O K.E a) ^ m)) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff).1 h
  have ha0 : algebraMap K.O K.E a ≠ 0 := by
    simpa using ha.1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have h1 : algebraMap K.O K.E (a * (a ^ d * r)) = algebraMap K.O K.E 1 := by
    simp only [map_mul, map_pow, map_one, hr]
    field_simp
    ring
  have h2 := IsFractionRing.injective K.O K.E h1
  exact ha.2.1 (IsUnit.of_mul_eq_one _ h2)
end GlobalTheory.UnitLemma.TorusPts
