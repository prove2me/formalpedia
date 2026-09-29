-- Prove2me | solution 1 for ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldC_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/19b26218-12c3-5777-98ee-9bb8dbe62ac6

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

theorem solution
    (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ) :
    ModularCurve.charLDegeneracyRoof κ N ℓ = ModularCurve.modularFunctionFieldC κ (N * ℓ) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpNℓ : ¬ p ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
    · exact hpN h1
    · exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h2)
  apply le_antisymm
  ·
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC κ p (N * ℓ) hpNℓ]
    unfold ModularCurve.charLDegeneracyRoof
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ModularCurve.jqModC_mem_full κ (N * ℓ)
    · exact ModularCurve.jqModCd_mem_full κ (N * ℓ) (dvd_mul_right N ℓ)
    · exact ModularCurve.jqModCd_mem_full κ (N * ℓ) (dvd_mul_left ℓ N)
    · exact ModularCurve.jqModCd_mem_full κ (N * ℓ) dvd_rfl
  ·
    unfold ModularCurve.modularFunctionFieldC ModularCurve.charLDegeneracyRoof
    apply IntermediateField.adjoin.mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))

#print axioms solution

end S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
end P2MW
export P2MW.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul (solution)
