-- Prove2me | solution 1 for ModularCurve.relfinrank_full_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ec637fde-3fa5-5d1c-8df4-999b6d262557

import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem
import Mathlib.FieldTheory.Relrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_full_eq_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_relfinrank_full_eq_mul.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand_one_apply jq jqN modularFunctionFieldFull jqd_mem_full finrank_adjoin_jqN_prime_of_not_mem finrank_adjoin_jqN_pow_succ_of_not_mem"
namespace W1
p2m_open "ModularCurve"

private theorem jqN_congr' {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) : jqN n = jqN m := by
  subst h; rfl

private theorem w1_relfinrank_insert (E : IntermediateField ℚ (LaurentSeries ℚ))
    (α : LaurentSeries ℚ) :
    IntermediateField.relfinrank E
      (IntermediateField.adjoin ℚ (insert α (E : Set (LaurentSeries ℚ))))
      = Module.finrank E
          (IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ))) := by
  have h : E ≤ IntermediateField.adjoin ℚ (insert α (E : Set (LaurentSeries ℚ))) :=
    fun x hx => IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ hx)
  have hEq : IntermediateField.adjoin E (insert α (E : Set (LaurentSeries ℚ)))
      = IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ)) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | hxE)
      · exact IntermediateField.subset_adjoin _ _ rfl
      · exact (IntermediateField.adjoin E _).algebraMap_mem (⟨x, hxE⟩ : E)
    · exact IntermediateField.adjoin.mono _ _ _
        (Set.singleton_subset_iff.mpr (Set.mem_insert α _))
  rw [IntermediateField.relfinrank_eq_finrank_of_le h,
    IntermediateField.extendScalars_adjoin h, hEq]

end ModularCurve.W1

namespace ModularCurve p2m_export "ModularCurve" "qExpand_one_apply jq jqN modularFunctionFieldFull jqd_mem_full finrank_adjoin_jqN_prime_of_not_mem finrank_adjoin_jqN_pow_succ_of_not_mem" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.relfinrank_full_eq_mul (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ)
    (hup : modularFunctionFieldFull (M * p ^ (a + 1)) =
      IntermediateField.adjoin ℚ
        (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) :
          Set (LaurentSeries ℚ))))
    (hnm : jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a)) :
    IntermediateField.relfinrank (modularFunctionFieldFull (M * p ^ a))
      (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p := by
  rw [hup, ModularCurve.W1.w1_relfinrank_insert]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [if_pos rfl]
    have e1 : p ^ (0 + 1) = p := by rw [zero_add, pow_one]
    have hj : jq ∈ modularFunctionFieldFull (M * p ^ 0) := by
      have h1 := jqd_mem_full (M * p ^ 0) (one_dvd _)
      rwa [qExpand_one_apply] at h1
    rw [ModularCurve.W1.jqN_congr' e1]
    rw [ModularCurve.W1.jqN_congr' e1] at hnm
    exact ModularCurve.finrank_adjoin_jqN_prime_of_not_mem _ hj p hnm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    rw [if_neg (Nat.succ_ne_zero k)]
    refine ModularCurve.finrank_adjoin_jqN_pow_succ_of_not_mem _ p k ?_ ?_ hnm
    · exact jqd_mem_full _ (Dvd.dvd.mul_left (pow_dvd_pow p (Nat.le_succ k)) M)
    · exact jqd_mem_full _ (dvd_mul_left _ _)

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_relfinrank_full_eq_mul.ModularCurve in

theorem solution (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hup : modularFunctionFieldFull (M * p ^ (a + 1)) = IntermediateField.adjoin ℚ (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)))) (hnm : jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a)) : IntermediateField.relfinrank (modularFunctionFieldFull (M * p ^ a)) (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p :=
  ModularCurve.relfinrank_full_eq_mul M p a hup hnm

#print axioms solution

end S_ModularCurve_relfinrank_full_eq_mul
end P2MW
export P2MW.S_ModularCurve_relfinrank_full_eq_mul (solution)
