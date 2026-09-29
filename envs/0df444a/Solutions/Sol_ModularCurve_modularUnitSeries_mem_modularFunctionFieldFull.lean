-- Prove2me | solution 1 for ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bbb00a88-70a0-5648-8976-119669fb911b

import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

theorem solution (N : ℕ) [NeZero N] : ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionFieldFull N := by
  suffices H : ∀ n : ℕ, ∀ _ : NeZero n,
      ModularCurve.modularUnitSeries n ∈ ModularCurve.modularFunctionFieldFull n from
    H N ‹NeZero N›
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hNZ
    haveI := hNZ
    have hn : n ≠ 0 := NeZero.ne n
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [ModularCurve.modularUnitSeries_one]
      exact one_mem _
    · obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨M, rfl⟩ := hdvd
      have hM : M ≠ 0 := by rintro rfl; exact hn (mul_zero p)
      have hp0 : p ≠ 0 := hp.ne_zero
      haveI : NeZero p := ⟨hp0⟩
      haveI : NeZero M := ⟨hM⟩
      haveI : NeZero (p * M) := ⟨mul_ne_zero hp0 hM⟩
      haveI : Fact p.Prime := ⟨hp⟩
      rw [ModularCurve.modularUnitSeries_mul p M]
      refine mul_mem ?_ ?_
      · exact ModularCurve.full_degeneracy_le (dvd_mul_right p M)
          (ModularCurve.modularFunctionField_le_full p
            (ModularCurve.modularUnitSeries_mem_modularFunctionField p))
      · have hMlt : M < p * M :=
          (lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hM)).mpr hp.one_lt
        have hmem := ih M hMlt ⟨hM⟩
        have h2 : ModularCurve.qExpandₐ p (ModularCurve.modularUnitSeries M)
            ∈ (ModularCurve.modularFunctionFieldFull M).map (ModularCurve.qExpandₐ p) :=
          ⟨_, hmem, rfl⟩
        have h3 := ModularCurve.full_degeneracy_map_le M p h2
        rw [ModularCurve.qExpandₐ_apply] at h3
        exact ModularCurve.full_degeneracy_le (dvd_of_eq (mul_comm M p)) h3

end S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
end P2MW
export P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull (solution)
