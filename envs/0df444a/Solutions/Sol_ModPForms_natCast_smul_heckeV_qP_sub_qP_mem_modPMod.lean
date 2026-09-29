-- Prove2me | solution 1 for ModPForms.natCast_smul_heckeV_qP_sub_qP_mem_modPMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b3806d00-bae3-57a4-aea2-cf362ba2c35e

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_SwdAlgebra
import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Theorems.Thm_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve

namespace FltWs24
namespace E2L

theorem sum_divisors_filter_dvd {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : n ≠ 0) (hℓn : ℓ ∣ n) :
    ∑ d ∈ n.divisors.filter (fun d => ℓ ∣ d), (d : ℤ) = (ℓ : ℤ) * ∑ e ∈ (n / ℓ).divisors, (e : ℤ) := by
  obtain ⟨m, rfl⟩ := hℓn
  have hm : m ≠ 0 := fun h => hn (by rw [h, mul_zero])
  rw [Nat.mul_div_cancel_left m hℓ.pos, Finset.mul_sum]

  refine Finset.sum_nbij' (fun d => d / ℓ) (fun e => ℓ * e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, -⟩, ⟨c, rfl⟩⟩ := hd
    rw [Nat.mem_divisors, Nat.mul_div_cancel_left c hℓ.pos]
    exact ⟨(Nat.mul_dvd_mul_iff_left hℓ.pos).mp hdn, hm⟩
  · intro e he
    rw [Nat.mem_divisors] at he
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_dvd_mul_left ℓ he.1, mul_ne_zero hℓ.ne_zero hm⟩, dvd_mul_right ℓ e⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2
  · intro e _
    exact Nat.mul_div_cancel_left e hℓ.pos
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨c, rfl⟩ := hd.2
    rw [Nat.mul_div_cancel_left c hℓ.pos]
    push_cast
    ring

theorem sum_divisors_eq (ℓ : ℕ) (hℓ : ℓ.Prime) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (d : ℤ) =
      (sigmaPrimeTo ℓ n : ℤ) + (ℓ : ℤ) * (if ℓ ∣ n then ∑ e ∈ (n / ℓ).divisors, (e : ℤ) else 0) := by
  unfold sigmaPrimeTo
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => ℓ ∣ d), add_comm]
  congr 1
  split_ifs with h
  · exact sum_divisors_filter_dvd hℓ hn h
  · rw [mul_zero]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact absurd (dvd_trans hd.2 hd.1.1) h

theorem coeff_qP (F : Type) [Field F] (n : ℕ) :
    PowerSeries.coeff n (SwdAlgebra.qP F) =
      ((if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ) : ℤ) : F) := by
  unfold SwdAlgebra.qP
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]

theorem smul_heckeV_qP_sub_qP_eq (ℓ : ℕ) (hℓ : ℓ.Prime) (F : Type) [Field F] :
    (ℓ : F) • PowerSeries.heckeV ℓ (SwdAlgebra.qP F) - SwdAlgebra.qP F =
      PowerSeries.mk fun n => ((eisensteinTwoCoeff ℓ n : ℤ) : F) := by
  ext n
  simp only [map_sub, map_smul, PowerSeries.coeff_heckeV, PowerSeries.coeff_mk, smul_eq_mul, coeff_qP]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [dvd_zero, if_true, Nat.zero_div, eisensteinTwoCoeff_zero]
    push_cast
    ring
  · rw [if_neg hn, eisensteinTwoCoeff_of_ne_zero ℓ hn, sum_divisors_eq ℓ hℓ hn]
    by_cases h : ℓ ∣ n
    · have hq : n / ℓ ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h) hℓ.pos).ne'
      rw [if_pos h, if_pos h, if_neg hq]
      push_cast
      ring
    · rw [if_neg h, if_neg h]
      push_cast
      ring

end FltWs24.E2L

open FltWs24.E2L in
theorem solution (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] :
    (ℓ : F) • PowerSeries.heckeV ℓ (SwdAlgebra.qP F) - SwdAlgebra.qP F ∈ ModPForms.modPMod ℓ 2 F := by
  rw [smul_heckeV_qP_sub_qP_eq ℓ Fact.out F]
  obtain ⟨E, hE⟩ := exists_modularForm_qCoeff_eq_eisensteinTwoCoeff ℓ
  unfold ModPForms.modPMod
  exact Submodule.subset_span ⟨E, fun n => eisensteinTwoCoeff ℓ n, hE, rfl⟩

end S_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod
end P2MW
export P2MW.S_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod (solution)
