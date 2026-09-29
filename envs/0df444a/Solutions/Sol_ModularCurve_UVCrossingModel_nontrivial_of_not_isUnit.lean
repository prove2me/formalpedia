-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.nontrivial_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ae99fcb6-3f96-5636-ac9c-f29ae9d9bb4d

import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit

open ModularCurve ModularCurve.UVCrossingModel

theorem solution {W : Type*} [CommRing W] {π : W} (hπ : ¬IsUnit π) :
    Nontrivial (UVCrossingModel W π) :=
  by
  refine Ideal.Quotient.nontrivial_iff.mpr fun htop => hπ ?_
  have h1 : (1 : MvPowerSeries (Fin 2) W) ∈ uvCrossingIdeal W π := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.mp h1
  have hcc := congrArg (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)) hf
  simp only [map_mul, map_sub, map_one, MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_C, zero_mul, zero_sub, mul_neg] at hcc
  refine IsUnit.of_mul_eq_one (-(MvPowerSeries.constantCoeff f)) ?_
  rw [mul_comm, neg_mul]
  exact hcc

end S_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit (solution)
