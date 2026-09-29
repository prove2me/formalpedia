-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5669b0fa-023d-5171-8ee2-fa15687611a5

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel IgusaScheme.jFull IgusaScheme.chartAlgFin IgusaScheme modularFunctionFieldFull modularUnitSeries modularUnitSeries_mem_chartAlgFin_int modularUnitSeries_mem_modularFunctionFieldFull"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "comp"
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

private theorem modularUnitSeries_mem_chartAlgFin_mul
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q)) :
    (⟨modularUnitSeries q, hmem⟩ : ↥(modularFunctionFieldFull (N₀ * q))) ∈ IgusaScheme.chartAlgFin (N₀ * q) q ∧
      ((q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * (⟨modularUnitSeries q, hmem⟩ : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹) ∈ IgusaScheme.chartAlgFin (N₀ * q) q := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
    apply IntermediateField.adjoin.mono
    rintro x ⟨d, hd, hdq, rfl⟩
    exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
  have hmemq : modularUnitSeries q ∈ modularFunctionFieldFull q :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q

  obtain ⟨h1, h2⟩ := ModularCurve.modularUnitSeries_mem_chartAlgFin_int q hmemq

  let ι : ↥(modularFunctionFieldFull q) →+* ↥(modularFunctionFieldFull (N₀ * q)) :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιu : ι ⟨modularUnitSeries q, hmemq⟩ = ⟨modularUnitSeries q, hmem⟩ := rfl
  have hιj : ι (IgusaScheme.jFull q) = IgusaScheme.jFull (N₀ * q) := rfl

  have key : ∀ x : ↥(modularFunctionFieldFull q),
      x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q) →
        ι x ∈ IgusaScheme.chartAlgFin (N₀ * q) q := by
    intro x hx
    let A : Subalgebra ℤ ↥(modularFunctionFieldFull q) := Algebra.adjoin ℤ {IgusaScheme.jFull q}
    let B : Subalgebra ℤ ↥(modularFunctionFieldFull (N₀ * q)) := Algebra.adjoin ℤ {IgusaScheme.jFull (N₀ * q)}
    have hx' : IsIntegral A x := hx
    have hAB : ∀ y : ↥(modularFunctionFieldFull q), y ∈ A → ι y ∈ B := by
      intro y hy
      have hy' : y ∈ Subring.closure {IgusaScheme.jFull q} := by
        have : A = subalgebraOfSubring (Subring.closure {IgusaScheme.jFull q}) := Algebra.adjoin_int _
        rw [this] at hy
        exact hy
      have hcl : Subring.closure {IgusaScheme.jFull q} ≤ B.toSubring.comap ι :=
        Subring.closure_le.mpr (Set.singleton_subset_iff.mpr (by
          show ι (IgusaScheme.jFull q) ∈ B
          rw [hιj]
          exact Algebra.subset_adjoin rfl))
      exact hcl hy'
    let φ : A →+* B := (ι.comp A.val.toRingHom).codRestrict B (fun y => hAB y y.2)
    have hB : IsIntegral B (ι x) :=
      hx'.map_of_comp_eq φ ι (by ext; rfl)

    have hC := AlgebraicCurve.TwoChartIntegralModel.chartAlg_le_chartAlg ℤ ↥(modularFunctionFieldFull (N₀ * q))
      ↥(GaloisRep.ratLocalizedAt q) {IgusaScheme.jFull (N₀ * q)} (x := ι x) hB
    exact hC
  refine ⟨?_, ?_⟩
  · simpa only [hιu] using key _ h1
  · have := key _ h2
    rwa [map_mul, map_pow, map_inv₀, map_natCast, hιu] at this

end ModularCurve.DRModelPackageLevel

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q)) :
    (⟨modularUnitSeries q, hmem⟩ : ↥(modularFunctionFieldFull (N₀ * q))) ∈ IgusaScheme.chartAlgFin (N₀ * q) q ∧
      ((q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * (⟨modularUnitSeries q, hmem⟩ : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹) ∈ IgusaScheme.chartAlgFin (N₀ * q) q :=
  ModularCurve.DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul N₀ q hqN hmem

end S_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul (solution)
