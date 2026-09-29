-- Prove2me | solution 1 for ModularCurve.eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/887eeda9-802d-5a0f-9cb1-78fd8ff54bb0

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "modularFunctionFieldBar" namespace S1Aux end ModularCurve.S1Aux
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.S1Aux.ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  have hu : IsUnit (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F a⁻¹, v.algebraMap_mem' a⁻¹⟩, ?_⟩
    ext
    simp [ha]
  have := v.ord_coe_unit hu.unit
  simpa using this

theorem solution (N : ℕ) [NeZero N]
    {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (h1 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) = 1)
    (hP : Divisor.IsPrincipal (D' - D)) : D' = D := by
  obtain ⟨h, h0, hh⟩ := hP
  have hmem : h ∈ riemannRochSpace D := mem_riemannRochSpace_iff.mpr fun v => Or.inr (by
    have e := hh v
    have e' := hD' v
    rw [Finsupp.sub_apply] at e
    simp only [Finsupp.coe_zero, Pi.zero_apply] at e'
    linarith)
  have hone : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace D :=
    mem_riemannRochSpace_iff.mpr fun w => Or.inr (by rw [Place.ord_one]; have := hD w; simpa using this)
  have hne : (⟨1, hone⟩ : ↥(riemannRochSpace D)) ≠ 0 := by
    intro e; exact one_ne_zero (congrArg Subtype.val e)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h1 ⟨h, hmem⟩
  have e1 : a • (1 : modularFunctionFieldBar N) = h := by
    simpa using congrArg Subtype.val ha
  have hval : h = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a := by
    rw [Algebra.algebraMap_eq_smul_one]; exact e1.symm
  have ha0 : a ≠ 0 := by
    rintro rfl; apply h0; rw [hval, map_zero]
  ext v
  have e := hh v
  rw [Finsupp.sub_apply, hval, ModularCurve.S1Aux.ord_algebraMap v ha0] at e
  linarith

end S_ModularCurve_eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one
end P2MW
export P2MW.S_ModularCurve_eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one (solution)
