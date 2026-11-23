-- Prove2me | solution 1 for GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:22.420116+00:00
-- url     : https://prove2.me/submissions/b704e68a-339e-4866-ac0d-e5798ed36ae8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution (R : Type v) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Algebra K R] (L : Type w) [Field L] [Algebra R L]
    [IsFractionRing R L] [Algebra K L] [IsScalarTower K R L]
    (hres : ∀ r : R, ∃ c : K, ¬ IsUnit (r - algebraMap K R c)) : IsIntegrallyClosedIn K L := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap K L).injective, fun {x} hx ↦ ?_⟩
  have key : ∀ y : L, IsIntegral K y → ∃ r : R, algebraMap R L r = y := fun y hy ↦
    IsIntegrallyClosed.algebraMap_eq_of_integral (hy.tower_top (A := R))
  obtain ⟨r, rfl⟩ := key x hx
  obtain ⟨c, hc⟩ := hres r
  refine ⟨c, ?_⟩
  by_contra hne
  have h0 : algebraMap R L r - algebraMap K L c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have halg : IsIntegral K (algebraMap R L r - algebraMap K L c)⁻¹ :=
    (hx.sub isIntegral_algebraMap).isAlgebraic.inv.isIntegral
  obtain ⟨s, hs⟩ := key _ halg
  refine hc (IsUnit.of_mul_eq_one s (IsFractionRing.injective R L ?_))
  rw [map_mul, map_sub, hs, ← IsScalarTower.algebraMap_apply, map_one, mul_inv_cancel₀ h0]
end GlobalTheory.OnePoint
