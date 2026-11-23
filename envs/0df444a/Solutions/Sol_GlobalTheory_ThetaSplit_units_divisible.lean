-- Prove2me | solution 1 for GlobalTheory.ThetaSplit.units_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:46.097747+00:00
-- url     : https://prove2.me/submissions/358348a6-1e04-4fa0-aa5b-b7dd8cde3262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit
namespace GlobalTheory.ThetaSplit
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n) (y : Γ(Sp k, ⊤)ˣ) :
    ∃ x : Γ(Sp k, ⊤)ˣ, x ^ n = y := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (e y) hn
  have h : e.symm x ^ n = y := by rw [← map_pow, hx, RingEquiv.symm_apply_apply]
  have hu : IsUnit (e.symm x) := (isUnit_pow_iff hn.ne').1 (h ▸ y.isUnit)
  exact ⟨hu.unit, Units.ext h⟩
end GlobalTheory.ThetaSplit
