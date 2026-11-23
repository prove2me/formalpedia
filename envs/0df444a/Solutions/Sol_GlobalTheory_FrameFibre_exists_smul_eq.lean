-- Prove2me | solution 1 for GlobalTheory.FrameFibre.exists_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:49.162252+00:00
-- url     : https://prove2.me/submissions/73fed634-953f-4b2b-9e95-6c497cfa004f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
namespace GlobalTheory.FrameFibre
theorem _root_.solution {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hspan : Submodule.span E (Set.range φ) = ⊤) (u : Fin r → E) :
    ∃ (c : 𝓞 E) (v : L), c ≠ 0 ∧ (c : E) • u = φ v := by
  have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ⟨1, v, one_ne_zero, by simp⟩
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, v, hc, hv⟩ := hx
    obtain ⟨d, w, hd, hw⟩ := hy
    refine ⟨c * d, d • v + c • w, mul_ne_zero hc hd, ?_⟩
    rw [map_add, map_smul, map_smul, ← hv, ← hw]
    ext k
    simp [Algebra.smul_def]
    ring
  | smul a x _ hx =>
    obtain ⟨c, v, hc, hv⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd0
    refine ⟨c * d, n • v, mul_ne_zero hc hd0, ?_⟩
    rw [map_smul, ← hv]
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
    rw [Algebra.smul_def]
    field_simp
end GlobalTheory.FrameFibre
