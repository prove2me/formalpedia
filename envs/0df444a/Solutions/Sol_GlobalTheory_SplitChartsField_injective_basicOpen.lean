-- Prove2me | solution 1 for GlobalTheory.SplitChartsField.injective_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:28.555277+00:00
-- url     : https://prove2.me/submissions/c4456f1c-6497-474c-8bf1-20f3cf2ef6d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitChartsTorusExtensionOverField
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul_zero
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_preimage_basicOpen
import Theorems.Thm_GlobalTheory_AffineThickening_app_rs
import Theorems.Thm_GlobalTheory_AffineThickening_exists_eq_pow_mul
import Theorems.Thm_GlobalTheory_AffineThickening_exists_pow_mul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.SplitChartsField
open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {B : Scheme.{0}}
  {i : splitTorus S X ⟶ G} {q : G.left ⟶ B} [IsAffineHom q] {V : B.Opens} (hi : IsMonHom i) (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.app V).hom c = a)
  (hinj : Function.Injective (q.app V).hom) (hS : Stable i (q ⁻¹ᵁ V))
include hi hV h₀ hS
omit hi h₀ hS
include hinj
namespace GlobalTheory.SplitChartsField
theorem _root_.solution (c : Γ(B, V)) : Function.Injective (q.app (B.basicOpen c)).hom := by
  have hle := B.basicOpen_le c
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c a rfl
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero (hV.preimage q) (q.preimage_mono hle) ((q.app V).hom c)
    ((q.app V).hom y) (Scheme.preimage_basicOpen _ _) (by rw [← app_rs q hle, hy, map_mul, ha, mul_zero])
  rw [← map_pow, ← map_mul, map_eq_zero_iff _ hinj] at hm
  have := congrArg (rs hle) hm
  rwa [map_mul, map_pow, map_zero, hy, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero, Units.mul_right_eq_zero] at this
end GlobalTheory.SplitChartsField
