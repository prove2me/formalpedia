-- Prove2me | solution 1 for GlobalTheory.PureType.period_w0_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:18:42.489888+00:00
-- url     : https://prove2.me/submissions/44f3d451-d49b-4aa1-b296-1cd8447093ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase
import Theorems.Thm_GlobalTheory_PureType_period_rt_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.PureType
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
namespace GlobalTheory.PureType
theorem _root_.solution {ρ : ℂ} {a : D.La} (ha : a ∈ lat hP ρ) : Pe (H.w0 • a) = ((1 + ρ) / 2) • Pe a := by
  have h : (2 : ℂ) • Pe (H.w0 • a) = (1 + ρ) • Pe a := by
    have e : H.w0 • a + H.w0 • a = a + H.rt • a := by
      rw [← two_smul (𝓞 E), ← mul_smul, H.two_weight_eq_one_add_root, add_smul, one_smul]
    rw [two_smul, ← map_add, e, map_add, period_rt_smul hP ha, add_smul, one_smul]
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul]
  norm_num
end GlobalTheory.PureType
