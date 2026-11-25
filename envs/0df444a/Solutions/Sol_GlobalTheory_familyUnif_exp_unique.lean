-- Prove2me | solution 1 for GlobalTheory.familyUnif_exp_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:50.004099+00:00
-- url     : https://prove2.me/submissions/736e126a-96c8-498a-91f3-37e10472599b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Theorems.Thm_GlobalTheory_ExpUniqFamily_isHolTo_ex
import Theorems.Thm_GlobalTheory_ExpUniqFamily_fibrewise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i j P P' hP hP' hu
  obtain ⟨h, gam, h1, h2, h3, h4⟩ := ExpUniqFamily.fibrewise Xo.univ.t (U.Di i) (U.Di j) ty P P' hP hP' _ _ hu
    (U.ex i P) (U.ex j P') (U.ex_add i P hP) (U.ex_add j P' hP') (U.ex_ker i P hP) (U.ex_ker j P' hP')
    (U.ex_lin i P hP) (U.ex_lin j P' hP') (U.ex_weil i P hP) (U.ex_weil j P' hP')
    (ExpUniqFamily.isHolTo_ex U i P hP) (ExpUniqFamily.isHolTo_ex U j P' hP') (U.ex_diff i P hP) (U.ex_diff j P' hP')
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  exact ⟨h, gam, h1, h2, h3,
    fun a ha => h4 l.M _ _ _ hM (U.ex_eta i P hP a ha) (U.ex_eta j P' hP' a ha),
    fun a => h4 l.A _ _ _ l.A_pos (U.ex_etaA i P hP a) (U.ex_etaA j P' hP' a)⟩
end GlobalTheory
