-- Prove2me | solution 1 for GlobalTheory.LieExt.detCond_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:14.171484+00:00
-- url     : https://prove2.me/submissions/f9665f54-b494-49bc-bc9a-22f213f5f398

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LieMultIffFinrank
import Theorems.Thm_GlobalTheory_LieExt_lieMult_extend_iff
import Theorems.Thm_GlobalTheory_LieExt_exists_comp_eq

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.LieExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LieExt
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (D : Geo.Tor.Datum H)
    {k K : Type} [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] (act : Geo.Tor.OAct (𝓞 E) G) {ρ : k} (h : Geo.Tor.DetCond D act (𝟙 _) ρ) :
    Geo.Tor.DetCond D act (Geo.Tor.spMap φ) (φ ρ) := by
  intro τ
  obtain ⟨χ, rfl⟩ := exists_comp_eq φ τ
  rw [lieMult_extend_iff, lieMult_extend_iff]
  exact ⟨fun e => (h χ).1 (φ.injective e), fun e => (h χ).2 fun e' => e (congrArg φ e')⟩
end GlobalTheory.LieExt
