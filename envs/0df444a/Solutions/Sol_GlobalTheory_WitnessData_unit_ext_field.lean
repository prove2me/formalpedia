-- Prove2me | solution 1 for GlobalTheory.WitnessData.unit_ext_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:43.843954+00:00
-- url     : https://prove2.me/submissions/dad5744e-9cd4-4fea-af8f-14d4dc38fced

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WitnessData
namespace GlobalTheory.WitnessData
theorem _root_.solution {K F : Type} [Field K] [Field F] (i : K →+* F) {V : (Sp K).Opens} {a b : Γ(Sp K, V)ˣ}
    (h : ∀ z, spMap i z ∈ V → gm (spMap i) z V a = gm (spMap i) z V b) : a = b := by
  have : QuasiCompact (spMap i) := inferInstanceAs (QuasiCompact (Spec.map _))
  have : IsDominant (spMap i) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 i.injective).le.trans bot_le)⟩
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap i)
  have e : pullU (spMap i) V a = pullU (spMap i) V b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 _) _ z V hz, gm_pull (𝟙 _) _ z V hz, Category.id_comp]
    exact h z hz
  exact Units.ext ((spMap i).app_injective V (congrArg Units.val e))
end GlobalTheory.WitnessData
