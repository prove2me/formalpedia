-- Prove2me | solution 1 for GlobalTheory.JetSer.fnVal_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:30.390152+00:00
-- url     : https://prove2.me/submissions/3795e27c-329d-48fe-80e1-7d5ca143a6d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Theorems.Thm_GlobalTheory_JetSer_fnVal_eq_fnValHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.JetSer
variable {A : Type} [CommRing A] {X : Scheme.{0}}
namespace GlobalTheory.JetSer
theorem _root_.solution {Y : Scheme.{0}} (p : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ q ⁻¹ᵁ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(Y, V)) :
    ⊤ ≤ (p ≫ q) ⁻¹ᵁ V ∧ fnVal (p ≫ q) V f = fnVal p U ((q.appLE V U hUV).hom f) := by
  have h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V := fun z _ => by
    have : p z ∈ q ⁻¹ᵁ V := hUV (h trivial)
    simpa using this
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.appLE_comp_appLE p q V U ⊤ hUV h]
  rfl
end GlobalTheory.JetSer
