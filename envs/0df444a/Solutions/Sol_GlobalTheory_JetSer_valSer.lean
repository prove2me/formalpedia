-- Prove2me | solution 1 for GlobalTheory.JetSer.valSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:24:53.96089+00:00
-- url     : https://prove2.me/submissions/b2c99d3e-b253-4bac-a441-3f1c0d21ac2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
import Theorems.Thm_GlobalTheory_JetSer_valSer_germ_fnVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution : ValSerSt := by
  intro A _ X L hL j z Ψ _ hΨ
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Ψ) (fun ψ => ψ.1) (fun _ => j) (fun _ _ _ => rfl)
    (fun ψ => hΨ ψ.1 ψ.2 (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial))
  refine ⟨J, hJ, fun Y K _ φ ε t r hr => ?_⟩
  have hU : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j) := fun y hy => Set.mem_iInter.2 fun k => hΨ _ (hr k) hy
  rw [val_of t r z J (fun _ => j) (fun k => e ⟨_, hr k⟩)]
  exact (gs_unit r z _ (hU (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)) _).symm.trans
    (valSer_germ_fnVal r _ hU z _).symm
end GlobalTheory.JetSer
