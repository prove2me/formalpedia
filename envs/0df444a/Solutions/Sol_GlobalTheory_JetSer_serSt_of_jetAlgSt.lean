-- Prove2me | solution 1 for GlobalTheory.JetSer.serSt_of_jetAlgSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:16.596316+00:00
-- url     : https://prove2.me/submissions/05d00309-8f37-49e0-908b-46f5424c3299

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Theorems.Thm_GlobalTheory_JetSer_fnVal_eq_fnValHom
import Theorems.Thm_GlobalTheory_JetSer_top_le_preimage_comp
import Theorems.Thm_GlobalTheory_JetSer_fnVal_specMap
import Theorems.Thm_GlobalTheory_JetSer_fnVal_comp
import Theorems.Thm_GlobalTheory_JetSer_fnVal_res
import Theorems.Thm_GlobalTheory_JetSer_top_le_preimage_jet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


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
namespace GlobalTheory.JetSer
theorem _root_.solution : JetAlgSt → SerSt := by
  intro hJ R _ κ _ X p hp U h0
  have hU := top_le_preimage_jet p hp U h0
  obtain ⟨hτ, -, hinj, hex, -⟩ := hJ R κ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : ∀ f : Γ(X, U), ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = fnValHom (p m) U (hU m) f := by
      intro f
      refine hex (fun m => fnValHom (p m) U (hU m) f) fun m => ?_
      have := fnVal_specMap (jetTruncR R κ m).toRingHom (p (m + 1)) U (hU _) f
      rw [← spMap_left, hp m, fnVal_eq_fnValHom _ _ (hU _), fnVal_eq_fnValHom _ _ (hU _)] at this
      exact this.symm
    choose T hT using hc
    choose τ hτ₁ hτ₂ using hτ
    refine ⟨{ toFun := T
              map_one' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_one, map_one]
              map_mul' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_mul, map_mul, hτ₁, hτ₁, hT, hT]
              map_zero' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_zero, map_zero]
              map_add' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_add, map_add, hτ₁, hτ₁, hT, hT] }, fun f g => ⟨fun H => ?_, fun H m => ?_⟩⟩
    · exact hinj _ _ fun m => by
        rw [← (H m).2, fnVal_eq_fnValHom _ _ (hU m)]
        exact (hT f m).symm
    · refine ⟨hU m, ?_⟩
      rw [H, fnVal_eq_fnValHom _ _ (hU m)]
      exact (hT f m).symm
  · intro V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_res (p m) U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro Y q V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_comp (p m) q U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro κ' _ b ψ hb hψ f g H m
    refine ⟨top_le_preimage_comp _ _ U (hU m), ?_⟩
    have := fnVal_specMap (ψ m).toRingHom (p m) U (hU m) f
    rw [(H m).2] at this
    exact this.trans (((hJ R κ').2.2.2.2 κ b hb m).2 (ψ m) (hψ m) g)
end GlobalTheory.JetSer
