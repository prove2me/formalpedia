-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.chartBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:54.294228+00:00
-- url     : https://prove2.me/submissions/29e7f619-f2e3-4b25-86a4-2c93abeb8baa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_surjective
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_mul
import Theorems.Thm_GlobalTheory_ChartBaseChange_isUnivChart_baseChange
import Theorems.Thm_GlobalTheory_ChartBaseChange_germEval_oneStandardPoint_self
import Theorems.Thm_GlobalTheory_ChartBaseChange_eval_standard_points_two
import Theorems.Thm_GlobalTheory_ChartBaseChange_eval_standard_points_three
import Theorems.Thm_GlobalTheory_ChartBaseChange_const_map
import Theorems.Thm_GlobalTheory_ChartBaseChange_hasSer_move
import Theorems.Thm_GlobalTheory_ChartBaseChange_rep_iff
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_move
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution : JetAlgSt → SerSt → ChartBCSt := by
  intro hJ _ R R' _ _ _ β G _ G' _ π hπ d x hx
  letI : Algebra R R' := β.toAlgebra
  have hπ' : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π := hπ
  choose x' hx' using fun m => push_surjective hπ' (spMap (jetCoeff R R' (Fin d) m) ≫ x m)
  refine ⟨x', isUnivChart_baseChange hπ' hx hx', ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF
    refine ⟨fun i => const_map (hF.1 i), fun n a b y z hy hz => ?_⟩
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a, b] ![y, z]
      (fun i => by fin_cases i; exacts [hy, hz])
    have H := hF.2 2 _ _ _ _ (ht 0) (ht 1)
    have hFe : addOf F (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 2) d 0) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1) = F :=
      funext fun i => eval_standard_points_two _
    rw [hFe] at H
    refine (rep_iff hπ' hJ hx' (pair_points_zero_constant hy.1 hz.1) hΘ H _).2 fun m => ?_
    rw [push_mul, MonObj.comp_mul, ← e 0 m, ← e 1 m]
    rfl
  · intro f f' α hf hα
    refine ⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
    have H := hα.2 1 _ _ (ht 0)
    have hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _
    rw [hFe] at H
    refine (rep_iff hπ' hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_
    rw [← Category.assoc, ← e 0 m]
    apply Over.OverMorphism.ext
    show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left
    rw [Category.assoc, Category.assoc, hf]
  · intro U f g hg n a y hy
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
    have H := hg 1 _ _ (ht 0)
    rw [germEval_oneStandardPoint_self] at H
    exact hasSer_move hΘ π _ _ (fun m => congrArg (fun k => k.left) (e 0 m)) U f g H
  · intro π₂ h1 h2 U f g hg n a b y z hy hz
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a, b] ![y, z]
      (fun i => by fin_cases i; exacts [hy, hz])
    have H := hg 2 _ _ _ _ (ht 0) (ht 1)
    rw [eval_standard_points_two] at H
    refine hasSer_move hΘ π₂ _ _ (fun m => ?_) U f g H
    rw [← Over.comp_left, comp_lift, ← e 0 m, ← e 1 m]
    apply Over.tensorObj_ext
    · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      rfl
  · intro π₃ h1 h2 h3 U f g hg n a b c y z w hy hz hw
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a, b, c] ![y, z, w]
      (fun i => by fin_cases i; exacts [hy, hz, hw])
    have H := hg 3 _ _ _ _ _ _ (ht 0) (ht 1) (ht 2)
    rw [eval_standard_points_three] at H
    refine hasSer_move hΘ π₃ _ _ (fun m => ?_) U f g H
    rw [← Over.comp_left, comp_lift, comp_lift, ← e 0 m, ← e 1 m, ← e 2 m]
    apply Over.tensorObj_ext
    · show _ ≫ (fst G _).left = _ ≫ (fst G _).left
      rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd G (G ⊗ G)).left = _ ≫ (snd G (G ⊗ G)).left
      apply Over.tensorObj_ext
      · show (_ ≫ (snd G (G ⊗ G)).left) ≫ (fst G G).left = (_ ≫ (snd G (G ⊗ G)).left) ≫ (fst G G).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, h2, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_fst, lift_snd_assoc, lift_fst]
        rfl
      · show (_ ≫ (snd G (G ⊗ G)).left) ≫ (snd G G).left = (_ ≫ (snd G (G ⊗ G)).left) ≫ (snd G G).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, h3, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, lift_snd_assoc, lift_snd]
        rfl
end GlobalTheory.ChartBaseChange
