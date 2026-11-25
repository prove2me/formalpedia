-- Prove2me | solution 1 for GlobalTheory.ChartCmp.carries_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:35.526832+00:00
-- url     : https://prove2.me/submissions/eb81aeae-242e-4859-bf93-2c3d02894f35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculus
import Theorems.Thm_GlobalTheory_ChartCmp_CarryCalc_carries_iff
import Theorems.Thm_GlobalTheory_ChartCmp_CarryCalc_val_of_carries
import Theorems.Thm_GlobalTheory_ChartCmp_CarryCalc_carries_of_val
import Theorems.Thm_P2M_GlobalTheory_ChartCmp_CarryCalc_exists_good__51775dee39aa
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_zpow_of_sameSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp
open CarryCalc
namespace GlobalTheory.ChartCmp
theorem _root_.solution : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  intro X X' L' L F _ w hL' hL hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Y K _ φ ε g hg
    obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
    exact ⟨t, ht, (carries_iff w φ ε g t).2 hv⟩
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' hs _ _ _ _ Hg Hh
    have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
        (val g (𝟙 Y) y J' = val h (𝟙 Y) y J' ↔ val g' (𝟙 Y) y J = val h' (𝟙 Y) y J) := fun y J J' hJ hJ' => by
      rw [val_of_carries Hg (𝟙 Y) hJ hJ', val_of_carries Hh (𝟙 Y) hJ hJ',
        DVR.prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => fac w y J J' (𝟙 Y ≫ ψ)), mul_right_inj]
    refine ⟨fun C => corr_of_val hL fun y J hJ => ?_, fun C => corr_of_val hL' fun y J' hJ' => ?_⟩
    · obtain ⟨J', hJ'⟩ := exists_good' hL' y
      exact (key y J J' hJ hJ').1 (val_corr hJ' C _)
    · obtain ⟨J, hJ⟩ := exists_good' hL y
      exact (key y J J' hJ hJ').2 (val_corr hJ C _)
  · intro Y Z K _ φ ε g g' r g'' hg _ hg'' H C
    refine carries_of_val hL' hL hw (DVR.pullGen_isGen _ _ _ _ hg r) hg'' fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_pull hJ, val_pull hJ', val_of_carries H _ hJ hJ']
    simp only [Category.assoc]
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' p hg hh _ _ hp Hg Hh C
    refine carries_of_val hL' hL hw (DVR.mulGen_isGen _ _ _ _ _ _ _ hg hh) hp fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_mul hJ, val_mul hJ', val_of_carries Hg _ hJ hJ', val_of_carries Hh _ hJ hJ',
      Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
    rfl
  · intro Y K _ φ ε g g' H
    refine (carries_iff w φ _ _ _).2 fun Z r z p q hp hq => ?_
    refine (map_inv _ _).trans ((congrArg (·⁻¹) ((carries_iff w φ ε g g').1 H Z r z p q hp hq)).trans ?_)
    refine (mul_inv _ _).trans (congrArg₂ (· * ·) ?_ (map_inv _ _).symm)
    simp only [pw, zpow_neg, Finset.prod_inv_distrib]
end GlobalTheory.ChartCmp
