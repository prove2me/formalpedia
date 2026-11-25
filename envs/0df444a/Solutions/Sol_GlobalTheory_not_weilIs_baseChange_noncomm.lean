-- Prove2me | solution 1 for GlobalTheory.not_weilIs_baseChange_noncomm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:48.669893+00:00
-- url     : https://prove2.me/submissions/d6f0365c-d1c4-4310-acd8-8acdfcb53511

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
import Theorems.Thm_GlobalTheory_WeilNoncomm_oneChart_isLB
import Theorems.Thm_GlobalTheory_WeilNoncomm_twoCharts_isLB
import Theorems.Thm_GlobalTheory_WeilNoncomm_twoCharts_iso
import Theorems.Thm_GlobalTheory_WeilNoncomm_weilIs_oneChart
import Theorems.Thm_GlobalTheory_WeilNoncomm_not_weilIs_heis
import Theorems.Thm_GlobalTheory_WeilNoncomm_unit_heis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso


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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open WeilNoncomm
namespace GlobalTheory
theorem _root_.solution : ¬ ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (_ : IsGrpPullback G' G f φ) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S') (n : ℤ) (x' y' : Over.mk t ⟶ G') (x y : Over.mk (t ≫ f) ⟶ G) (c : Rˣ), x.left = x'.left ≫ φ → y.left = y'.left ≫ φ → (Out.WeilIs G' L' n x' y' (unitOn c) ↔ Out.WeilIs G L n x y (unitOn c)) := by
  intro H
  let _ := heisGrp (Sp (ZMod 3))
  have : IsMonHom (Iso.refl (heisScheme (Sp (ZMod 3)))).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have hp := isGrpPullback_of_iso (Iso.refl (heisScheme (Sp (ZMod 3))))
  have u1 : unitOn (1 : (ZMod 3)ˣ) = 1 := map_one _
  have h := H _ _ _ _ _ _ hp _ _ (oneChart_isLB _) (twoCharts_isLB _) (twoCharts_iso _) (ZMod 3) (𝟙 _) 1
    (heisMk _ 1 0 0) (heisMk _ 0 1 0) (pushPt hp.1.w (heisMk (Over.mk (𝟙 _)) 1 0 0))
    (pushPt hp.1.w (heisMk (Over.mk (𝟙 _)) 0 1 0)) 1 rfl rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : IsUnit (2 : Γ(Sp (ZMod 3), ⊤)) := by
    have := (show IsUnit (2 : ZMod 3) from IsUnit.of_mul_eq_one 2 rfl).map (Scheme.ΓSpecIso (CommRingCat.of (ZMod 3))).inv.hom
    rwa [map_ofNat] at this
  refine not_weilIs_heis (Over.mk (𝟙 (Sp (ZMod 3)))) (⊥ : PrimeSpectrum (ZMod 3)) h2 _ (h.2 ?_)
  rw [u1]
  have : IsIso (⊤ : (Sp (ZMod 3)).Opens).ι := inferInstanceAs (IsIso (Sp (ZMod 3)).topIso.hom)
  have : IsIso (Out.overRes (T := Over.mk (𝟙 (Sp (ZMod 3)) ≫ 𝟙 _)) ⊤).hom :=
    inferInstanceAs (IsIso ((⊤ : (Sp (ZMod 3)).Opens).ι ≫ 𝟙 _ ≫ 𝟙 _))
  exact weilIs_oneChart _ 1 _ _ unit_heis
end GlobalTheory
