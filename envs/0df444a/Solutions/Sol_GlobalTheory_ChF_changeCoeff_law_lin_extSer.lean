-- Prove2me | solution 1 for GlobalTheory.ChF.changeCoeff_law_lin_extSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:50.023801+00:00
-- url     : https://prove2.me/submissions/dc1f5e1e-f951-4608-a392-8898121f9a20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupLawJacobianExtensionChangeCoeff
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private lemma map_subst_single {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d) :
    MvPowerSeries.map β (sub ![x] f) =
      sub ![fun j => MvPowerSeries.map β (x j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by fin_cases i; exact hx j) f _ (fun i j => by fin_cases i; rfl)
private lemma constCoeff_subst_single {R : Type} [CommRing R] {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x] f) = 0 :=
  cc_sub _ (fun i j => by fin_cases i; exact hx j) f hf
private lemma isHomF_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ}
    (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (φ : Fin e → PS R 1 d)
    (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) (h : IsHomF F F' φ) :
    IsHomF (fun j => MvPowerSeries.map β (F j)) (fun j => MvPowerSeries.map β (F' j))
      (fun j => MvPowerSeries.map β (φ j)) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun j => by simp [MvPowerSeries.constantCoeff_map, h0], fun j => ?_⟩
  have := congrArg (MvPowerSeries.map β) (h1 j)
  simp only [ev_eq] at this ⊢
  rw [map_subst_single β _ hF, map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))
    (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))] at this
  simp only [map_subst_single β _ (cc_pt _), map_pt] at this
  exact this
private lemma lin_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ} (φ : Fin e → PS R 1 d) :
    lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β := by
  ext i j
  simp [lin, MvPowerSeries.coeff_map]
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  intro R S _ _ β
  refine ⟨fun d F => ⟨mapLaw β F, rfl⟩, fun d e φ => lin_map β φ, fun d g r F FB J Q h => ⟨?_, ?_, ?_⟩⟩
  · have hg : (fun j => MvPowerSeries.map β (gmF R r j)) = gmF S r := by
      funext j; simp [gmF]
    rw [← hg]
    exact isHomF_map β _ _ _ (fun j => by simp [gmF]) h.homI
  · exact isHomF_map β _ _ _ F.const h.homQ
  · rw [lin_map, lin_map]
    obtain ⟨h0, A', B', h1, h2, h3⟩ := h.exact
    refine ⟨?_, A'.map β, B'.map β, ?_, ?_, ?_⟩
    · rw [← Matrix.map_mul, h0]; simp
    · rw [← Matrix.map_mul, h1]; simp
    · rw [← Matrix.map_mul, h2]; simp
    · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add β), h3]; simp
end GlobalTheory.ChF
