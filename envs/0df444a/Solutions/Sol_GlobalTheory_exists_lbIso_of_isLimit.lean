-- Prove2me | solution 1 for GlobalTheory.exists_lbIso_of_isLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:21:37.728907+00:00
-- url     : https://prove2.me/submissions/a17237c9-9b56-4e1e-9cad-6af9da3c8eec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_GlobalTheory_exists_gen_of_refinement
import Theorems.Thm_GlobalTheory_exists_units_of_isLimit
import Theorems.Thm_GlobalTheory_lb_div_isLB
import Theorems.Thm_GlobalTheory_gm_div_pull_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
include hc
namespace GlobalTheory
theorem _root_.solution {i : I} [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (M N : LB (D.obj i)) (hM : M.IsLB) (hN : N.IsLB) (h : LBIso (M.pull (π i)) (N.pull (π i))) :
    ∃ (j : I) (f : j ⟶ i), LBIso (M.pull (D.map f)) (N.pull (D.map f)) := by
  have loc : ∀ x : D.obj i, ∃ (V : (D.obj i).Opens) (p : N.ι × M.ι),
      IsAffineOpen V ∧ x ∈ V ∧ V ≤ (LB.div N M).U p := by
    intro x
    obtain ⟨p, hp⟩ := exists_chart (lb_div_isLB hM hN) x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open hp ((LB.div N M).U p).isOpen
    exact ⟨V, p, hV, hx, hle⟩
  choose V p hV hx hle using loc
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x => (V x : Set (D.obj i)))
    (fun x => (V x).isOpen.mem_nhds (hx x))
  have cov : ∀ x : D.obj i, ∃ a : σ, x ∈ V a := fun x => by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hσ.ge (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  have le : ∀ {Z : Scheme.{0}} (F : Z ⟶ D.obj i) (a : D.obj i), F ⁻¹ᵁ V a ≤
      (LB.div (N.pull F) (M.pull F)).U (fun _ => (p a).1, fun _ => (p a).2) :=
    fun F a z hz => ⟨mem_pull.2 (hle a hz).1, mem_pull.2 (hle a hz).2⟩
  obtain ⟨t, ht⟩ := h
  obtain ⟨j, f, u, hu⟩ := exists_units_of_isLimit D π w hc (fun a : σ => V a) (fun a => hV a)
    (fun a b => res (inf_le_inf (hle a) (hle b)) ((LB.div N M).g (p a) (p b)))
    (fun a => res (le (π i) a) (t.s (fun _ => (p a).1, fun _ => (p a).2))) (by
      intro a b y ha hb
      have hm : (𝟙 X : X ⟶ X) y ∈
          (LB.div (N.pull (π i)) (M.pull (π i))).U (fun _ => (p a).1, fun _ => (p a).2) ⊓
          (LB.div (N.pull (π i)) (M.pull (π i))).U (fun _ => (p b).1, fun _ => (p b).2) :=
        ⟨le _ _ ha, le _ _ hb⟩
      have e := congrArg (gm (𝟙 X) y _)
        (ht (fun _ => (p a).1, fun _ => (p a).2) (fun _ => (p b).1, fun _ => (p b).2))
      refine (gm_res (𝟙 X) y _ ha _).trans ((gm_res (𝟙 X) y _ hm _).symm.trans (e.trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))))
      · exact (gm_div_pull_g M N (π i) y (p a) (p b) ⟨hle a ha, hle b hb⟩).trans
          (gm_res (π i) y _ (show π i y ∈ V a ⊓ V b from ⟨ha, hb⟩) _).symm
      · exact (gm_res (𝟙 X) y _ hm _).trans (gm_res (𝟙 X) y _ hb _).symm)
  refine ⟨j, f, exists_gen_of_refinement _ (lb_div_isLB (pull_isLB hM _) (pull_isLB hN _))
    (fun a : σ => D.map f ⁻¹ᵁ V a) (fun y => cov (D.map f y))
    (fun a => (fun _ => (p a).1, fun _ => (p a).2)) (fun a => le _ a) u fun a b y ha hb => ?_⟩
  refine (hu a b y ha hb).trans (congrArg (· * _) ?_)
  exact (gm_res (D.map f) y _ (show D.map f y ∈ V a ⊓ V b from ⟨ha, hb⟩) _).trans
    (gm_div_pull_g M N (D.map f) y (p a) (p b) ⟨hle a ha, hle b hb⟩).symm
end GlobalTheory
