-- Prove2me | solution 1 for GlobalTheory.ThetaCocycle.PullsBack.cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:24:10.718148+00:00
-- url     : https://prove2.me/submissions/aa8be8c3-5453-485c-9bca-47f64fe91139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
import Theorems.Thm_GlobalTheory_CoverGlue_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_chartPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ThetaCocycle
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}
private theorem lbIso_pull_comp_of_lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {f : Y ⟶ X}
    (H : LBIso L' (L.pull f)) (c : Z ⟶ Y) : LBIso (L'.pull c) (L.pull (c ≫ f)) := by
  have a : ChartPull (L'.pull c) L' c :=
    ⟨fun J => J PUnit.unit, fun J y hy => Set.mem_iInter.1 hy PUnit.unit, fun y J J' hJ hJ' => by
      refine (gm_linComb L' (fun _ => c) (fun _ => 1) (𝟙 _) y J J' hJ hJ').trans ?_
      simp⟩
  exact LBIso.chartPull a (chartPullSame L (fun _ => c ≫ f) (fun _ => f) (fun _ => 1) c (fun _ => rfl)) H
end GlobalTheory.ThetaCocycle
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaCocycle
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}
namespace GlobalTheory.ThetaCocycle
namespace PullsBack
theorem _root_.solution {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} (f' : S'' ⟶ S') {f : S' ⟶ S}
    {h : S'' ⟶ S} {ψ : t''.A.left ⟶ t.A.left} {φ : t'.A.left ⟶ t.A.left} (H'' : PullsBack t'' t h ψ)
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : ∃ c, PullsBack t'' t' f' c ∧ c ≫ φ = ψ := by
  obtain ⟨g'', l'', p''⟩ := H''
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  have sq : ψ ≫ t.A.hom = (t''.A.hom ≫ f') ≫ f := by rw [g''.1.w, Category.assoc]
  set c := g₀.1.lift ψ (t''.A.hom ≫ f') sq with hcdef
  have hc₁ : c ≫ φ = ψ := g₀.1.lift_fst _ _ _
  have hc₂ : c ≫ t'.A.hom = t''.A.hom ≫ f' := g₀.1.lift_snd _ _ _
  refine ⟨c, ⟨g₀.cancel (by rw [hc₁]; exact g'') hc₂, ?_, fun i => ?_⟩, hc₁⟩
  · have l₁ := lbIso_pull_comp_of_lbIso_pull l₀ c
    rw [hc₁] at l₁
    exact LBIso.trans t''.isLB (pull_isLB t.isLB ψ) (pull_isLB t'.isLB c) l'' (LBIso.symm l₁)
  · apply g₀.1.hom_ext
    · rw [Category.assoc, hc₁, p'' i, Category.assoc, Category.assoc, p₀ i]
    · rw [Category.assoc, hc₂, ← Category.assoc, Over.w (t''.pt i), Category.assoc, Over.w (t'.pt i)]
      simp [Out.baseOver]
end PullsBack
end GlobalTheory.ThetaCocycle
