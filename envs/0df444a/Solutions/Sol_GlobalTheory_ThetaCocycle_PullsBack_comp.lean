-- Prove2me | solution 1 for GlobalTheory.ThetaCocycle.PullsBack.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:24.502969+00:00
-- url     : https://prove2.me/submissions/0f36babd-b809-4de2-b9b5-a08d8eedad13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_chartPull
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
theorem _root_.solution {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} {f' : S'' ⟶ S'} {f : S' ⟶ S}
    {h : S'' ⟶ S} {φ' : t''.A.left ⟶ t'.A.left} {φ : t'.A.left ⟶ t.A.left} (H' : PullsBack t'' t' f' φ')
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : PullsBack t'' t h (φ' ≫ φ) := by
  obtain ⟨g', l', p'⟩ := H'
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  refine ⟨g'.comp g₀, ?_, fun i => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB φ') (pull_isLB t.isLB (φ' ≫ φ)) l'
      (lbIso_pull_comp_of_lbIso_pull l₀ φ')
  · rw [reassoc_of% (p' i), p₀ i, Category.assoc]
end PullsBack
end GlobalTheory.ThetaCocycle
