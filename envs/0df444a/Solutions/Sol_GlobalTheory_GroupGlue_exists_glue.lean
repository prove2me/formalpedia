-- Prove2me | solution 1 for GlobalTheory.GroupGlue.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:18:14.539214+00:00
-- url     : https://prove2.me/submissions/8c6e012b-38f4-42af-86cf-453d1df1dd37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_ext_small
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
namespace GlobalTheory.GroupGlue
theorem _root_.solution {T Y : Scheme.{0}} (t : T ⟶ X) (P : ∀ S : Scheme.{0}, (S ⟶ T) → (S ⟶ Y) → Prop)
    (ex : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (g : S ⟶ T) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ t → ∃ z, P S g z)
    (nat : ∀ (S S' : Scheme.{0}) (k : S' ⟶ S) (g : S ⟶ T) (z : S ⟶ Y), P S g z → P S' (k ≫ g) (k ≫ z))
    (uniq : ∀ (S : Scheme.{0}) (g : S ⟶ T) (z z' : S ⟶ Y), P S g z → P S g z' → z = z') :
    ∃ z : T ⟶ Y, ∀ (S : Scheme.{0}) (g : S ⟶ T) (z' : S ⟶ Y), P S g z' → g ≫ z = z' := by
  choose z hz using fun i => ex i _ (pullback.fst t (𝒰.f i)) (pullback.snd t (𝒰.f i)) pullback.condition.symm
  have key : ∀ (S : Scheme.{0}) (g : S ⟶ T) (w : S ⟶ Y), P S g w →
      ∀ i (m : S ⟶ pullback t (𝒰.f i)), m ≫ pullback.fst t (𝒰.f i) = g → m ≫ z i = w := by
    intro S g w hw i m hm
    have h1 := nat _ _ m _ _ (hz i)
    rw [hm] at h1
    exact uniq _ _ _ _ h1 hw
  refine ⟨Scheme.Cover.glueMorphisms (𝒰.pullback₁ t) z ?_, ?_⟩
  · intro i j
    have h2 := nat _ _ (pullback.snd (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j))) _ _ (hz j)
    have hc : pullback.snd (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j)) ≫ pullback.fst t (𝒰.f j) =
        pullback.fst (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j)) ≫ pullback.fst t (𝒰.f i) :=
      pullback.condition.symm
    rw [hc] at h2
    exact key _ _ _ h2 i _ rfl
  · intro S g w hw
    refine ext_small 𝒰 (g ≫ t) fun i S' k u hu => ?_
    obtain ⟨m, hm⟩ : ∃ m : S' ⟶ pullback t (𝒰.f i), m ≫ pullback.fst t (𝒰.f i) = k ≫ g :=
      ⟨pullback.lift (k ≫ g) u (by simp [hu]), pullback.lift_fst _ _ _⟩
    have e1 := key _ _ _ (nat _ _ k _ _ hw) i m hm
    rw [← e1, ← Category.assoc, ← hm, Category.assoc]
    congr 1
    exact Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ t) z _ i
end GlobalTheory.GroupGlue
