-- Prove2me | solution 1 for GlobalTheory.SchemeHomsFromPoints.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:11.268032+00:00
-- url     : https://prove2.me/submissions/b259440d-940f-4e55-a855-0f2a37128089

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_hom_ext_of_points
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_range_subset
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_exists_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints
namespace GlobalTheory.SchemeHomsFromPoints
theorem _root_.solution {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    {S : Scheme.{0}} (q : Y ⟶ S) [IsSeparated q] [IsAffine S]
    (H : ∀ z, ∃ (W : X.Opens) (D : Y.Opens), IsAffineOpen D ∧ ⊤ ≤ ex z ⁻¹ᵁ W ∧
      (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D) ∧
      ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
        valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : X ⟶ Y, ∀ z, ex z ≫ g = ey z := by
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  choose W D hD hW hWD hf using H
  choose g hg using fun z => exists_local p ex ey hex (W z) (D z) (hD z) (hWD z) (hf z)
  have hcov : TopologicalSpace.IsOpenCover W := by
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x₀ _
    by_contra hx₀
    have hcl : IsClosed ((iSup W : X.Opens) : Set X)ᶜ := (iSup W).isOpen.isClosed_compl
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints ⟨x₀, hx₀⟩ hcl.isLocallyClosed
    obtain ⟨z, hz⟩ := hex _ (pointOfClosedPoint_comp p x hxc)
    apply hx
    have h1 : ex z (IsLocalRing.closedPoint ℂ) ∈ W z :=
      hW z (show (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈ ⊤ from trivial)
    have h2 : ex z (IsLocalRing.closedPoint ℂ) = x := by
      rw [hz]
      exact pointOfClosedPoint_apply p x hxc _
    exact le_iSup W z (h2 ▸ h1)
  have hglue : ∀ i j, pullback.fst (W i).ι (W j).ι ≫ g i = pullback.snd (W i).ι (W j).ι ≫ g j := by
    intro i j
    have : IsReduced (pullback (W i).ι (W j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (W i).ι (W j).ι ≫ (W i).ι)
    refine hom_ext_of_points (pullback.fst (W i).ι (W j).ι ≫ (W i).ι ≫ p) _ _ ?_
    intro x hx
    obtain ⟨w, hw⟩ := hex (x ≫ pullback.fst (W i).ι (W j).ι ≫ (W i).ι) (by simpa using hx)
    rw [← Category.assoc, ← Category.assoc, hg i w _ (by rw [hw, Category.assoc]),
      hg j w _ (by rw [hw, Category.assoc, pullback.condition])]
  refine ⟨(X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue, fun z => ?_⟩
  have h1 := IsOpenImmersion.lift_fac (W z).ι (ex z) (range_subset (W z) (ex z) (hW z))
  have h2 : (W z).ι ≫ (X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue = g z :=
    Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover W hcov) g hglue z
  rw [← hg z z _ h1, ← h2, ← Category.assoc, h1]
end GlobalTheory.SchemeHomsFromPoints
