-- Prove2me | solution 1 for GlobalTheory.KSInh.ksRel_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:45.3815+00:00
-- url     : https://prove2.me/submissions/53aee1e8-5457-42ee-8782-38aed07e03e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGoodUniformisationKodairaSpencer
import Theorems.Thm_GlobalTheory_KSInh_isOpen_dom
import Theorems.Thm_GlobalTheory_KSInh_differentiableOn_fn
import Theorems.Thm_GlobalTheory_KSInh_differentiableAt_fn
import Theorems.Thm_GlobalTheory_KSInh_ex_add_period
import Theorems.Thm_GlobalTheory_cauchyRiemann_iff_differentiableOn_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KSInh
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
namespace GlobalTheory.KSInh
theorem _root_.solution (w : Fin g → ℂ) :
    KSRel u A₀.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) where
  der z := by
    have hd : ∀ (W : A₀.left.Opens) (k : Γ(A₀.left, W)), ⊤ ≤ ((u.ex z).left ≫ 𝟙 _) ⁻¹ᵁ W →
        DifferentiableAt ℂ (fn u (𝟙 _) W k) z :=
      fun W k hW => differentiableAt_fn u W k hW
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW' f => ?_⟩
    · have e : fn u (𝟙 _) W (f + f') = fn u (𝟙 _) W f + fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.add_apply]
        split_ifs with hy
        · simp only [valAt, map_add]
        · exact (add_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f + f')) z w =
        fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f') z w
      rw [e, fderiv_add (hd W f hW) (hd W f' hW)]
      rfl
    · have e : fn u (𝟙 _) W (f * f') = fn u (𝟙 _) W f * fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.mul_apply]
        split_ifs with hy
        · simp only [valAt, map_mul]
        · exact (mul_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f * f')) z w =
        fn u (𝟙 _) W f z * fderiv ℂ (fn u (𝟙 _) W f') z w + fn u (𝟙 _) W f' z * fderiv ℂ (fn u (𝟙 _) W f) z w
      rw [e, fderiv_mul (hd W f hW) (hd W f' hW)]
      rfl
    · show fderiv ℂ (fn u (𝟙 _) W' (resG A₀.left h f)) z w = fderiv ℂ (fn u (𝟙 _) W f) z w
      have hev : fn u (𝟙 _) W' (resG A₀.left h f) =ᶠ[nhds z] fn u (𝟙 _) W f := by
        filter_upwards [(isOpen_dom u W').mem_nhds hW'] with y hy
        have hyW' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W' := hy
        have hy' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W := hyW'.trans (Scheme.Hom.preimage_mono _ h)
        simp only [fn, valAt', dif_pos hyW', dif_pos hy']
        unfold valAt resG
        have key : A₀.left.presheaf.map (homOfLE h).op ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W' ⊤ hyW' =
            Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W ⊤ hy' :=
          Scheme.Hom.map_appLE _ _ _
        rw [← key]
        rfl
      rw [hev.fderiv_eq]
  base z r := by
    show fderiv ℂ (fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r)) z w = 0
    obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ y, fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) y = K := by
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
        ((Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge).hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), fun y => ?_⟩
      have ht : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ (⊤ : A₀.left.Opens) := (Scheme.Hom.preimage_top _).ge
      have key : Scheme.Hom.appLE A₀.hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) ⊤ ⊤ ht =
          Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge := by
        rw [Scheme.Hom.appLE_comp_appLE]
        congr 1
        simp
      simp only [fn, valAt', dif_pos ht]
      unfold valAt constFn
      rw [← key]
      rfl
    have e : fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) = fun _ => K := funext hK
    rw [e]
    simp
  hol W f :=
    ((cauchyRiemann_iff_differentiableOn_complex g _ _ (isOpen_dom u W)).2 (differentiableOn_fn u W f)).2 w
  per l W f z _ := by
    show fderiv ℂ (fn u (𝟙 _) W f) (z + l) w =
      fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f) z ((0 : Matrix (Fin g) (Fin g) ℂ).mulVec (star (l : Fin g → ℂ)))
    have hp : (fun y => fn u (𝟙 _) W f (y + l)) = fn u (𝟙 _) W f := by
      funext y
      unfold fn
      rw [ex_add_period]
    rw [Matrix.zero_mulVec, map_zero, add_zero, ← fderiv_comp_add_right, hp]
end GlobalTheory.KSInh
