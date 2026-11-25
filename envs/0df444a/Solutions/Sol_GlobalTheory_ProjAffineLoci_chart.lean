-- Prove2me | solution 1 for GlobalTheory.ProjAffineLoci.chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:36.52986+00:00
-- url     : https://prove2.me/submissions/c49d4fb1-8475-497a-ae5f-cd137c2e6ffe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NonzeroLocusSecPw
import Theorems.Thm_GlobalTheory_VeryAmplePow_exists_ratio
import Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_iff_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.ProjAffineLoci
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_res gs_mul fn_ext)
open TopologicalSpace
variable {X : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.ProjAffineLoci
theorem _root_.solution (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (hH : H.IsLB) {I : Type} (t : I → LB.Sec H) (i : I)
    {W : X.Opens} (e : nonzeroLocus (t i) = W) {n : ℕ} (b : Fin n → Γ(X, W))
    (hb : Function.Surjective (MvPolynomial.eval₂Hom (cst f W) b)) (c : Fin n → I)
    (hc : ∀ l k, rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t (c l)).f k) =
      rs X (inf_le_left : W ⊓ H.U k ≤ W) (b l) * rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t i).f k)) :
    ∃ r : I → Γ(X, nonzeroLocus (t i)),
      (∀ j k, rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t j).f k) =
        rs X (inf_le_left : nonzeroLocus (t i) ⊓ H.U k ≤ nonzeroLocus (t i)) (r j) *
          rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (t i))) r) := by
  subst e
  choose ρ hρ using fun j => GlobalTheory.VeryAmplePow.exists_ratio (t i) (t j)
  refine ⟨ρ, fun j k => fn_ext fun y hy => ?_, fun y => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hρ j _ (𝟙 X) y k hy.1 hy.2).trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _))).symm)
  · have hρb : ∀ l, ρ (c l) = b l := fun l => fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show z ∈ ⨆ k, H.U k by rw [hH.cover]; trivial)
      have hm : (𝟙 X : X ⟶ X) z ∈ nonzeroLocus (t i) ⊓ H.U k := ⟨hz, hk⟩
      have h₁ := (gs_res _ z _ hm _).symm.trans ((congrArg (gs (𝟙 X) z _) (hc l k)).trans
        ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _) (gs_res _ z _ hm _))))
      have u := (GlobalTheory.VeryAmplePow.isUnit_iff_mem (t i) (𝟙 X) z hk).2 hz
      exact u.mul_left_inj.1 ((hρ (c l) _ (𝟙 X) z k hz hk).symm.trans h₁)
    obtain ⟨p, rfl⟩ := hb y
    refine ⟨MvPolynomial.rename c p, ?_⟩
    rw [MvPolynomial.eval₂Hom_rename]
    congr 2
    exact funext hρb
end GlobalTheory.ProjAffineLoci
