-- Prove2me | solution 1 for GlobalTheory.SecRatio.existsUnique_isRatio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:40.364837+00:00
-- url     : https://prove2.me/submissions/53424954-083c-4e47-915b-d3d8e6dbfaad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Theorems.Thm_GlobalTheory_SecRatio_compat_res
import Theorems.Thm_GlobalTheory_SecRatio_isUnit_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
namespace GlobalTheory.SecRatio
private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
variable {X : Scheme.{0}} {H : LB X}
end GlobalTheory.SecRatio
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.SecRatio
variable {X : Scheme.{0}} {H : LB X}
namespace GlobalTheory.SecRatio
theorem _root_.solution (hH : H.IsLB) (s t : H.Sec) (W : X.Opens)
    (hW : W ≤ Out.nonzeroLocus t) : ∃! r : Γ(X, W), IsRatio s t W r := by
  have hu : ∀ l, IsUnit (resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l)) :=
    fun l => isUnit_res t l (inf_le_left.trans hW) _
  have hq : ∀ l, ∃ q : Γ(X, W ⊓ H.U l), resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) =
      q * resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l) := fun l =>
    ⟨resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) * ↑(hu l).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : W ≤ ⨆ l, W ⊓ H.U l := by
    rw [← inf_iSup_eq, hH.cover, inf_top_eq]
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun l => W ⊓ H.U l) q := by
    intro i j
    change resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i) (q i) =
      resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j) (q j)
    have hi : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U i := inf_le_left.trans inf_le_right
    have hj : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U j := inf_le_right.trans inf_le_right
    have e1 := congrArg (resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have u := isUnit_res t i ((inf_le_left.trans inf_le_left).trans hW) hi
    apply u.mul_right_cancel
    rw [← e1, compat_res s i j hi hj, compat_res t i j hi hj, e2]
    ring
  obtain ⟨r, hr, hr'⟩ := X.sheaf.existsUnique_gluing' (fun l => W ⊓ H.U l) W
    (fun l => homOfLE inf_le_left) hcov q hcomp
  refine ⟨r, fun l => ?_, fun r' h' => hr' r' fun l => ?_⟩
  · have : resG X (inf_le_left : W ⊓ H.U l ≤ W) r = q l := hr l
    rw [this]; exact hq l
  · change resG X (inf_le_left : W ⊓ H.U l ≤ W) r' = q l
    apply (hu l).mul_right_cancel
    rw [← hq l]; exact (h' l).symm
end GlobalTheory.SecRatio
