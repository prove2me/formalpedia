-- Prove2me | solution 1 for GlobalTheory.SqZero.existsUnique_lieMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:07.171905+00:00
-- url     : https://prove2.me/submissions/88a7e770-edcc-45da-893d-ef9ea074c8c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_isTangent_comp
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {m : ℕ}
  {w : Fin m → (epsR R ⟶ H)} (f : G ⟶ H) [IsMonHom f]
omit [IsCommMonObj G]
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : ∀ i, IsTangent (v i)) (hw : IsLieBasis w) :
    ∃! M : Matrix (Fin n) (Fin m) R, ∀ i, IsLieComb (M i) w (v i ≫ f) := by
  have hx : ∀ i, ∃! c, IsLieComb c w (v i ≫ f) := fun i => hw.2 _ (isTangent_comp f (hv i))
  exact ⟨fun i => (hx i).exists.choose, fun i => (hx i).exists.choose_spec,
    fun M' hM' => funext fun i => (hx i).unique (hM' i) (hx i).exists.choose_spec⟩
end GlobalTheory.SqZero
