-- Prove2me | solution 1 for GlobalTheory.KS.VertFamily.ptDer_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:46:58.053736+00:00
-- url     : https://prove2.me/submissions/54326e74-22c1-403e-9816-8ac843157c70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVecStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangent
import Theorems.Thm_GlobalTheory_KS_VertFamily_differentiableAt_val
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.KS.VertFamily
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
private theorem valAt'_add' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f + f') = valAt' y W f + valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp
private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp
private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W W' : X.Opens} (hle : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : valAt' y W' (resG X hle f) = valAt' y W f := by
  have hW : ⊤ ≤ y ⁻¹ᵁ W := fun x hx => hle (h hx)
  unfold valAt' valAt
  rw [dif_pos h, dif_pos hW]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
end GlobalTheory.KS.VertFamily
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertFamily
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
namespace GlobalTheory.KS.VertFamily
theorem _root_.solution (z w : Fin g → ℂ) :
    PtDer (u.ex z).left (fun O f => fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w) where
  add O h f f' := by
    have e : (fun z' => valAt' (u.ex z').left O (f + f')) =
        (fun z' => valAt' (u.ex z').left O f) + fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_add' _ _ _ _
    rw [e, fderiv_add (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    rfl
  mul O h f f' := by
    have e : (fun z' => valAt' (u.ex z').left O (f * f')) =
        (fun z' => valAt' (u.ex z').left O f) * fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_mul_of_top_le_preimage_open _ _ _ _
    rw [e, fderiv_mul (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  res O O' hle h f := by
    have hev : (fun z' => valAt' (u.ex z').left O' (resG A.left hle f)) =ᶠ[nhds z]
        fun z' => valAt' (u.ex z').left O f := by
      filter_upwards [(u.hol O' (resG A.left hle f)).1.mem_nhds h] with z' hz'
      exact valAt'_resG _ hle hz' f
    rw [hev.fderiv_eq]
end GlobalTheory.KS.VertFamily
