-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.exists_coord_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:26.153908+00:00
-- url     : https://prove2.me/submissions/f63816ef-1718-43aa-9418-9777c840308f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_self
import Theorems.Thm_GlobalTheory_SectionsDescent_ext_affine
import Theorems.Thm_GlobalTheory_SectionsDescent_coord_mul_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_exists_coord
import Theorems.Thm_GlobalTheory_SectionsDescent_loc_compat

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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))
namespace GlobalTheory.SectionsDescent
theorem _root_.solution {ℓ : F →ₗ[K] K}
    (Λ : ∀ V : Y.Opens, IsAffineOpen V → FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V)
    (hΛ : ∀ V hV, IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ (Λ V hV)) {M : LB Y} (t : (M.pull p).Sec) :
    ∃ s : M.Sec, ∀ j V hV (h : V ≤ M.U j), rs h (s.f j) = Λ V hV (rs (pre_mono p h) (loc t j)) := by
  choose y hy using fun j => exists_coord H Λ hΛ (M.U j) (loc t j)
  refine ⟨⟨y, fun i j => ext_affine fun W hW h => ?_⟩, hy⟩
  have hi : W ≤ M.U i := h.trans inf_le_left
  have hj : W ≤ M.U j := h.trans inf_le_right
  rw [map_mul]
  refine (rs_rs inf_le_left h _).trans (Eq.trans ?_ (congrArg _ (rs_rs inf_le_right h _).symm))
  have := coord_mul_rs H hW le_rfl (hΛ W hW) (hΛ W hW) (rs h (M.g i j : Γ(Y, M.U i ⊓ M.U j)))
    (rs (pre_mono p hj) (loc t j))
  rw [rs_self] at this
  rw [hy i W hW hi, hy j W hW hj, loc_compat t i j hi hj]
  exact this.trans (congrArg _ (rs_self _ _))
end GlobalTheory.SectionsDescent
