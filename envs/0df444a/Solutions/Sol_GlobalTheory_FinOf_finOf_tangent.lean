-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:46.639893+00:00
-- url     : https://prove2.me/submissions/a3d5fcb7-f26d-4ac2-b191-076582ffae8c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Theorems.Thm_GlobalTheory_FinOf_finOf_fst_sqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FinOf
theorem _root_.solution (B : BX R₀) (p : ℕ) (hp : p ≠ 0) (C : Type) [Field C] [CharZero C]
    [Algebra R₀ C] (z z' : B.G ⟨DualNumber C⟩) (hz : p • z = 0) (hz' : p • z' = 0)
    (h : B.map (finOf_fst C) z = B.map (finOf_fst C) z') : z = z' := by
  obtain ⟨v, hv⟩ := (B.tg_ker (finOf_fst C) (finOf_fst_sqZero C) (z - z')).1
    (by rw [map_sub, h, sub_self])
  have h1 : p • v = 0 := B.tg_inj (finOf_fst C) (finOf_fst_sqZero C)
    (by rw [map_nsmul, hv, smul_sub, hz, hz', sub_self, map_zero])
  have hinj : Function.Injective
      (p • LinearMap.id : (finOf_fst (R₀ := R₀) C).ker →ₗ[R₀] (finOf_fst (R₀ := R₀) C).ker) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : p • (a.1 : DualNumber C) = 0 := congrArg Subtype.val ha
    apply Subtype.ext
    have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
    rw [← Nat.cast_smul_eq_nsmul C] at ha'
    exact (smul_eq_zero.1 ha').resolve_left hpC
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := B.gg) _ hinj
  have h3 : v = 0 := h2 (by
    rw [map_zero, ← h1]
    have := map_nsmul (LinearMap.lTensorHom (R := R₀) B.gg) p
      (LinearMap.id : (finOf_fst (R₀ := R₀) C).ker →ₗ[R₀] (finOf_fst (R₀ := R₀) C).ker)
    simp only [LinearMap.coe_lTensorHom, LinearMap.lTensor_id] at this
    rw [this]; rfl)
  rw [h3, map_zero] at hv
  exact sub_eq_zero.1 hv.symm
end GlobalTheory.FinOf
