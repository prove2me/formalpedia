-- Prove2me | solution 1 for GlobalTheory.ConstFam.isExtension_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:35.995552+00:00
-- url     : https://prove2.me/submissions/d8359475-2148-4fdf-a2d3-2644a449cd64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_exists_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
namespace GlobalTheory.ConstFam
theorem _root_.solution {k E : Type} [Field k] [Field E] [Algebra k E] {V W W' : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module E W] [AddCommGroup W'] [Module E W'] {a : V →ₛₗ[algebraMap k E] W}
    (ha : IsExtension a) (θ : W →ₗ[E] W') (hθ : Function.Bijective θ) (a' : V →ₛₗ[algebraMap k E] W')
    (e : ∀ v, a' v = θ (a v)) : IsExtension a' := by
  constructor
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨x, rfl⟩ := hθ.2 x
    obtain ⟨n, c, v, rfl⟩ := ha.exists_sum x
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, e _⟩)
  · intro ℓ
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    refine ⟨Λ.comp (LinearEquiv.ofBijective θ hθ).symm.toLinearMap.toAddMonoidHom, fun c v => ?_⟩
    have : (LinearEquiv.ofBijective θ hθ).symm (c • a' v) = c • a v := by
      rw [LinearEquiv.symm_apply_eq, map_smul, e]; rfl
    exact (congrArg Λ this).trans (hΛ c v)
end GlobalTheory.ConstFam
