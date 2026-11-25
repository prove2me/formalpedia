-- Prove2me | solution 1 for GlobalTheory.DetExtend.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:46:11.835978+00:00
-- url     : https://prove2.me/submissions/2e12f726-a7ed-44e4-8c0e-49983f9cdba2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.DetExtend
namespace GlobalTheory.DetExtend
theorem _root_.solution {O K Ω : Type} [CommRing O] [Algebra.IsIntegral ℤ O] [Field K] [IsAlgClosed K] [Field Ω]
    (i : K →+* Ω) (σ : O →+* Ω) : ∃ τ : O →+* K, i.comp τ = σ := by
  let _ := i.toAlgebra
  have h : ∀ a, σ a ∈ i.range := fun a => by
    have h₀ : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
    have h₁ : IsIntegral K (σ a) := h₀.tower_top
    exact minpoly.mem_range_of_degree_eq_one K _
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h₁))
  let e : K ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b hab => i.injective (congrArg Subtype.val hab), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (σ.codRestrict _ h), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (σ.codRestrict _ h a))
end GlobalTheory.DetExtend
