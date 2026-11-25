-- Prove2me | solution 1 for GlobalTheory.SplitTorus.isMonHom_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:37.434794+00:00
-- url     : https://prove2.me/submissions/4dd6ed7f-2da8-43a8-ba23-bcd4dfaa1083

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Theorems.Thm_GlobalTheory_SplitTorus_mulN_eq_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
namespace GlobalTheory.SplitTorus
theorem _root_.solution {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ) :
    IsMonHom (mulN G m) := by
  rw [mulN_eq_pow]
  refine ⟨?_, ?_⟩
  · rw [MonObj.comp_pow, Category.comp_id]
    have : η[G] = 1 := by rw [Hom.one_def]; simp
    rw [this, one_pow]
  · have h1 : μ[G] = fst G G * snd G G := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    have h2 : ((𝟙 G) ^ m ⊗ₘ (𝟙 G) ^ m) ≫ μ[G] = (fst G G ≫ (𝟙 G) ^ m) * (snd G G ≫ (𝟙 G) ^ m) := by
      rw [Hom.mul_def]; congr 1
    rw [h2, MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id,
      Category.comp_id, ← mul_pow, ← h1]
end GlobalTheory.SplitTorus
