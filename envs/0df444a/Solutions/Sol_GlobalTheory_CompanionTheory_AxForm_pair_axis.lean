-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.pair_axis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:15.827962+00:00
-- url     : https://prove2.me/submissions/29650524-24c2-4114-8441-c7523782cf7e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pairing_differential_pullback
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_exists_factor
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_factor_unique
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_factor_over
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_mem_of_closedPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_mem_of_fst
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_isPullForm_iff


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R] {X X' : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (ω : GlobForm s) (hω : IsPullForm h ω 0) (U : X.affineOpens) {B M : Type} [CommRing B] [Algebra R B]
    [IsLocalRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (t : Sec s U.1 →+* TrivSqZeroExt B M) (ht : OverR R t) (y : Sp (TrivSqZeroExt B M) ⟶ X')
    (hy : y ≫ s' = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))
    (e : spMap t ≫ affPt s U = y ≫ φ) : pair t ht (ω.1 (op U)) = 0 := by
  have hU : ∀ z, (y ≫ φ) z ∈ U.1 := fun z ↦ by
    rw [← e]
    change affPt s U _ ∈ U.1
    have := U.2.range_fromSpec
    rw [← SetLike.mem_coe, ← this]
    exact ⟨_, rfl⟩
  let w : Sp B ⟶ X' := spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y
  have hz : w (IsLocalRing.closedPoint B) ∈ φ ⁻¹ᵁ U.1 := hU _
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset hz
  have hyV : ∀ z, y z ∈ V := mem_of_fst y V (mem_of_closedPoint w V hzV)
  obtain ⟨t', et'⟩ := exists_factor s' ⟨V, hV⟩ y hyV
  have ht' : OverR R t' := factor_over s' ⟨V, hV⟩ t' _ (by rw [et', hy])
  let p : Pair φ := ⟨(⟨V, hV⟩, U), hVU⟩
  have et : t = t'.comp (secPull s s' p) := factor_unique s U (by
    rw [e, spMap_comp, Category.assoc, secPull_affPt, ← Category.assoc, et'])
  subst et
  have k := isPullForm_iff.1 hω p
  rw [← pairing_differential_pullback _ (semiHom_secPull h p) t' ht' ht]
  have k' : (semiHom_secPull h p).m1 (ω.1 (op U)) = 0 := k
  rw [k', map_zero]
end GlobalTheory.CompanionTheory.AxForm
