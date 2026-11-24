-- Prove2me | solution 1 for GlobalTheory.CMNormIdentity.quadratic_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:03.347893+00:00
-- url     : https://prove2.me/submissions/61c7eea4-9b95-48c2-986f-6d0e00250112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingSmul
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CMNormIdentity
namespace GlobalTheory.CMNormIdentity
theorem _root_.solution {L : Type} [AddCommGroup L] (B : L → L → ℂ) (hl : ∀ a b c, B (a + b) c = B a c + B b c)
    (hr : ∀ a b c, B a (b + c) = B a b + B a c) {m : ℕ} (e : Fin m → L)
    (he : Submodule.span ℤ (Set.range e) = ⊤) (h1 : ∀ i, B (e i) (e i) = 0)
    (h2 : ∀ i j, B (e i + e j) (e i + e j) = 0) (a : L) : B a a = 0 := by
  let S : L →+ L →+ ℂ := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => B a b + B b a) fun b c => by
    rw [hl, hr]; ring) fun a b => by
      ext c
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, hl, hr]
      ring
  have hS : ∀ i, S (e i) = 0 := fun i => by
    have : (S (e i)).toIntLinearMap = 0 := by
      refine LinearMap.ext_on_range he fun j => ?_
      have := h2 i j
      rw [hl, hr, hr, h1, h1] at this
      simpa [S] using this
    exact AddMonoidHom.ext fun c => LinearMap.congr_fun this c
  have hS' : S.toIntLinearMap = 0 := LinearMap.ext_on_range he hS
  have h3 : S a = 0 := LinearMap.congr_fun hS' a
  have h4 : B a a + B a a = 0 := DFunLike.congr_fun h3 a
  linear_combination h4 / 2
end GlobalTheory.CMNormIdentity
