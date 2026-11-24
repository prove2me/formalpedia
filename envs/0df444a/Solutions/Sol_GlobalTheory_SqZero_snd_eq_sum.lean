-- Prove2me | solution 1 for GlobalTheory.SqZero.snd_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:30:18.340994+00:00
-- url     : https://prove2.me/submissions/2f49d095-4d81-49b6-ac32-b1594d11f46c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
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
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



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
variable {R : Type} [CommRing R]
variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace GlobalTheory.SqZero
theorem _root_.solution {B κ : Type} [CommRing B] [Algebra R B] [Fintype κ] {β : κ → B}
    {τ : κ → Derivation R B B}
    (hτ : ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : B →ₐ[R] A),
        (∀ b b', (φ b - φ' b) * (φ b' - φ' b') = 0) →
        ∀ b, φ b - φ' b = ∑ i, φ' (τ i b) * (φ (β i) - φ' (β i)))
    (u : B →ₐ[R] S) (φ : B →ₐ[R] DualNumber S) (hφ : ∀ b, (φ b).fst = u b) (b : B) :
    (φ b).snd = ∑ i, u (τ i b) * (φ (β i)).snd := by
  have hd : ∀ b, φ b - ((inlS R S).comp u) b = inr (φ b).snd := fun b =>
    TrivSqZeroExt.ext (by simp [hφ]) (by simp)
  have key := hτ (DualNumber S) φ ((inlS R S).comp u)
    (fun b b' => by rw [hd, hd]; exact TrivSqZeroExt.inr_mul_inr _ _ _) b
  simp_rw [hd] at key
  simpa [TrivSqZeroExt.snd_sum, mul_comm] using congrArg TrivSqZeroExt.snd key
end GlobalTheory.SqZero
