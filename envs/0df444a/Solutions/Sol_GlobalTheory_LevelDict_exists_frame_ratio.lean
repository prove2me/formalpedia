-- Prove2me | solution 1 for GlobalTheory.LevelDict.exists_frame_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:32:48.331532+00:00
-- url     : https://prove2.me/submissions/39d8e23c-f69b-4ed6-a3b8-56fa6083b59d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
import Theorems.Thm_GlobalTheory_PullHermitian_exists_chart
import Theorems.Thm_GlobalTheory_PullHermitian_exists_glue
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
open PullHermitian
namespace GlobalTheory.LevelDict
theorem _root_.solution (hL : L.IsLB) (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u₀.fr i (F z) = r z * u.fr i z := by
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => PullHermitian.exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  refine ⟨r, hr, fun z => ?_, fun i z hi => ?_⟩
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
    rw [hrφ i z hi]
    exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi)
  · rw [hrφ i z hi, div_mul_cancel₀ _ (u.fr_ne _ _ hi)]
end GlobalTheory.LevelDict
