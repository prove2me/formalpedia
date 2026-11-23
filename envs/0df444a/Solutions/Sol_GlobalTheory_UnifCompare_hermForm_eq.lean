-- Prove2me | solution 1 for GlobalTheory.UnifCompare.hermForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:32.702307+00:00
-- url     : https://prove2.me/submissions/cbe0ca29-3f05-497d-b007-fe3109cd8848

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Theorems.Thm_GlobalTheory_UnifCompare_mem_iff
import Theorems.Thm_GlobalTheory_PullHermitian_exists_chart
import Theorems.Thm_GlobalTheory_PullHermitian_exists_glue
import Theorems.Thm_GlobalTheory_PullHermitian_hermForm_pull
import Theorems.Thm_GlobalTheory_PullHermitian_hermForm_sub_smul
import Theorems.Thm_GlobalTheory_appellHumbert_trivial_of_nowhere_vanishing
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
open GlobalTheory
open GlobalTheory.UnifCompare
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
open PullHermitian
namespace GlobalTheory.UnifCompare
theorem _root_.solution (hL : L.IsLB) (u u₀ : HolUnif A L g) {Hm H₀ : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} {χ₀ : u₀.Λ → ℂ} (hu : u.IsAH Hm χ) (hu₀ : u₀.IsAH H₀ χ₀)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u₀.ex (F z) = u.ex z) (z w : Fin g → ℂ) :
    hermForm H₀ (F z) (F w) = hermForm Hm z w := by
  have hΛ : ∀ l : u.Λ, F l ∈ u₀.Λ := fun l => (mem_iff u u₀ F hF l).2 l.2
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => exists_chart (u.ex z).left hL)
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
  set H₂ := (LinearMap.toMatrix' F).transpose * H₀ * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu₀.1
  have hsub : ∀ z w, hermForm (Hm - H₂) z w = hermForm Hm z w - hermForm H₀ (F z) (F w) :=
    fun z w => by
      have := hermForm_sub_smul Hm H₂ 1 1 z w
      rwa [one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, hermForm_pull] at this
  have := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    (Hm - H₂) (fun l => χ l / χ₀ ⟨F l, hΛ l⟩) r (hu.1.sub hH₂h)
    (fun l => by simp [hu.2.2.1, hu₀.2.2.1]) hr
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      rw [hrφ i z hi]
      exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi))
    (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have h1 := hu.2.2.2 l i z hi
      have h2 := hu₀.2.2.2 ⟨F l, hΛ l⟩ i (F z) (tr hi)
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)
      have h4 : χ₀ ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu₀.2.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ i z hi, hrφ i (z + l) hi']
      simp only [hsub, map_add]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ H₀.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ H₀.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') := by
        rw [← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      field_simp)
  have h := hsub z w
  rw [key.1] at h
  have h0 : hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z w = 0 := by simp [hermForm]
  rw [h0] at h
  exact (sub_eq_zero.1 h.symm).symm
end GlobalTheory.UnifCompare
