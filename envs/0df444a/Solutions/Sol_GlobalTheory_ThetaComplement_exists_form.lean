-- Prove2me | solution 1 for GlobalTheory.ThetaComplement.exists_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:38.204091+00:00
-- url     : https://prove2.me/submissions/ed87008b-9364-4241-919c-17ab09684ff7

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsComplementaryThetaOfLinearMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaComplement
namespace GlobalTheory.ThetaComplement
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ ∈ SiegelH (Fin g)) :
    ∃ H : Matrix (Fin g) (Fin g) ℂ, H.IsHermitian ∧ H.IsSymm ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) ∧
      ∀ n n' : Fin g → ℤ, H.mulVec (star (τ *ᵥ ofIntVec n + ofIntVec n'))
        = H.mulVec (τ *ᵥ ofIntVec n + ofIntVec n') - (2 * I) • ofIntVec n := by
  obtain ⟨hs, hY⟩ := hτ
  set Y := τ.map Complex.im with hYd
  have hYi : Y⁻¹.PosDef := hY.inv
  have hsym : ∀ i j, Y⁻¹ i j = Y⁻¹ j i := fun i j => by
    simpa using (hYi.isHermitian.apply i j).symm
  refine ⟨Y⁻¹.map (fun x : ℝ => (x : ℂ)), ?_, ?_, ?_, ?_⟩
  · ext i j
    simp [hsym i j]
  · ext i j
    simp [hsym i j]
  · intro z hz
    have h : (z ⬝ᵥ (Y⁻¹.map (fun x : ℝ => (x : ℂ))).mulVec (star z)).re
        = (fun i => (z i).re) ⬝ᵥ Y⁻¹.mulVec (fun i => (z i).re)
          + (fun i => (z i).im) ⬝ᵥ Y⁻¹.mulVec (fun i => (z i).im) := by
      simp [dotProduct, mulVec, re_sum, im_sum, Finset.sum_add_distrib]
    rw [h]
    have h1 := hYi.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).re)
    have h2 := hYi.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).im)
    simp only [star_trivial] at h1 h2
    by_cases hr : (fun i => (z i).re) = 0
    · have hi : (fun i => (z i).im) ≠ 0 := by
        intro hi
        apply hz
        funext i
        exact Complex.ext (congrFun hr i) (congrFun hi i)
      have h3 := hYi.dotProduct_mulVec_pos hi
      simp only [star_trivial] at h3
      linarith
    · have h3 := hYi.dotProduct_mulVec_pos hr
      simp only [star_trivial] at h3
      linarith
  · intro n n'
    have h1 : star (τ *ᵥ ofIntVec n + ofIntVec n') = τ *ᵥ ofIntVec n + ofIntVec n'
        - (2 * I) • ((Y.map (fun x : ℝ => (x : ℂ))) *ᵥ ofIntVec n) := by
      funext i
      apply Complex.ext <;>
        simp [dotProduct, mulVec, re_sum, im_sum, ofIntVec, hYd]
      ring
    have h2 : Y⁻¹.map (fun x : ℝ => (x : ℂ)) * Y.map (fun x : ℝ => (x : ℂ)) = 1 := by
      have := (Matrix.map_mul (L := Y⁻¹) (M := Y) (f := Complex.ofRealHom)).symm
      rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.1 hY.isUnit)] at this
      exact this.trans (by simp)
    rw [h1, mulVec_sub, mulVec_smul, mulVec_mulVec, h2, one_mulVec]
end GlobalTheory.ThetaComplement
