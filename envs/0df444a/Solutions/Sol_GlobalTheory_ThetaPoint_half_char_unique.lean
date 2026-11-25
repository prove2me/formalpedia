-- Prove2me | solution 1 for GlobalTheory.ThetaPoint.half_char_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:34.709896+00:00
-- url     : https://prove2.me/submissions/bc43a967-f052-460c-8ce8-a17db98e2f06

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHalfOfSqEqOne
import Theorems.Thm_GlobalTheory_CanTh_differentiable_thetaChar
import Theorems.Thm_GlobalTheory_CanTh_mem_thetaDomain
import Theorems.Thm_GlobalTheory_CanTh_thetaChar_eq_theta
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_isUnit
import Theorems.Thm_GlobalTheory_mem_periodLattice_of_theta_translate_eq_unit_mul
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_periodLattice_isLattice_of_mem_siegelH
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
import Theorems.Thm_ReciprocityTheory_PTheta_thetaCharShift_holds
import Theorems.Thm_ReciprocityTheory_PTheta_thetaQuasiPeriod_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.ThetaPoint
open CanTh
variable {g : ℕ}
namespace GlobalTheory.ThetaPoint
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    {a b a' b' : Fin g → ℝ} (ha : ∀ k, a k = 0 ∨ a k = 1 / 2) (hb : ∀ k, b k = 0 ∨ b k = 1 / 2)
    (ha' : ∀ k, a' k = 0 ∨ a' k = 1 / 2) (hb' : ∀ k, b' k = 0 ∨ b' k = 1 / 2)
    {U : (Fin g → ℂ) → ℂ} (hU : Differentiable ℂ U) (hU0 : ∀ z, U z ≠ 0)
    (h : ∀ z, theta a' b' z τ = U z * theta a b z τ) : a' = a ∧ b' = b := by
  have H₁ : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z,
        (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') =
          eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧
        (fun z => theta 0 0 z τ) ≠ 0 := fun g τ hτ => by
    refine ⟨⟨?_, fun n n' z => ?_⟩, theta_ne_zero hτ 0 0⟩
    · have := differentiable_thetaChar (mem_thetaDomain hτ.2) 0 0
      simpa only [← thetaChar_eq_theta] using this
    · have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
      simp only [thetaQuasiPeriod_holds (Fin g) 0 0 z τ n n' hτ.1, autFactor, h0, zero_dotProduct, sub_zero, eC_zero,
        one_mul]
      congr 2
      ring
  let p : (Fin g → ℝ) → (Fin g → ℝ) → (Fin g → ℂ) → ℂ := fun a b z =>
    eC (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b + ofRealVec 0))
  have hp0 : ∀ a b z, p a b z ≠ 0 := fun a b z => Complex.exp_ne_zero _
  have hpd : ∀ a b, Differentiable ℂ (p a b) := fun a b => by
    simp only [p, eC, dotProduct]
    fun_prop
  have sh : ∀ a b z, theta a b z τ = p a b z * theta 0 0 (z + τ *ᵥ ofRealVec a + ofRealVec b) τ := fun a b z => by
    simpa only [zero_add] using thetaCharShift_holds (Fin g) a b 0 0 z τ hs
  let v := τ *ᵥ ofRealVec a + ofRealVec b
  obtain ⟨n, n', hn⟩ := mem_periodLattice_of_theta_translate_eq_unit_mul H₁
    periodLattice_isLattice_of_mem_siegelH g τ ⟨hs, hp⟩ (τ *ᵥ ofRealVec a' + ofRealVec b' - v)
    (fun z => U (z - v) * p a b (z - v) * (p a' b' (z - v))⁻¹)
    (((hU.comp (differentiable_id.sub_const v)).mul ((hpd a b).comp (differentiable_id.sub_const v))).mul
      (((hpd a' b').comp (differentiable_id.sub_const v)).inv fun z => hp0 _ _ _))
    (fun z => mul_ne_zero (mul_ne_zero (hU0 _) (hp0 _ _ _)) (inv_ne_zero (hp0 _ _ _))) (fun z => by
      have e := h (z - v)
      rw [sh a' b', sh a b, show z - v + τ *ᵥ ofRealVec a + ofRealVec b = z by simp only [v]; abel,
        show z - v + τ *ᵥ ofRealVec a' + ofRealVec b' = z + (τ *ᵥ ofRealVec a' + ofRealVec b' - v) by abel] at e
      have := hp0 a' b' (z - v)
      field_simp
      linear_combination e)
  have him : (τ.map Complex.im) *ᵥ (a' - a - fun i => (n i : ℝ)) = 0 := by
    ext i
    have := congrArg Complex.im (congrFun hn i)
    simp only [v, mulVec, dotProduct, ofRealVec, ofIntVec, Pi.add_apply, Pi.sub_apply, add_im, sub_im, im_sum,
      mul_im, ofReal_re, ofReal_im, intCast_re, intCast_im, mul_zero, zero_add, add_zero] at this
    simp only [mulVec, dotProduct, map_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    linarith
  have h1 : (a' - a - fun i => (n i : ℝ)) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.2 hp.isUnit) (him.trans (mulVec_zero _).symm)
  have half : ∀ (x y : ℝ) (k : ℤ), (x = 0 ∨ x = 1 / 2) → (y = 0 ∨ y = 1 / 2) → x - y = k → x = y ∧ k = 0 := by
    intro x y k hx hy e
    have h1 : (-1 : ℝ) < k := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h2 : (k : ℝ) < 1 := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h3 : k = 0 := by
      have : (-1 : ℤ) < k := by exact_mod_cast h1
      have : k < 1 := by exact_mod_cast h2
      omega
    subst h3
    exact ⟨by simpa [sub_eq_zero] using e, rfl⟩
  have h2 := fun i => half _ _ (n i) (ha' i) (ha i) (sub_eq_zero.1 (congrFun h1 i))
  obtain rfl : a' = a := funext fun i => (h2 i).1
  obtain rfl : n = 0 := funext fun i => (h2 i).2
  refine ⟨rfl, funext fun i => (half _ _ (n' i) (hb' i) (hb i) ?_).1⟩
  simp only [v, ofIntVec_zero, mulVec_zero, zero_add, add_sub_add_left_eq_sub] at hn
  have := congrFun hn i
  simp only [Pi.sub_apply, ofRealVec, ofIntVec] at this
  exact_mod_cast this
end GlobalTheory.ThetaPoint
