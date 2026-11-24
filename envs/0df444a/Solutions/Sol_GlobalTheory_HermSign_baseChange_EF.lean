-- Prove2me | solution 1 for GlobalTheory.HermSign.baseChange_EF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:55.84051+00:00
-- url     : https://prove2.me/submissions/ff870a2f-a9de-4855-a52f-14839db22728

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_hermC_eq
import Theorems.Thm_GlobalTheory_HermSign_realMap_tmul
import Theorems.Thm_GlobalTheory_CMType_trace_eq_sum_two_mul_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {r : ℕ}
  (Φ : CMType E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
namespace GlobalTheory.HermSign
theorem _root_.solution (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (x y : ℝ ⊗[ℤ] D.La) :
    D.EF.baseChange ℝ x y = ∑ τ : Φ, 2 * (τ.1 ξ *
      (realMap D Φ φ x τ ⬝ᵥ (Gm.map τ.1) *ᵥ star (realMap D Φ φ y τ))).re := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', Pi.add_apply, add_dotProduct, mul_add,
      Complex.add_re, Finset.sum_add_distrib]
  | tmul t x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, hy, hy', Pi.add_apply, star_add, mulVec_add, dotProduct_add, mul_add,
        Complex.add_re, Finset.sum_add_distrib]
    | tmul s y =>
      have h1 : ((D.EF x y : ℤ) : ℝ) = ∑ τ : Φ, 2 * (τ.1 (ξ * FD.herm Gm (φ x) (φ y))).re := by
        rw [← Φ.trace_eq_sum_two_mul_re, ← hEF]; simp
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, h1, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h2 : realMap D Φ φ (t ⊗ₜ x) τ ⬝ᵥ (Gm.map τ.1) *ᵥ star (realMap D Φ φ (s ⊗ₜ y) τ) =
          ((t * s : ℝ) : ℂ) * τ.1 (FD.herm Gm (φ x) (φ y)) := by
        rw [← hermC_eq]
        simp only [FD.hermC, FD.herm, realMap_tmul, map_sum, map_mul, FD.cc,
          IsCMField.complexEmbedding_complexConj, Finset.mul_sum, Complex.conj_ofReal]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        push_cast
        ring
      rw [h2, mul_left_comm (τ.1 ξ), Complex.re_ofReal_mul, map_mul]
      ring
end GlobalTheory.HermSign
