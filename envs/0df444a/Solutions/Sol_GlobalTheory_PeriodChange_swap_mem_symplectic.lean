-- Prove2me | solution 1 for GlobalTheory.PeriodChange.swap_mem_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:20.613008+00:00
-- url     : https://prove2.me/submissions/21846ec2-5e01-45a6-b4f7-8e77701a4fc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ChangeOfNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodChange
open Complex Matrix NumberField in
private theorem matrix_eq_of_dotProduct_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n] (M K : Matrix n n ℤ)
    (h : ∀ a b : n → ℤ, a ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ (K *ᵥ b)) : M = K := by
  ext i j
  simpa [mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1) (Pi.single j 1)
open Complex Matrix NumberField in
private theorem omegaStd_eq_neg_dotProduct_J {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b = -(a ⬝ᵥ (J (Fin g) ℤ *ᵥ b)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
  simp [Matrix.J, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Finset.sum_sub_distrib,
    neg_mulVec, one_mulVec, Finset.sum_neg_distrib, mul_comm]
  ring
open Complex Matrix NumberField in
private theorem fromBlocks_swap_mul_J_mul_swap {g : ℕ} :
    fromBlocks (0 : Matrix (Fin g) (Fin g) ℤ) 1 1 0 * J (Fin g) ℤ * fromBlocks 0 1 1 0 =
      -J (Fin g) ℤ := by
  simp [Matrix.J, fromBlocks_multiply, fromBlocks_neg]
end GlobalTheory.PeriodChange
end

set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChange
open Complex Matrix NumberField
namespace GlobalTheory.PeriodChange
namespace _root_.GlobalTheory.PeriodChange
theorem _root_.solution {g : ℕ} (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hN : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd (N *ᵥ a) (N *ᵥ b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) :
    Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∈
      Matrix.symplecticGroup (Fin g) ℤ := by
  set S : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := fromBlocks 0 1 1 0 with hS
  have hNJN : Nᵀ * J (Fin g) ℤ * N = J (Fin g) ℤ := by
    apply matrix_eq_of_dotProduct_mulVec_eq
    intro a b
    have := hN a b
    rw [omegaStd_eq_neg_dotProduct_J, omegaStd_eq_neg_dotProduct_J, neg_inj] at this
    rw [← this, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
  have hSt : Sᵀ = S := by simp [hS, fromBlocks_transpose]
  have hM : Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ =
      S * Nᵀ * S := by
    conv_rhs => rw [← fromBlocks_toBlocks N]
    simp [hS, fromBlocks_transpose, fromBlocks_multiply]
  rw [hM, SymplecticGroup.mem_iff]
  calc S * Nᵀ * S * J (Fin g) ℤ * (S * Nᵀ * S)ᵀ
      = S * (Nᵀ * ((S * J (Fin g) ℤ * S) * N)) * S := by
        simp only [transpose_mul, transpose_transpose, hSt, Matrix.mul_assoc]
    _ = -(S * (Nᵀ * J (Fin g) ℤ * N) * S) := by
        rw [fromBlocks_swap_mul_J_mul_swap]; simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    _ = J (Fin g) ℤ := by rw [hNJN, fromBlocks_swap_mul_J_mul_swap, neg_neg]
end _root_.GlobalTheory.PeriodChange
end GlobalTheory.PeriodChange
