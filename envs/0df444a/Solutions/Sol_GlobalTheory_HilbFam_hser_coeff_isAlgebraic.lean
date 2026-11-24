-- Prove2me | solution 1 for GlobalTheory.HilbFam.hser_coeff_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:39.253849+00:00
-- url     : https://prove2.me/submissions/5ba8e512-cf98-46bb-ac7a-9ea4e93770e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaFactorPowTwoMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertDiagonalRestrictionCoeffIsAlgebraic
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HilbFam_omegaFactor_pow_two_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_mul_mem_algebraicClosure {f g : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ)
    (hg : ∀ n, PowerSeries.coeff n g ∈ algebraicClosure ℚ ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) ∈ algebraicClosure ℚ ℂ := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ ↦ mul_mem (hf _) (hg _)
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_pow_mem_algebraicClosure {f : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ) (e : ℕ) :
    ∀ n, PowerSeries.coeff n (f ^ e) ∈ algebraicClosure ℚ ℂ := by
  induction e with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ e ih =>
    rw [pow_succ]
    exact coeff_mul_mem_algebraicClosure ih hf
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_exp_two_pi_I_mul_rat (q : ℚ) :
    IsAlgebraic ℚ (Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ))) := by
  refine (IsIntegral.of_pow q.den_pos ?_).isAlgebraic
  have h : Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ)) ^ q.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hq : (q : ℂ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have hmul : (q.den : ℂ) * (2 * ↑Real.pi * Complex.I * (q : ℂ)) =
        (q.num : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      linear_combination (2 * ↑Real.pi * Complex.I) * hq
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  rw [h]
  exact isIntegral_one
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_realEmbedding_apply {F : Type} [Field F] [NumberField F]
    (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F) : IsAlgebraic ℚ ((i y : ℝ) : ℂ) :=
  (Algebra.IsAlgebraic.isAlgebraic y).algHom (Complex.ofRealHom.comp i).toRatAlgHom
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma ecoef_mem_algebraicClosure_of_isCoef {F : Type} [Field F] [NumberField F] {k : ℕ}
    {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a) (ha₀ : IsAlgebraic ℚ a₀) (N : ℕ)
    (x : F) (μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (n : ℕ) :
    _root_.GlobalTheory.HilbFam.ecoef N a x μ n ∈ algebraicClosure ℚ ℂ := by
  unfold _root_.GlobalTheory.HilbFam.ecoef
  refine finsum_mem_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun ξ _ ↦ ?_
  refine mul_mem (mul_mem ?_ ?_) (prod_mem fun i _ ↦ pow_mem ?_ _)
  · rw [mem_algebraicClosure_iff]
    by_cases hξ : ξ = 0
    · rw [hξ, ha.1]
      exact ha₀
    · obtain ⟨m, hm⟩ := ha.2.1 ξ hξ
      rw [hm]
      exact isAlgebraic_int _
  · rw [mem_algebraicClosure_iff]
    unfold _root_.GlobalTheory.HilbFam.eTr
    exact isAlgebraic_exp_two_pi_I_mul_rat _
  · rw [mem_algebraicClosure_iff]
    exact isAlgebraic_realEmbedding_apply i ξ
end GlobalTheory.HilbFam
end

set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
namespace _root_.GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N κ c n hk ha ha₀ hc
  rw [← mem_algebraicClosure_iff]
  unfold _root_.GlobalTheory.HilbFam.hser
  simp only [map_smul, map_sum, smul_eq_mul]
  refine mul_mem ?_ (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _) ?_)
  · rw [hk, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
    exact SubfieldClass.ratCast_mem _ _
  · refine coeff_mul_mem_algebraicClosure
      (coeff_pow_mem_algebraicClosure (fun m ↦ ?_) _) (fun m ↦ ?_) n
    · rw [PowerSeries.coeff_mk, mem_algebraicClosure_iff]
      exact hc m
    · rw [PowerSeries.coeff_mk]
      exact ecoef_mem_algebraicClosure_of_isCoef ha ha₀ N x μ m
end _root_.GlobalTheory.HilbFam
end GlobalTheory.HilbFam
