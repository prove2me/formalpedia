-- Prove2me | solution 1 for GlobalTheory.HilbFam.hser_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:37.585225+00:00
-- url     : https://prove2.me/submissions/7a015cbf-bcf1-4bb9-adbd-2f7cb48cf83c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinFourierCoeffRingEquivConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaFactorPowTwoMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesRingEquivConj
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HilbFam_ecoef_ringEquiv
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
private lemma powerSeries_map_mk' (g : ℂ ≃+* ℂ) (c : ℕ → ℂ) :
    PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk c) = PowerSeries.mk fun n ↦ g (c n) := by
  ext n
  simp
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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F)) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N g m π κ c n hk hN ha hga hlev hexp hemb
  have htr : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ,
      PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) =
        PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a (m * x) fun j ↦ μ (π.symm j)) := by
    intro μ
    rw [powerSeries_map_mk']
    congr 1
    funext j
    exact _root_.GlobalTheory.HilbFam.ecoef_ringEquiv F k 𝔞 𝔟 a₀ a x N g m π μ j hN ha hga hlev
      hexp hemb
  unfold _root_.GlobalTheory.HilbFam.hser
  subst hk
  simp only [map_smul, map_sum, smul_eq_mul, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
  rw [map_mul, map_ratCast, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun μ j ↦ μ (π.symm j)) (fun μ i ↦ μ (π i)) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    exact fun j ↦ hμ (π.symm j)
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    intro i
    simpa using hμ (π i)
  · intro μ _
    funext i
    simp
  · intro μ _
    funext j
    simp
  · intro μ _
    have hcoeff : ∀ φ : PowerSeries ℂ,
        g (PowerSeries.coeff n φ) = PowerSeries.coeff n (PowerSeries.map (g : ℂ →+* ℂ) φ) :=
      fun φ ↦ by
        rw [PowerSeries.coeff_map]
        rfl
    rw [map_mul, map_intCast, hcoeff, map_mul, map_pow, powerSeries_map_mk', htr]
    rw [Equiv.prod_comp π.symm fun i ↦
        _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i,
      Equiv.sum_comp π.symm fun i ↦ κ i - μ i]
end _root_.GlobalTheory.HilbFam
end GlobalTheory.HilbFam
