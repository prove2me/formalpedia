-- Prove2me | solution 1 for Malliavin.IteratedIntegralConstruction.symmetrizeRestrict_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:11.278854+00:00
-- url     : https://prove2.me/submissions/4de89061-ec73-4238-8692-42ba169178bc

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_coeFn_symmetrizeL
import Theorems.Thm_Malliavin_measurableSet_simplex
import Theorems.Thm_Malliavin_mem_simplex
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_perm_eq_of_strictMono_comp
import Theorems.Thm_Malliavin_symmetrizeL_symmetrizeL
import Theorems.Thm_Malliavin_symmetrize_congr_ae
attribute [local simp] Malliavin.mem_symmetricSubmodule


section
namespace Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
section Step
variable {W : ℝ≥0 → Ω → ℝ}
end Step
section ContinuousTower
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
namespace IteratedIntegralConstruction
section HilbertBasisCountability
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]
end HilbertBasisCountability
end IteratedIntegralConstruction
namespace IteratedIntegralConstruction
private lemma symmetrize_factorial_indicator_on_simplex
    (n : ℕ) (g : (Fin n → ℝ≥0) → ℝ) {t : Fin n → ℝ≥0}
    (ht : t ∈ simplex ℝ≥0 n) :
    symmetrize n ((n.factorial : ℝ) • (simplex ℝ≥0 n).indicator g) t = g t := by
  classical
  rw [symmetrize_apply]
  have hsum :
      ∑ σ : Equiv.Perm (Fin n),
          (((n.factorial : ℝ) • (simplex ℝ≥0 n).indicator g) (t ∘ σ)) =
        (n.factorial : ℝ) • g t := by
    calc
      _ = (((n.factorial : ℝ) • (simplex ℝ≥0 n).indicator g)
          (t ∘ (1 : Equiv.Perm (Fin n)))) := by
        apply Finset.sum_eq_single 1
        · intro σ _ hσ
          have hnot : t ∘ σ ∉ simplex ℝ≥0 n := by
            intro hσ_mem
            have hEq : σ = 1 :=
              perm_eq_of_strictMono_comp (mem_simplex.mp ht).injective
                (mem_simplex.mp hσ_mem) (by
                  have ht_one : t ∘ (1 : Equiv.Perm (Fin n)) = t := by
                    funext i
                    rfl
                  rw [ht_one]
                  exact mem_simplex.mp ht)
            exact hσ hEq
          simp only [Pi.smul_apply, Set.indicator_of_notMem hnot, smul_zero]
        · intro h
          exact (h (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).elim
      _ = (n.factorial : ℝ) • g t := by
        have hone : t ∘ (1 : Equiv.Perm (Fin n)) = t := by
          funext i
          rfl
        rw [hone]
        simp only [Pi.smul_apply, Set.indicator_of_mem ht]
  rw [hsum, smul_smul, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]
private lemma coeFn_zeroExtendSimplex (n : ℕ) (g : SimplexKernel n) :
    ⇑(zeroExtendSimplex n g) =ᵐ[iteratedKernelMeasure n]
      (simplex ℝ≥0 n).indicator (fun t ↦ g t) :=
  MemLp.coeFn_toLp (memLp_zeroExtension n g)
private lemma restrict_symmetrize_factorial_zeroExtend (n : ℕ) (g : SimplexKernel n) :
    restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          ((n.factorial : ℝ) • zeroExtendSimplex n g)) = g := by
  apply Lp.ext
  have hinput :
      ⇑((n.factorial : ℝ) • zeroExtendSimplex n g) =ᵐ[iteratedKernelMeasure n]
        (n.factorial : ℝ) • (simplex ℝ≥0 n).indicator (fun t ↦ g t) := by
    filter_upwards [Lp.coeFn_smul (n.factorial : ℝ) (zeroExtendSimplex n g),
      coeFn_zeroExtendSimplex n g] with t ht₁ ht₂
    simp only [Pi.smul_apply] at ht₁ ⊢
    exact ht₁.trans (congrArg ((n.factorial : ℝ) • ·) ht₂)
  have hsymm :
      ⇑(symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          ((n.factorial : ℝ) • zeroExtendSimplex n g)) =ᵐ[iteratedKernelMeasure n]
        symmetrize n ((n.factorial : ℝ) •
          (simplex ℝ≥0 n).indicator (fun t ↦ g t)) :=
    (coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2
      ((n.factorial : ℝ) • zeroExtendSimplex n g)).trans
      (symmetrize_congr_ae (μ := nonnegativeLebesgueMeasure) hinput)
  have hpoint :
      symmetrize n ((n.factorial : ℝ) •
          (simplex ℝ≥0 n).indicator (fun t ↦ g t)) =ᵐ[
            (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)] ⇑g := by
    filter_upwards [ae_restrict_mem (measurableSet_simplex n)] with t ht
    exact symmetrize_factorial_indicator_on_simplex n (fun t ↦ g t) ht
  filter_upwards [restrictToSimplex_ae n _, ae_restrict_of_ae hsymm, hpoint]
    with t ht₁ ht₂ ht₃
  exact ht₁.trans (ht₂.trans ht₃)
private lemma symmetrizeRestrict_rightInverse (n : ℕ) (g : SimplexKernel n) :
    symmetrizeRestrict n (symmetrizedRightInverse n g) = g := by
  change restrictToSimplex n
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
      ((n.factorial : ℝ) •
        symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (zeroExtendSimplex n g))) = g
  simpa only [map_smul, symmetrizeL_symmetrizeL] using
    restrict_symmetrize_factorial_zeroExtend n g
end IteratedIntegralConstruction
namespace IteratedIntegralConstruction
end IteratedIntegralConstruction
end ContinuousTower
end Malliavin
end

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
open Malliavin.IteratedIntegralConstruction
namespace Malliavin.IteratedIntegralConstruction
theorem _root_.solution (n : ℕ) :
    Function.Surjective (symmetrizeRestrict n) :=
  fun g ↦ ⟨symmetrizedRightInverse n g, symmetrizeRestrict_rightInverse n g⟩
end Malliavin.IteratedIntegralConstruction
