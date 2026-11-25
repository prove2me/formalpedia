-- Prove2me | solution 1 for GlobalTheory.Cyc.IntBasis.norm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:46.519933+00:00
-- url     : https://prove2.me/submissions/bd80f4e9-eb87-4429-ba1e-633288dead8c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
import Theorems.Thm_GlobalTheory_T_norm_mem_cyclotomic_layer_prime_rpow
import Theorems.Thm_GlobalTheory_T_norm_primitiveRoot_primePow_sub_one_padicComplex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.IntBasis
theorem _root_.solution (K : FinExt l) (i : ℕ) (hi : 2 ≤ i) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ i))
    (z : Om l) (hz : z ∈ Ks K (i - 1)) (h0 : z ≠ 0) :
    ∃ n : ℤ, ‖z‖ = (l : ℝ) ^ (((n * l : ℤ) : ℝ) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1))) ∧
      ∀ a : ℕ, ‖z * (ζ - 1) ^ a‖ =
        (l : ℝ) ^ (((n * l - a : ℤ) : ℝ) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1))) := by
  obtain ⟨n, hn⟩ := GlobalTheory.T.norm_mem_cyclotomic_layer_prime_rpow l K (i - 1) (by omega) z hz h0
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hζC : IsPrimitiveRoot (ζ : PadicComplex l) (l ^ i) := by
    have := hζ.map_of_injective (algebraMap (PadicAlgCl l) (PadicComplex l)).injective
    simpa [← PadicComplex.coe_eq] using this
  have hnorm1 : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (i - 1) * ((l : ℝ) - 1))) := by
    rw [← GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l i (by omega) _ hζC, ← PadicComplex.norm_extends]
    congr 1
    rw [PadicComplex.coe_eq, PadicComplex.coe_eq, map_sub, map_one]
  set D : ℝ := (l : ℝ) ^ (i - 1) * ((l : ℝ) - 1) with hD
  have hpow : (l : ℝ) ^ (i - 1) = (l : ℝ) ^ (i - 1 - 1) * l := by
    rw [← pow_succ]
    congr 1
    omega
  have hD' : (0 : ℝ) < (l : ℝ) ^ (i - 1 - 1) * ((l : ℝ) - 1) := by
    apply mul_pos (pow_pos hl0 _)
    linarith
  refine ⟨n, ?_, ?_⟩
  · rw [hn]
    congr 1
    rw [hD, hpow]
    push_cast
    field_simp
  · intro a
    rw [norm_mul, norm_pow, hnorm1, hn, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_add hl0]
    congr 1
    rw [hD, hpow]
    push_cast
    field_simp
    ring
end GlobalTheory.Cyc.IntBasis
