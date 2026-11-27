-- Prove2me | solution 1 for GlobalTheory.integral_conj_character_mul_character_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:59.891124+00:00
-- url     : https://prove2.me/submissions/6fda02ff-09e9-4324-986e-ad383876393b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_finrank_pos_of_isIrreducible
import Theorems.Thm_GlobalTheory_integral_conj_entry_mul_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
namespace GlobalTheory
theorem _root_.solution [ρ.IsIrreducible]
    (hρc : ∀ v, Continuous fun k => ρ k v) (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) :
    ∫ k, conj (ρ.character k) * ρ.character k ∂μ = 1 := by
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_isIrreducible ρ).ne'
  set b := stdOrthonormalBasis ℂ V
  have hi : ∀ i j, Integrable (fun k => conj ⟪b i, ρ k (b i)⟫_ℂ * ⟪b j, ρ k (b j)⟫_ℂ) μ :=
    fun i j => integrable_of_continuous_of_compactSpace μ
      ((Complex.continuous_conj.comp (continuous_const.inner (hρc _))).mul
        (continuous_const.inner (hρc _)))
  simp only [Representation.character, LinearMap.trace_eq_sum_inner _ b, _root_.map_sum,
    Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp only [integral_finsetSum _ (fun j _ => hi _ j),
    integral_conj_entry_mul_entry μ ρ hρc hρu b]
  simp [hd]
end GlobalTheory
