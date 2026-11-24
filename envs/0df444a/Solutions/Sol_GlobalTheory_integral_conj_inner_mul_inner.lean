-- Prove2me | solution 1 for GlobalTheory.integral_conj_inner_mul_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:10:14.665923+00:00
-- url     : https://prove2.me/submissions/a684321c-a2e6-477f-9eb1-296216009ece

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_inner_rankOneAverage
import Theorems.Thm_GlobalTheory_finrank_pos_of_isIrreducible

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
theorem _root_.solution [ρ.IsIrreducible] (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (u v u' v' : V) :
    ∫ k, conj ⟪u, ρ k v⟫_ℂ * ⟪u', ρ k v'⟫_ℂ ∂μ =
      ⟪u', u⟫_ℂ * ⟪v, v'⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 (rankOneAverage μ ρ ρ hρc hρu hρc v v')
  have hA : ∀ x, rankOneAverage μ ρ ρ hρc hρu hρc v v' x = c • x := by
    intro x
    rw [← hc, Algebra.algebraMap_eq_smul_one]
    rfl
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_isIrreducible ρ).ne'
  set b := stdOrthonormalBasis ℂ V
  have htr : (Module.finrank ℂ V : ℂ) * c = ⟪v, v'⟫_ℂ := by
    have h1 : ∑ i, ⟪b i, rankOneAverage μ ρ ρ hρc hρu hρc v v' (b i)⟫_ℂ
        = (Module.finrank ℂ V : ℂ) * c := by
      simp [hA]
    rw [← h1]
    simp only [inner_rankOneAverage]
    have hi : ∀ i, Integrable (fun k => conj ⟪b i, ρ k v⟫_ℂ * ⟪b i, ρ k v'⟫_ℂ) μ :=
      fun i => integrable_of_continuous_of_compactSpace μ
        ((Complex.continuous_conj.comp (continuous_const.inner (hρc v))).mul
          (continuous_const.inner (hρc v')))
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    simp [b.sum_inner_mul_inner, inner_map_map_of_norm_map ρ hρu]
  rw [← inner_rankOneAverage μ ρ ρ hρc hρu hρc, hA, inner_smul_right, ← htr]
  field_simp
end GlobalTheory
