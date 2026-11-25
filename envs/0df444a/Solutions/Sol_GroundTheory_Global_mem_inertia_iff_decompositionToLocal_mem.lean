-- Prove2me | solution 1 for GroundTheory.Global.mem_inertia_iff_decompositionToLocal_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:10.049861+00:00
-- url     : https://prove2.me/submissions/d76bdac1-0636-4a92-a42f-73aa24590c2f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia
import Theorems.Thm_GroundTheory_Global_exists_sub_ringOfIntegersToInteger_mem
import Theorems.Thm_GroundTheory_Global_ringOfIntegersToInteger_mem_maximalIdeal_iff
import Theorems.Thm_GroundTheory_Global_integerAlgEquiv_ringOfIntegersToInteger
import Theorems.Thm_GroundTheory_Global_integerAlgEquiv_mem_maximalIdeal_iff
import Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_natCast_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    (σ : Gal(L/K)) ∈ w.asIdeal.inertia Gal(L/K) ↔
      decompositionToLocal v w σ ∈
        lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 := by
  have h0 : ((0 : ℕ) : ℤ) = 0 := rfl
  rw [← h0, mem_lowerRamificationGroup_natCast_iff, zero_add, pow_one]
  change (∀ r : 𝓞 L, (σ : Gal(L/K)) • r - r ∈ w.asIdeal) ↔ _
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := exists_sub_ringOfIntegersToInteger_mem w x
    have h1 := (integerAlgEquiv_mem_maximalIdeal_iff v w (decompositionToLocal v w σ) _).2 hr
    have h2 : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
          ringOfIntegersToInteger w r ∈ 𝓂[w.adicCompletion L] := by
      rw [integerAlgEquiv_ringOfIntegersToInteger, ← map_sub,
        ringOfIntegersToInteger_mem_maximalIdeal_iff]
      exact h r
    rw [map_sub] at h1
    have : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x =
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) x - integerAlgEquiv (v.adicCompletion K)
            (w.adicCompletion L) (decompositionToLocal v w σ) (ringOfIntegersToInteger w r)) +
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
            ringOfIntegersToInteger w r) - (x - ringOfIntegersToInteger w r) := by
      ring
    rw [this]
    exact sub_mem (add_mem h1 h2) hr
  · intro h r
    have := h (ringOfIntegersToInteger w r)
    rwa [integerAlgEquiv_ringOfIntegersToInteger, ← map_sub,
      ringOfIntegersToInteger_mem_maximalIdeal_iff] at this
end GroundTheory.Global
