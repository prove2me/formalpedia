-- Prove2me | solution 1 for GroundTheory.Global.isArithFrobAt_iff_decompositionToLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:06:36.657029+00:00
-- url     : https://prove2.me/submissions/551b996d-0af8-4883-b197-96ddb2d42afb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia
import Theorems.Thm_GroundTheory_Global_exists_sub_ringOfIntegersToInteger_mem
import Theorems.Thm_GroundTheory_Global_ringOfIntegersToInteger_mem_maximalIdeal_iff
import Theorems.Thm_GroundTheory_Global_integerAlgEquiv_ringOfIntegersToInteger
import Theorems.Thm_GroundTheory_Global_integerAlgEquiv_mem_maximalIdeal_iff
import Theorems.Thm_GroundTheory_Global_natCard_residueField_eq_under

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
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal ↔
      ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈
          𝓂[w.adicCompletion L] := by
  rw [natCard_residueField_eq_under v w]
  change (∀ r : 𝓞 L, (σ : Gal(L/K)) • r - r ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈
    w.asIdeal) ↔ _
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := exists_sub_ringOfIntegersToInteger_mem w x
    set q := Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K))
    have h1 := (integerAlgEquiv_mem_maximalIdeal_iff v w (decompositionToLocal v w σ) _).2 hr
    rw [map_sub] at h1
    have h2 : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
          ringOfIntegersToInteger w r ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
        ringOfIntegersToInteger_mem_maximalIdeal_iff]
      exact h r
    have h3 : ringOfIntegersToInteger w r ^ q - x ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [← Ideal.Quotient.eq, map_pow, map_pow, Ideal.Quotient.eq.2 hr]
    have : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ q =
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) x - integerAlgEquiv (v.adicCompletion K)
            (w.adicCompletion L) (decompositionToLocal v w σ) (ringOfIntegersToInteger w r)) +
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
            ringOfIntegersToInteger w r ^ q) + (ringOfIntegersToInteger w r ^ q - x ^ q) := by
      ring
    rw [this]
    exact add_mem (add_mem h1 h2) h3
  · intro h r
    have := h (ringOfIntegersToInteger w r)
    rwa [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
      ringOfIntegersToInteger_mem_maximalIdeal_iff] at this
end GroundTheory.Global
