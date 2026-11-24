-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.isClosed_meets_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:29:59.752898+00:00
-- url     : https://prove2.me/submissions/25f2d777-a6a8-4723-a77c-0512bdb706df

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution {K : Set X} (hK : IsCompact K) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) K) :
    IsClosed {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hF : Continuous fun p : (Fin d → α → ℂ) × K => fun k => ∑ j, p.1 k j * b j p.2 := by
    refine continuous_pi fun k => ?_
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun p : (Fin d → α → ℂ) × K => p.1 k j :=
      (continuous_apply j).comp ((continuous_apply k).comp continuous_fst)
    have h2 : Continuous fun p : (Fin d → α → ℂ) × K => b j (p.2 : X) :=
      (hb j).comp_continuous (continuous_subtype_val.comp continuous_snd) fun p => p.2.2
    exact h1.mul h2
  have hclosed : IsClosed {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_eq ((continuous_apply k).comp hF) continuous_const
  have himage : {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} =
      Prod.fst '' {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    ext C
    constructor
    · rintro ⟨z, hz, h⟩
      exact ⟨(C, ⟨z, hz⟩), h, rfl⟩
    · rintro ⟨⟨C', z⟩, h, rfl⟩
      exact ⟨z, z.2, h⟩
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ hclosed
end GlobalTheory.CompanionTheory.FSCrofton
