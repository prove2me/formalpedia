-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.pull_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:17.012802+00:00
-- url     : https://prove2.me/submissions/29dc179a-34eb-49d9-b826-b84618589410

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
include hσ
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (g : A.U ε ι) : g ∈ A.uQ ε s ⊓ A.uQ ε Set.univ ↔
    ∃ hg : g ∈ A.uQ ε s, piQ A ε hσ ⟨g, hg⟩ ∈ A.uQ ε (Set.univ : Set ↥sᶜ) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Subgroup.mem_subgroupOf.2 fun r hr c hc => ?_⟩
    have h2' := Subgroup.mem_subgroupOf.1 h2
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, trivial, rfl⟩ hr
    · exact h2' (Sum.inr i.1) (by rintro ⟨_, _, h⟩; cases h) (Sum.inl j.1) ⟨j.1, trivial, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Subgroup.mem_subgroupOf.2 fun r hr c hc => ?_⟩
    have h2' := Subgroup.mem_subgroupOf.1 h2
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, trivial, rfl⟩ hr
    have t1 := q_tri A ε hσ ⟨g, h1⟩
    have t2 := q_tri' A ε hσ ⟨g, h1⟩
    by_cases hj : j ∈ s
    · have : (Sum.inr i : ι ⊕ ι) ∉ (Sum.inl '' s : Set (ι ⊕ ι)) := by rintro ⟨_, _, h⟩; cases h
      exact ⟨t1.col _ this j hj, t2.col _ this j hj⟩
    by_cases hi : i ∈ s
    · have : (Sum.inl j : ι ⊕ ι) ∉ (Sum.inr '' s : Set (ι ⊕ ι)) := by rintro ⟨_, _, h⟩; cases h
      exact ⟨t1.row i hi _ this, t2.row i hi _ this⟩
    · exact h2' (Sum.inr ⟨i, hi⟩) (by rintro ⟨_, _, h⟩; cases h) (Sum.inl ⟨j, hj⟩) ⟨⟨j, hj⟩, trivial, rfl⟩
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
