-- Prove2me | solution 1 for GlobalTheory.CubeCut.ExactMod.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:50.208201+00:00
-- url     : https://prove2.me/submissions/1253d33d-cf39-4634-9959-c4a6dd9dd315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open GlobalTheory.CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
namespace GlobalTheory.CubeCut
namespace ExactMod
theorem _root_.solution {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : ∀ a : I, A.obj {a})
    (hy : ∀ a a' : I, Cube.res A (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) -
      Cube.res A (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ J {a, a'}) :
    ∃ y₀ : A.obj ∅, ∀ a, Cube.res A (Finset.empty_subset {a}) y₀ - y a ∈ J {a} := by
  have key : ∀ i j : I, (hij : i < j) →
      Cube.d A 1 (Cube.termOneEquiv A y) ⟨{i, j}, Finset.card_pair hij.ne⟩ ∈ J {i, j} := by
    intro i j hij
    rw [Cube.d_one_apply_pair A _ hij]
    simp only [Cube.termOneEquiv_apply]
    have h1 := (J {i, j}).neg_mem (hy i j)
    rwa [neg_sub] at h1
  have hx : ∀ s, Cube.d A 1 (Cube.termOneEquiv A y) s ∈ J s.1 := by
    rintro ⟨t, ht⟩
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 ht
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact key i j h'
    · revert ht
      rw [Finset.pair_comm i j]
      intro ht
      exact key j i h'
  obtain ⟨z, hz⟩ := h.2 0 (Cube.termOneEquiv A y) hx
  refine ⟨Cube.termZeroEquiv A z, fun a => ?_⟩
  have h1 := hz ⟨{a}, Finset.card_singleton a⟩
  rw [Pi.sub_apply, Cube.d_zero_apply, Cube.aug_apply, Cube.termOneEquiv_apply] at h1
  have h2 := (J {a}).neg_mem h1
  rwa [neg_sub] at h2
end ExactMod
end GlobalTheory.CubeCut
