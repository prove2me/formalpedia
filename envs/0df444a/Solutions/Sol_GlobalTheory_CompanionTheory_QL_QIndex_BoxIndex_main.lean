-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:14.011507+00:00
-- url     : https://prove2.me/submissions/5676bc2c-4b39-48b0-9d05-53e8fe9aa915

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_relIndex_line
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_extendByZero_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_boxAdd_eq_map
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_pi__f86b704c6d51


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV
namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (c c' : Fin n → Fin n → F), (∀ a b, c a b ≠ 0) → (∀ a b, c' a b ≠ 0) → (∀ a b, ∃ o ∈ O, c' a b = c a b * o) → (((boxAdd O β c').relIndex (boxAdd O β c) : ℕ) : ℝ) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => β p.1 ≤ β p.2), nrm (c p.1 p.2) / nrm (c' p.1 p.2) := by
  intro F _ _ _ _ O ϖ nrm q h n β c c' hc hc' hcc
  rw [boxAdd_eq_map, boxAdd_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (extendByZero_injective β),
    relIndex_pi', Nat.cast_prod,
    Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => β p.1 ≤ β p.2)
      (p := fun p : Fin n × Fin n => β p.1 ≤ β p.2) (fun p => by simp)]
  refine Finset.prod_congr rfl fun p _ => ?_
  obtain ⟨o, ho, e⟩ := hcc p.1.1 p.1.2
  have ho0 : o ≠ 0 := by
    rintro rfl
    exact hc' p.1.1 p.1.2 (by simpa using e)
  rw [e]
  exact relIndex_line h (hc _ _) ho ho0
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
