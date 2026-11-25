-- Prove2me | solution 1 for GlobalTheory.T.alternatingDifference_term_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:51.134212+00:00
-- url     : https://prove2.me/submissions/7dbe26ca-2cb3-417f-8afc-a72c5de65d19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindowStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_term_window


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ I I' : Finset ι, I ⊆ S → I' ⊆ S → (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N : ℕ) (x s : B.A), IsUnit x → IsUnit s → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ k : ℕ, L ≤ k → ∀ (M : Submodule K.O B.A) (p : ι → ℤ), Pos B a e N M p → (term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M ≠ 0 → Win I I' L k p) ∧ (Win I I' L k p → Mid S L k p → term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M = term B π I I' (eS B e I * (x * algebraMap K.O B.A a ^ (2 * k))) (eS B e I' * s) M) := by
  first | exact @GlobalTheory.UnitLemma.Desc.term_window | exact GlobalTheory.UnitLemma.Desc.term_window | (intros; apply GlobalTheory.UnitLemma.Desc.term_window <;> assumption)
end _root_.GlobalTheory.T
