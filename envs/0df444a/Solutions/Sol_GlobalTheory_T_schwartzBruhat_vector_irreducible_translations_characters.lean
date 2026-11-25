-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhat_vector_irreducible_translations_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:24.678411+00:00
-- url     : https://prove2.me/submissions/d2909edb-b91b-457d-981d-01dbb115d241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatVectorIrreducibleTranslationsChara
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatVectorIrreducibleTranslationsCharaStatement
import Theorems.Thm_GlobalTheory_IrredSBVec_sb_irreducible_vec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ W : Submodule ℂ ((κ → k) → ℂ), W ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ φ ∈ W, ∀ v : κ → k, (fun x => φ (x + v)) ∈ W) →
    (∀ φ ∈ W, ∀ y : κ → k, (fun x => ψ0 (x ⬝ᵥ y) * φ x) ∈ W) →
    ∀ φ₀ ∈ W, φ₀ ≠ 0 → W = GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @GlobalTheory.IrredSBVec.sb_irreducible_vec | exact GlobalTheory.IrredSBVec.sb_irreducible_vec | (intros; apply GlobalTheory.IrredSBVec.sb_irreducible_vec <;> assumption)
end _root_.GlobalTheory.T
