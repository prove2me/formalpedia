-- Prove2me | solution 1 for GlobalTheory.T.residue_generates_unramifiedExt_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:32.071832+00:00
-- url     : https://prove2.me/submissions/e0094f49-3449-47a3-8c52-01cec1dbbd49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGeneratesUnramifiedExtResidueField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGeneratesUnramifiedExtResidueFieldStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_residue_generates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A → (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 → Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree → ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z := by
  first | exact @GlobalTheory.UnitLemma.Unr.residue_generates | exact GlobalTheory.UnitLemma.Unr.residue_generates | (intros; apply GlobalTheory.UnitLemma.Unr.residue_generates <;> assumption)
end _root_.GlobalTheory.T
