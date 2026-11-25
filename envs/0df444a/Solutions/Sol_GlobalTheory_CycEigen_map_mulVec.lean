-- Prove2me | solution 1 for GlobalTheory.CycEigen.map_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:30:59.553205+00:00
-- url     : https://prove2.me/submissions/55a15891-9e38-4d1e-9250-c26c604cdbff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {C : Type} [NormedField C] [IsUltrametricDist C]
omit [IsUltrametricDist C]
namespace GlobalTheory.CycEigen
theorem _root_.solution {r : ℕ} (X : AddSubgroup C) (O : Set C) (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X)
    (T : C → C) (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hB : ∀ a b, B a b ∈ O) (v : Fin r → C) (hv : ∀ a, v a ∈ X) :
    (fun a => T (B.mulVec v a)) = B.mulVec fun a => T (v a) := by
  let T' : X →+ C := AddMonoidHom.mk' (fun x => T x) fun x x' => hadd _ x.2 _ x'.2
  funext a
  have h := map_sum T' (fun b => (⟨B a b * v b, hOX _ (hB a b) _ (hv b)⟩ : X)) Finset.univ
  simp only [T', AddMonoidHom.mk'_apply, AddSubgroup.val_finset_sum] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  exact Finset.sum_congr rfl fun b _ => hlin _ (hB a b) _ (hv b)
end GlobalTheory.CycEigen
