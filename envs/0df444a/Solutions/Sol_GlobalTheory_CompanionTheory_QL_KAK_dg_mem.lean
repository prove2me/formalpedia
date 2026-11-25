-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.KAK.dg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:51.03213+00:00
-- url     : https://prove2.me/submissions/dc609cb8-cc8f-47e7-8723-d17fd7a66792

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.KAK
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.KAK
theorem _root_.solution (O : Subring F) {n : ℕ} (a : Fin n → Fˣ) (h₁ : ∀ i, (a i : F) ∈ O)
    (h₂ : ∀ i, (((a i)⁻¹ : Fˣ) : F) ∈ O) : dg a ∈ GLint O n := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (Matrix.diagonal fun i => (a i : F)) i j ∈ O
    by_cases hij : i = j
    · subst hij; simpa using h₁ i
    · simp [Matrix.diagonal_apply_ne _ hij, O.zero_mem]
  · change (Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)) i j ∈ O
    by_cases hij : i = j
    · subst hij; simpa using h₂ i
    · simp [Matrix.diagonal_apply_ne _ hij, O.zero_mem]
end GlobalTheory.CompanionTheory.QL.KAK
