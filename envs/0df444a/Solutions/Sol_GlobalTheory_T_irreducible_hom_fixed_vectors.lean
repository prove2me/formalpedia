-- Prove2me | solution 1 for GlobalTheory.T.irreducible_hom_fixed_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:00.775567+00:00
-- url     : https://prove2.me/submissions/cb5908d0-8f01-4077-9a03-067bb099944b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_hecke_determines


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → (∃ v ∈ fixed π K, v ≠ 0) → ∀ T : V →ₗ[ℂ] W, (∀ v ∈ fixed π K, T v ∈ fixed τ K) → (∀ w ∈ fixed τ K, ∃ v ∈ fixed π K, T v = w) → (∀ v ∈ fixed π K, T v = 0 → v = 0) → (∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v)) → Nonempty (π.Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeInj.hecke_determines | exact GlobalTheory.CompanionTheory.HeckeInj.hecke_determines | (intros; apply GlobalTheory.CompanionTheory.HeckeInj.hecke_determines <;> assumption)
end _root_.GlobalTheory.T
