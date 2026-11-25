-- Prove2me | solution 1 for GlobalTheory.CubeTop.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:11:20.922804+00:00
-- url     : https://prove2.me/submissions/b1492957-0766-4dc5-8f91-bae38bfa873e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Theorems.Thm_GlobalTheory_CubeTop_span_topClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.CubeTop
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
namespace GlobalTheory.CubeTop
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R) (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s)), (∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}), Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) → ((∀ a, T a ≠ Finset.univ) → (cubeComplex A).ExactAt (Fintype.card ι)) ∧ ({a | T a = Finset.univ}.Finite → Module.Finite R ((cubeComplex A).homology (Fintype.card ι))) := by
  intro ι _ _ R _ κ T A b hb
  have h := span_topClass T A b hb
  refine ⟨fun hT => ?_, fun hT => ⟨h ▸ Submodule.fg_span (hT.image _)⟩⟩
  · rw [Set.eq_empty_of_forall_notMem (s := {a | T a = Finset.univ}) hT, Set.image_empty,
      Submodule.span_empty] at h
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have := (Submodule.subsingleton_iff R).1 (subsingleton_of_bot_eq_top h)
    exact ModuleCat.isZero_of_subsingleton _
end GlobalTheory.CubeTop
