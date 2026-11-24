-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.adapted_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:52.774158+00:00
-- url     : https://prove2.me/submissions/0fd98f87-2721-4fb4-844d-e168dfa9e92d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution {h : V → V → L} {l l' : ℕ} {e f : Fin l' → V} {W : Submodule L V} {u : Fin l' → L}
    {Λ : AddSubgroup V} (hA : IsAdapted h e f W u Λ) (τ : Fin l ≃ Fin l') :
    IsAdapted h (e ∘ τ) (f ∘ τ) W (u ∘ τ) Λ := by
  intro a b w hw
  have h1 : ∑ i, a i • (e ∘ τ) i = ∑ j, (a ∘ τ.symm) j • e j :=
    Fintype.sum_equiv τ _ _ (fun i => by simp)
  have h2 : ∑ i, b i • (f ∘ τ) i = ∑ j, (b ∘ τ.symm) j • f j :=
    Fintype.sum_equiv τ _ _ (fun i => by simp)
  rw [h1, h2, hA _ _ w hw]
  simp only [Function.comp]
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  · exact ⟨fun H i => by simpa using H (τ i), fun H j => by simpa using H (τ.symm j)⟩
  · exact ⟨fun H i => by simpa using H (τ i), fun H j => by simpa using H (τ.symm j)⟩
end GlobalTheory.CompanionTheory.FlDecomp
