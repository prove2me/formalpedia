-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.adapted_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:56.161969+00:00
-- url     : https://prove2.me/submissions/79f132ce-e67a-4fe1-9750-bee550f86537

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
theorem _root_.solution {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V} {u v : Fin l → L}
    {Λ₁ Λ₂ : AddSubgroup V} (hF : IsFrame h δ e f W) (h1 : IsAdapted h e f W u Λ₁) (h2 : IsAdapted h e f W v Λ₂)
    (huv : ∀ i, ‖u i‖ = ‖v i‖) (x : V) : x ∈ Λ₁ ↔ x ∈ Λ₂ := by
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  rw [h1 a b w hw, h2 a b w hw]
  simp only [huv]
end GlobalTheory.CompanionTheory.FlDecomp
