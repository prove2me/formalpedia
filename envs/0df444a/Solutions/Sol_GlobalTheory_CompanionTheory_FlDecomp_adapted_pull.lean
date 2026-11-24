-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.adapted_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:51.008915+00:00
-- url     : https://prove2.me/submissions/bc931ff5-e863-403a-b602-0fe6a5b3eb73

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_mem_pull

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
theorem _root_.solution {h : V → V → L} {l : ℕ} {e f e' f' : Fin l → V} {W W' : Submodule L V} {u : Fin l → L}
    {Λ : AddSubgroup V} {k : V ≃ₗ[L] V} (hk : IsIso h k) (he : ∀ i, k (e i) = e' i) (hf : ∀ i, k (f i) = f' i)
    (hW : ∀ w ∈ W, k w ∈ W') (hA : IsAdapted h e' f' W' u Λ) : IsAdapted h e f W u (pull k Λ) := by
  intro a b w hw
  rw [mem_pull]
  have : k (∑ i, a i • e i + ∑ i, b i • f i + w) = ∑ i, a i • e' i + ∑ i, b i • f' i + k w := by
    simp [map_add, map_sum, he, hf]
  rw [this, hA a b (k w) (hW w hw), hk]
end GlobalTheory.CompanionTheory.FlDecomp
