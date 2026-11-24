-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.adapted_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:48.193834+00:00
-- url     : https://prove2.me/submissions/bcb6b1a8-dbb3-4864-b583-c3748d0fd671

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_flip_sum

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
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution (F : Fin l → Prop) [DecidablePred F] {c : L} (hc : ‖c‖ = 1) {u v : Fin l → L}
    {Λ : AddSubgroup V} (hv : ∀ i, ‖v i‖ = if F i then ‖u i‖⁻¹ else ‖u i‖) (hA : IsAdapted h e f W u Λ) :
    IsAdapted h (fun i => if F i then f i else e i) (fun i => if F i then c • e i else f i) W v Λ := by
  intro a b w hw
  rw [flip_sum, hA _ _ w hw, ← and_assoc, ← and_assoc, ← forall_and, ← forall_and]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  rw [hv i]
  by_cases hF : F i
  · simp only [hF, if_true, norm_mul, hc, one_mul, inv_inv]
    exact and_comm
  · simp only [hF, if_false]
end GlobalTheory.CompanionTheory.FlDecomp
