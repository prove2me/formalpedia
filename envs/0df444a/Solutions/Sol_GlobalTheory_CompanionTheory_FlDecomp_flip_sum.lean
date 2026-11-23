-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.flip_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:41.216794+00:00
-- url     : https://prove2.me/submissions/4f6d396e-9bec-4fde-afa5-b2d8a74c3049

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
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution (F : Fin l → Prop) [DecidablePred F] (c : L) (a b : Fin l → L) :
    ∑ i, a i • (if F i then f i else e i) + ∑ i, b i • (if F i then c • e i else f i) =
      ∑ i, (if F i then c * b i else a i) • e i + ∑ i, (if F i then a i else b i) • f i := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [smul_smul, add_comm, mul_comm (b i)]
  · rfl
end GlobalTheory.CompanionTheory.FlDecomp
