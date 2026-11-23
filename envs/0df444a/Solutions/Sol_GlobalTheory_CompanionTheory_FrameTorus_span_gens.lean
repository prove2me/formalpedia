-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.span_gens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:50.785621+00:00
-- url     : https://prove2.me/submissions/9ebfcf7a-430f-4105-8c1f-04b3c253a211

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) : Submodule.span L (gens e f W) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.subset_span (Or.inr hw))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
end GlobalTheory.CompanionTheory.FrameTorus
