-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:42:40.934401+00:00
-- url     : https://prove2.me/submissions/c583f169-335b-412a-8daa-dedf150bde1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_restrict_fromSpec_iff
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_forall_exists_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ x : X, ∃ i, x ∈ (g i).opensRange)
    (h : ∀ i, (F.restrict (g i)).IsQuasicoherent) : F.IsQuasicoherent := by
  refine isQuasicoherent_of_forall_exists_affine F fun x ↦ ?_
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, hUi⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (g i).opensRange.2
  have hU : IsAffineOpen U := hU
  refine ⟨U, hU, hx, (isQuasicoherent_restrict_fromSpec_iff F hU).mp ?_⟩
  have hr : Set.range hU.fromSpec ⊆ Set.range (g i) := by
    rw [hU.range_fromSpec]; exact hUi
  let l := IsOpenImmersion.lift (g i) hU.fromSpec hr
  have hl : l ≫ g i = hU.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (l ≫ g i) := hl ▸ inferInstance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (g i)
  let iso : Scheme.Modules.restrictFunctor (g i) ⋙
      Scheme.Modules.restrictFunctor l ≅ Scheme.Modules.restrictFunctor hU.fromSpec :=
    (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫ Scheme.Modules.restrictFunctorCongr hl
  have := h i
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso (iso.app F)
    (inferInstanceAs ((F.restrict (g i)).restrict l).IsQuasicoherent)
end GlobalTheory.QCoh
