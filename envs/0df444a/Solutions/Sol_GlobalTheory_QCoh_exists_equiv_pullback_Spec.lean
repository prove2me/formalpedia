-- Prove2me | solution 1 for GlobalTheory.QCoh.exists_equiv_pullback_Spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:18:16.612724+00:00
-- url     : https://prove2.me/submissions/dbb3dcbf-2233-4c30-a705-3eeb30d029db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_tildePullbackIso_hom_app_toOpen
import Theorems.Thm_GlobalTheory_QCoh_res_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution (M : (Spec R).Modules) [M.IsQuasicoherent] :
    letI := φ.hom.toAlgebra
    ∃ e : S ⊗[R] Γ(M, ⊤) ≃ₗ[S] Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤),
      ∀ m, e (1 ⊗ₜ m) =
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m := by
  letI := φ.hom.toAlgebra
  refine ⟨(tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) ≪≫
    moduleSpecΓFunctor.mapIso (tildeIsoPullback φ M)).toLinearEquiv, fun m ↦ ?_⟩
  have h₁ := tildePullbackIso_hom_app_toOpen φ (moduleSpecΓFunctor.obj M) m
  have h₂ := congr(($((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
    M.fromTildeΓ)).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m))
  have h₃ : M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) = m :=
    (congr($(Scheme.Modules.toOpen_fromTildeΓ_app M ⊤) m)).trans (res_self M le_rfl m)
  refine Eq.trans congr(((Scheme.Modules.pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤ $h₁) ?_
  refine h₂.symm.trans ?_
  exact congr(((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ $h₃)
end GlobalTheory.QCoh
