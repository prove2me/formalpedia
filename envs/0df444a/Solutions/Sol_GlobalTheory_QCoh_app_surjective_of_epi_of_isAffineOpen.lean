-- Prove2me | solution 1 for GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:35.707395+00:00
-- url     : https://prove2.me/submissions/599fc32e-46f6-4fa8-a783-795325259a8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections

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
variable {X Y : Scheme.{u}} {F F' : X.Modules}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : F ⟶ F') [Epi φ] [F.IsQuasicoherent]
    [F'.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (φ.app U) := by
  let ψ := (Scheme.Modules.restrictFunctor hU.fromSpec).map φ
  have h := (Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).naturality ψ
  have h₁ : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).app
    (F.restrict hU.fromSpec)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (F.restrict hU.fromSpec)
  have h₂ : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).app
    (F'.restrict hU.fromSpec)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (F'.restrict hU.fromSpec)
  have h₃ : Epi ((𝟭 _).map ψ) := inferInstanceAs (Epi ψ)
  have h₄ : Epi ((moduleSpecΓFunctor ⋙ tilde.functor Γ(X, U)).map ψ) := by
    rw [← epi_comp_iff_of_isIso _ ((Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).app
      (F'.restrict hU.fromSpec)), h]
    infer_instance
  have h₅ : Epi (moduleSpecΓFunctor.map ψ) := (tilde.functor Γ(X, U)).epi_of_epi_map h₄
  have h₆ : Function.Surjective (φ.app (hU.fromSpec ''ᵁ ⊤)) :=
    (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map ψ)).mp h₅
  rwa [fromSpec_image_top hU] at h₆
end GlobalTheory.QCoh
