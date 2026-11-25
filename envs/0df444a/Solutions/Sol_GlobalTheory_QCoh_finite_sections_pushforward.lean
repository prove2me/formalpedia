-- Prove2me | solution 1 for GlobalTheory.QCoh.finite_sections_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:52.495803+00:00
-- url     : https://prove2.me/submissions/96463cd1-5297-4c51-9af3-05a6bf930207

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
namespace GlobalTheory.QCoh
theorem _root_.solution [IsFinite f] {V : Y.Opens} (hV : IsAffineOpen V)
    [hF : Module.Finite Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)] :
    Module.Finite Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V) := by
  letI := (f.app V).hom.toAlgebra
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  letI : Module Γ(Y, V) Γ(F, f ⁻¹ᵁ V) := Module.compHom _ (f.app V).hom
  haveI : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V) := .of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Finite.trans (R := Γ(Y, V)) Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)
end GlobalTheory.QCoh
