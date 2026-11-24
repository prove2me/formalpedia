-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.isIrreducible_smInd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:49:57.709602+00:00
-- url     : https://prove2.me/submissions/4c86b888-db2d-47fd-8b44-5beac4de90c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_linearEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {P : Subgroup G} {Q : Subgroup H} {σ : Representation F P V}
    {τ : Representation F Q W} (φ : G ≃* H) (hφ : Continuous φ) (hφ' : Continuous φ.symm) (κ : V ≃ₗ[F] W)
    (hP : ∀ g, g ∈ P ↔ φ g ∈ Q) (h : ∀ (p : P) v, κ (σ p v) = τ ⟨φ p, (hP p).1 p.2⟩ (κ v)) :
    (smInd P σ).IsIrreducible ↔ (smInd Q τ).IsIrreducible := by
  refine isIrreducible_iff_of_linearEquiv φ φ.surjective (LinearEquiv.ofLinear
    (indPull (σ := τ) (τ := σ) φ.symm.toMonoidHom hφ' κ.toLinearMap fun q =>
      ⟨⟨φ.symm q, (hP _).2 (by simp)⟩, rfl, fun w => by simp [h]⟩)
    (indPull (σ := σ) (τ := τ) φ.toMonoidHom hφ κ.symm.toLinearMap fun p =>
      ⟨⟨φ p, (hP p).1 p.2⟩, rfl, fun w => κ.injective (by simp [h])⟩) ?_ ?_) fun g f => ?_
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show κ (κ.symm (f.1.1 (φ (φ.symm x)))) = f.1.1 x
    simp
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show κ.symm (κ (f.1.1 (φ.symm (φ x)))) = f.1.1 x
    simp
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show κ (f.1.1 (φ.symm x * g)) = κ (f.1.1 (φ.symm (x * φ g)))
    simp
end GlobalTheory.SmGL.MultiIrr
