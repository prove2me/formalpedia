-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:21.901799+00:00
-- url     : https://prove2.me/submissions/471c5e1e-8e25-41be-8c1b-08115e07fdca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv

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
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {ρ : Representation F G V} {σ : Representation F H W} (φ : G → H)
    (hφ : Function.Surjective φ) (κ : V ≃ₗ[F] W) (h : ∀ g v, κ (ρ g v) = σ (φ g) (κ v)) :
    ρ.IsIrreducible ↔ σ.IsIrreducible := by
  let E : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun S => ⟨S.toSubmodule.comap κ.symm.toLinearMap, fun g w hw => by
        obtain ⟨g, rfl⟩ := hφ g
        obtain ⟨v, rfl⟩ := κ.surjective w
        have hv : v ∈ S.toSubmodule := κ.symm_apply_apply v ▸ hw
        simpa [← h] using S.apply_mem_toSubmodule g hv⟩
      invFun := fun T => ⟨T.toSubmodule.comap κ.toLinearMap, fun g v hv => by
        show κ (ρ g v) ∈ T.toSubmodule
        rw [h]
        exact T.apply_mem_toSubmodule _ hv⟩
      left_inv := fun S => Subrepresentation.toSubmodule_injective (by ext v; simp)
      right_inv := fun T => Subrepresentation.toSubmodule_injective (by ext v; simp)
      map_rel_iff' := fun {S T} => ⟨fun hh v hv => by
        have : κ.symm (κ v) ∈ S.toSubmodule := (κ.symm_apply_apply v).symm ▸ hv
        have h2 : κ.symm (κ v) ∈ T.toSubmodule := hh this
        exact κ.symm_apply_apply v ▸ h2, fun hh v hv => hh hv⟩ }
  exact E.isSimpleOrder_iff
end GlobalTheory.SmGL.MultiIrr
