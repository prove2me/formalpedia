-- Prove2me | solution 1 for GlobalTheory.JacPiTensor.relJacD_piTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:06.710104+00:00
-- url     : https://prove2.me/submissions/5cb5df51-9595-4dc4-8ad3-e3d8cb0701ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelativeJacquetPiExteriorTensorEquivNormalized
import Theorems.Thm_GlobalTheory_JacStages_relDeltaHalfD_apply
import Theorems.Thm_GlobalTheory_JacStages_relEmbD_apply
import Theorems.Thm_GlobalTheory_JacStages_relJacD_mk
import Theorems.Thm_GlobalTheory_SmGL_jac_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.JacPiTensor
open scoped TensorProduct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {X : Fin s → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
namespace GlobalTheory.JacPiTensor
theorem _root_.solution :
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  refine ⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [relJacD_mk]
  show fwd e' ρ _ = piTensor (fun a => jac (e' a) (ρ a)) g (fwd e' ρ _)
  rw [map_smul, piTensor_tprod, fwd_mk_tprod', fwd_mk_tprod', piTensor_tprod]
  simp only [jac_mk, relEmbD_apply]
  rw [MultilinearMap.map_smul_univ, relDeltaHalfD_apply]
  congr 1
  simp [Units.coe_prod, Finset.prod_inv_distrib]
end GlobalTheory.JacPiTensor
