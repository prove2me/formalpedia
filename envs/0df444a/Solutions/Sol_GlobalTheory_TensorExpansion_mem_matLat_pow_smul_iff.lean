-- Prove2me | solution 1 for GlobalTheory.TensorExpansion.mem_matLat_pow_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:02.400892+00:00
-- url     : https://prove2.me/submissions/741cba08-2981-47bd-8869-d2aca86897bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
import Theorems.Thm_GlobalTheory_SplitFlip_mem_smul_lat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
noncomputable section
open GlobalTheory GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.TensorExpansion
theorem _root_.solution (ϖ : kˣ) (e : ℕ) {m n : ℕ} {Z : Matrix (Fin m) (Fin n) k} :
    Z ∈ matLat (Fin m) (ϖ ^ e • stdLat k (Fin n)) ↔ ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] :=
  ⟨fun h i j => mem_stdLat.1 ((mem_smul_lat _ _ _).1 (h i)) j,
   fun h i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => h i j)⟩
end GlobalTheory.TensorExpansion
