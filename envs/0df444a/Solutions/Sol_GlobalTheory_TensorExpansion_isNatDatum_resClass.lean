-- Prove2me | solution 1 for GlobalTheory.TensorExpansion.isNatDatum_resClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:15.782801+00:00
-- url     : https://prove2.me/submissions/848ea462-29ae-4123-ba37-2d4925b7ae87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
import Theorems.Thm_GlobalTheory_TensorExpansion_mem_of_inv_mul_mem
import Theorems.Thm_GlobalTheory_TensorExpansion_mem_matLat_pow_smul_iff
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat


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
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {m n : ℕ} (c : Fin m → Fin n → Res k e) :
    IsNatDatum ϖ e ((resClass ϖ c).indicator (1 : Matrix (Fin m) (Fin n) k → ℂ)) := by
  classical
  refine ⟨fun X hX => Set.indicator_of_notMem (fun h => hX (mem_matLat_stdLat.2 fun i j => (h i j).1)) _,
    fun X Z hZ => ?_⟩
  have hZ' := (mem_matLat_pow_smul_iff ϖ e).1 hZ
  have hiff : X + Z ∈ resClass ϖ c ↔ X ∈ resClass ϖ c := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have hz : Z i j ∈ 𝒪[k] := mem_of_inv_mul_mem hϖ e (hZ' i j)
    have h1 : (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) =
        (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) + (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j := by ring
    show (X i j + Z i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) ∈ 𝒪[k]) ↔
      (X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k])
    rw [h1, add_mem_cancel_right hz, add_mem_cancel_right (hZ' i j)]
  simp only [Set.indicator_apply, hiff, Pi.one_apply]
end GlobalTheory.TensorExpansion
