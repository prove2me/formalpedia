-- Prove2me | solution 1 for GlobalTheory.UnRep.Nakayama.mem_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:56.648666+00:00
-- url     : https://prove2.me/submissions/38fe5b61-e2ab-45db-8547-358521e555b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Nakayama
variable (F : Type) [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.UnRep.Nakayama
namespace _root_.GlobalTheory.UnRep.Nakayama
theorem _root_.solution (a : _root_.GlobalTheory.UnRep.Nakayama.intAdeles F)
    (ha : ∀ v, Valued.v (a.1 v) < 1) :
    a ∈ Ideal.jacobson (⊥ : Ideal (_root_.GlobalTheory.UnRep.Nakayama.intAdeles F)) := by
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hval : ∀ v, Valued.v ((a * y + 1).1 v) = 1 := by
    intro v
    have hy : Valued.v (y.1 v) ≤ 1 := (y.2 v)
    have hlt : Valued.v (a.1 v * y.1 v) < 1 := by
      rw [map_mul]
      calc Valued.v (a.1 v) * Valued.v (y.1 v) ≤ Valued.v (a.1 v) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact ha v
    have : (a * y + 1).1 v = 1 + a.1 v * y.1 v := by
      simp [add_comm]
    rw [this, Valuation.map_one_add_of_lt _ hlt]
  let w : FiniteAdeleRing (𝓞 F) F := ⟨fun v ↦ ((a * y + 1).1 v)⁻¹, Filter.Eventually.of_forall fun v ↦ by
    show _ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval v, inv_one]⟩
  have hw : w ∈ _root_.GlobalTheory.UnRep.Nakayama.intAdeles F := fun v ↦ by
    show _ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((a * y + 1).1 v)⁻¹ ≤ 1
    rw [map_inv₀, hval v, inv_one]
  refine isUnit_iff_exists_inv.mpr ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro v
  have hne : (a * y + 1).1 v ≠ 0 := by
    intro h
    have := hval v
    rw [h, map_zero] at this
    exact zero_ne_one this
  exact mul_inv_cancel₀ hne
end _root_.GlobalTheory.UnRep.Nakayama
end GlobalTheory.UnRep.Nakayama
