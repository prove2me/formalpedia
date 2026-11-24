-- Prove2me | solution 1 for GlobalTheory.UnRep.SplitRep.isUnA_mix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:02.398724+00:00
-- url     : https://prove2.me/submissions/1062c3f8-2c67-436e-ab0e-6414ab62b90a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
import Theorems.Thm_GlobalTheory_UnRep_SplitRep_mix_val
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
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SplitRep
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.SplitRep
namespace _root_.GlobalTheory.UnRep.SplitRep
theorem _root_.solution (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ε : _root_.GlobalTheory.AdLat.RA F E) (hε : ε * ε = ε)
    (hs : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ε = ε) (κ : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (hκ : _root_.GlobalTheory.UnRep.IsUnA c G κ.1) :
    _root_.GlobalTheory.UnRep.IsUnA c G (_root_.GlobalTheory.UnRep.SplitRep.mix ε hε κ).1 := by
  intro x y
  have hκxy := hκ x y
  unfold _root_.GlobalTheory.AdLat.hermA at hκxy ⊢
  rw [_root_.GlobalTheory.UnRep.SplitRep.mix_val]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_mul, map_sub, map_one, hs]
  set σ := _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
  calc _ = ε * (∑ a, ∑ b, (κ.1 *ᵥ x) a * 1 ⊗ₜ[F] G a b * σ ((κ.1 *ᵥ y) b)) +
        (1 - ε) * (∑ a, ∑ b, x a * 1 ⊗ₜ[F] G a b * σ (y b)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        linear_combination ((κ.1 *ᵥ x) a * 1 ⊗ₜ[F] G a b * σ ((κ.1 *ᵥ y) b) -
          (κ.1 *ᵥ x) a * 1 ⊗ₜ[F] G a b * σ (y b) - x a * 1 ⊗ₜ[F] G a b * σ ((κ.1 *ᵥ y) b) +
          x a * 1 ⊗ₜ[F] G a b * σ (y b)) * hε
    _ = _ := by rw [hκxy]; ring
end _root_.GlobalTheory.UnRep.SplitRep
end GlobalTheory.UnRep.SplitRep
