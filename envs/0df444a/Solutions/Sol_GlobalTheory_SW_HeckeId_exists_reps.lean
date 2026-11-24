-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:14.361103+00:00
-- url     : https://prove2.me/submissions/55565c61-5ac5-42fd-b68c-58da4edfd0f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_one_tmul_eq_zero
import Theorems.Thm_GlobalTheory_SW_Hyper_finrank_fibre
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
attribute [local instance] Ideal.Quotient.field
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] {B : ℕ}
    (hB : Nat.card (O ⧸ P) ^ Module.finrank O M = B) : ∃ ξ : Fin B → M, ∀ χ : AddChar M ℂ,
    (∀ c ∈ P, ∀ x, χ (c • x) = 1) → ∑ j, χ (ξ j) = if ∀ x, χ x = 1 then (B : ℂ) else 0 := by
  have : Finite ((O ⧸ P) ⊗[O] M) := Module.finite_of_finite (O ⧸ P)
  have hs : ∀ v : (O ⧸ P) ⊗[O] M, ∃ x : M, (1 : O ⧸ P) ⊗ₜ[O] x = v :=
    TensorProduct.mk_surjective O M (O ⧸ P) Ideal.Quotient.mk_surjective
  choose l hl using hs
  have hc : Nat.card ((O ⧸ P) ⊗[O] M) = B := by
    rw [← hB, ← Hyper.finrank_fibre O M (O ⧸ P), Module.natCard_eq_pow_finrank (K := O ⧸ P)]
  let ε := Finite.equivFinOfCardEq hc
  refine ⟨fun j => l (ε.symm j), fun χ hχ => ?_⟩
  have h0 : ∀ x ∈ (P • ⊤ : Submodule O M), χ x = 1 := fun x hx =>
    Submodule.smul_induction_on hx (fun c hc x _ => hχ c hc x) fun x y hx hy => by
      rw [AddChar.map_add_eq_mul, hx, hy, mul_one]
  have h1 : ∀ x y : M, (1 : O ⧸ P) ⊗ₜ[O] x = (1 : O ⧸ P) ⊗ₜ[O] y → χ x = χ y := fun x y h => by
    have := h0 (x - y) (by rw [← one_tmul_eq_zero, TensorProduct.tmul_sub, h, sub_self])
    rw [← sub_add_cancel x y, AddChar.map_add_eq_mul, this, one_mul]
  let ψ : AddChar ((O ⧸ P) ⊗[O] M) ℂ :=
    ⟨fun v => χ (l v), by rw [h1 _ 0 (by rw [hl]; simp), AddChar.map_zero_eq_one], fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact h1 _ _ (by rw [TensorProduct.tmul_add, hl, hl, hl])⟩
  haveI := Fintype.ofFinite ((O ⧸ P) ⊗[O] M)
  change ∑ j, ψ (ε.symm j) = _
  rw [ε.symm.sum_comp (fun v => ψ v), AddChar.sum_eq_ite, ← Nat.card_eq_fintype_card, hc]
  refine if_congr ⟨fun h x => ?_, fun h => ?_⟩ rfl rfl
  · rw [← h1 _ _ (hl (1 ⊗ₜ x))]
    exact DFunLike.congr_fun h _
  · ext v
    exact h _
end GlobalTheory.SW.HeckeId
