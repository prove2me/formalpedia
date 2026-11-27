-- Prove2me | solution 1 for GlobalTheory.exists_arithFrobenius_absGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:23.476194+00:00
-- url     : https://prove2.me/submissions/bbf1f7a0-d12f-41eb-95d3-a11aeb53b5ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsArithFrobeniusAbsGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (hfin : Finite (IsLocalRing.ResidueField V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)] : ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω) := by
  classical
  haveI : Algebra.IsIntegral K Ω := inferInstance
  letI : TopologicalSpace (integralClosure V Ω) := ⊥
  haveI : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  haveI : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := K) (L := Ω) (x : Ω) using 2
    ext g
    simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  haveI : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    refine ⟨fun x hx => ?_⟩
    have hmem : (x : Ω) ∈ IntermediateField.fixedField (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) := by
      rintro ⟨g, -⟩
      exact congrArg Subtype.val (hx g)
    rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hx2 : IsIntegral V (x : Ω) := x.2
    rw [← hk] at hx2
    have hint : IsIntegral V k :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom V K Ω) (algebraMap K Ω).injective).mp hx2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨v, Subtype.ext ?_⟩
    simp [IsScalarTower.algebraMap_apply V K Ω, hv, hk]
  haveI : (maximalIdeal (integralClosure V Ω)).LiesOver (maximalIdeal V) := by
    refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  letI : Fintype (V ⧸ maximalIdeal V) := @Fintype.ofFinite _ hfin
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  letI : Field (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) :=
    Ideal.Quotient.field _
  haveI : Algebra.IsIntegral (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := inferInstance
  haveI : Algebra.IsAlgebraic (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := Algebra.IsIntegral.isAlgebraic
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) (maximalIdeal (integralClosure V Ω))
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  refine ⟨g.1, fun x => ⟨g.1 • x, rfl, ?_⟩⟩
  rw [← Ideal.Quotient.eq]
  have h := congrArg (fun e => e (Ideal.Quotient.mk (maximalIdeal (integralClosure V Ω)) x)) hg
  simp only [Ideal.Quotient.stabilizerHom_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply] at h
  rw [Fintype.card_eq_nat_card] at h
  rw [map_pow]
  exact h
end _root_.GlobalTheory
end GlobalTheory
