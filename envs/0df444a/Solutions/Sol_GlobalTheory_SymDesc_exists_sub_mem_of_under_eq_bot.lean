-- Prove2me | solution 1 for GlobalTheory.SymDesc.exists_sub_mem_of_under_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:10.4448+00:00
-- url     : https://prove2.me/submissions/8baa7688-0ca0-4f56-b997-24f2cfb8ae2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat
import Theorems.Thm_GlobalTheory_SymDesc_injective_quotient
import Theorems.Thm_GlobalTheory_mem_range_of_forall_algHom_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SymDesc
variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]
namespace GlobalTheory.SymDesc
theorem _root_.solution [IsIntegrallyClosed R] [CharZero R]
    [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q : Ideal R₁) [Q.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    ∃ e : R, s - algebraMap R R₁ e ∈ Q := by
  classical
  let A := R₁ ⧸ Q
  let K₀ := FractionRing A
  let F := FractionRing R
  have hRA : Function.Injective (algebraMap R A) := injective_quotient Q hQ
  have hRK : Function.Injective (algebraMap R K₀) := by
    rw [IsScalarTower.algebraMap_eq R A K₀]
    exact (IsFractionRing.injective A K₀).comp hRA
  haveI : FaithfulSMul R K₀ := (faithfulSMul_iff_algebraMap_injective R K₀).2 hRK
  letI : Algebra F K₀ := FractionRing.liftAlgebra R K₀
  haveI : IsScalarTower R F K₀ := FractionRing.isScalarTower_liftAlgebra R K₀
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hRA
  haveI : Algebra.IsAlgebraic R A := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R K₀ := (IsFractionRing.isAlgebraic_iff' R A K₀).1 inferInstance
  haveI : Algebra.IsAlgebraic F K₀ :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff R F K₀).1 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  let π : R₁ →+* K₀ := (algebraMap A K₀).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ r : R, π (algebraMap R R₁ r) = algebraMap F K₀ (algebraMap R F r) := by
    intro r
    have hq : (Ideal.Quotient.mk Q) ((algebraMap R R₁) r) = algebraMap R A r := by
      first | rfl | exact Ideal.Quotient.mk_algebraMap _ _ | simp [A]
    simp only [π, RingHom.comp_apply]
    rw [hq, ← IsScalarTower.algebraMap_apply R A K₀, ← IsScalarTower.algebraMap_apply R F K₀]
  obtain ⟨e', he'⟩ := GlobalTheory.mem_range_of_forall_algHom_eq F K₀ inferInstance (π s) (by
    intro Ω _ _ φ₁ φ₂
    have h := hs Ω (φ₁.toRingHom.comp π) (φ₂.toRingHom.comp π) (by
      ext r
      simp only [RingHom.comp_apply, hπ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes])
    simpa using h)
  have hint : IsIntegral R (π s) := by
    have h1 : IsIntegral R (Ideal.Quotient.mk Q s) := Algebra.IsIntegral.isIntegral _
    exact h1.map (IsScalarTower.toAlgHom R A K₀)
  rw [← he'] at hint
  have hint' : IsIntegral R e' :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R F K₀) (algebraMap F K₀).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsFractionRing.injective A K₀
  rw [map_zero]
  have h : π (s - algebraMap R R₁ y) = 0 := by
    rw [map_sub, hπ, hy, he', sub_self]
  exact h
end GlobalTheory.SymDesc
