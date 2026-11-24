-- Prove2me | solution 1 for GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:14.494284+00:00
-- url     : https://prove2.me/submissions/0abd9a57-5267-48eb-ae87-4554f617fefe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecialization
import Theorems.Thm_GlobalTheory_PrimTransc_exists_separable_specialization
import Theorems.Thm_GlobalTheory_PrimTransc_exists_mul_mem_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open GlobalTheory GlobalTheory.PrimTransc
namespace GlobalTheory.PrimTransc
theorem _root_.solution :
    ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x →
      ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ))
        (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧
        (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧
        (P.map (MvPolynomial.eval c)).Separable := by
  intro K _ _ D x hx J _ e
  classical
  have := Fintype.ofFinite J
  let R := MvPolynomial (Fin D) ℚ
  let F := FractionRing R
  let φ : R →ₐ[ℚ] K := MvPolynomial.aeval x
  have φinj : Function.Injective φ := hx.1
  letI : Algebra R K := φ.toRingHom.toAlgebra
  have hφ : ∀ r : R, algebraMap R K r = φ r := fun r => rfl
  haveI : IsScalarTower ℚ R K := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 φinj
  letI : Algebra F K := FractionRing.liftAlgebra R K
  haveI : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K
  haveI : CharZero F := RingHom.charZero (algebraMap F K)
  haveI : Algebra.IsAlgebraic R K :=
    haveI := hx.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hx.1.aevalEquiv.symm.toRingHom) (g := RingHom.id K)
      (Algebra.IsAlgebraic.isAlgebraic y) hx.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hx.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra, φ]))⟩
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R F)

  let E := IntermediateField.adjoin F (Set.range e)
  haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
    (fun y _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) y).isIntegral)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hαE : F⟮(α : K)⟯ = E := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congrArg IntermediateField.lift hα
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic (R := R) (α : K))
  set θ : K := y • (α : K) with hθdef
  have hθF : IsIntegral F θ := (Algebra.IsAlgebraic.isAlgebraic (R := F) θ).isIntegral
  have hyF : algebraMap R F y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hy0
  have hαθ : (α : K) ∈ F⟮θ⟯ := by
    have : (α : K) = algebraMap F K (algebraMap R F y)⁻¹ * θ := by
      rw [hθdef, Algebra.smul_def, IsScalarTower.algebraMap_apply R F K, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hyF, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F θ)
  have heθ : ∀ j, e j ∈ Algebra.adjoin F {θ} := by
    intro j
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθF.isAlgebraic]
    have h1 : E ≤ F⟮θ⟯ := hαE ▸ IntermediateField.adjoin_simple_le_iff.2 hαθ
    exact h1 (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  choose d hd0 hdm using fun j => exists_mul_mem_adjoin (R := R) (F := F) θ (e j) (heθ j)

  let P := minpoly R θ
  let ψ₀ : AdjoinRoot P →ₐ[R] K := AdjoinRoot.liftAlgHom P (Algebra.ofId R K) θ (minpoly.aeval R θ)
  let ψ : AdjoinRoot P →ₐ[ℚ] K := ψ₀.restrictScalars ℚ
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun q hq => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective q
    have hq' : Polynomial.aeval θ q = 0 := hq
    exact AdjoinRoot.mk_eq_zero.2 ((minpoly.isIntegrallyClosed_dvd_iff hyint q).1 hq')
  have hrange : Algebra.adjoin R {θ} ≤ ψ₀.range := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨AdjoinRoot.root P, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
  have hsep : (P.map (algebraMap R F)).Separable := by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F hyint]
    exact (minpoly.irreducible hθF).separable
  obtain ⟨c, hc⟩ := exists_separable_specialization P hsep
  refine ⟨P, ψ, algebraMap R K (∏ j, d j), c, minpoly.monic hyint, hψinj, fun i => ?_, ?_, fun j => ?_, hc⟩
  · show ψ₀ (AdjoinRoot.of P (MvPolynomial.X i)) = x i
    rw [← AdjoinRoot.algebraMap_eq, AlgHom.commutes, hφ]
    exact MvPolynomial.aeval_X x i
  · exact (map_ne_zero_iff _ φinj).2 (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j)
  · have hm : algebraMap R K (∏ j, d j) * e j ∈ Algebra.adjoin R {θ} := by
      rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ j), mul_comm (d j), map_mul, mul_assoc]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdm j)
    obtain ⟨a, ha⟩ := hrange hm
    exact ⟨a, ha⟩
end GlobalTheory.PrimTransc
