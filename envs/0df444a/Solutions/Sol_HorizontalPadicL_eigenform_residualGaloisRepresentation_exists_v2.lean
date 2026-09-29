-- Prove2me | solution 1 for HorizontalPadicL.eigenform_residualGaloisRepresentation_exists_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-23T21:56:01.777394+00:00
-- url     : https://prove2.me/submissions/76b25940-22dd-4d01-a25a-8a961f4b72d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MTT_Eigenform_exists_adic_matrix_representation
import Theorems.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Definitions.Def_TaylorWiles_Primes
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Theorems.Thm_NumberField_exists_isFrobenius_lift_arithFrobAt
import Theorems.Thm_NumberField_exists_valuationSubring_eq_localization
import Theorems.Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem

-- From Solutions/ResidualMatrixReduction.lean
set_option autoImplicit false
noncomputable section BundleResidualMatrixReduction

open NumberField

lemma GaloisFactorsThroughFiniteLevel.comp
    {M M' : Type} [MulOneClass M] [MulOneClass M']
    {ρ : (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) →* M}
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (φ : M →* M') :
    GaloisFactorsThroughFiniteLevel (φ.comp ρ) := by
  obtain ⟨L, hL, hfix⟩ := hρ
  exact ⟨L, hL, fun σ hσ ↦ by simp [hfix σ hσ]⟩

namespace MTT.Eigenform

theorem exists_residual_matrix_representation
    {N k p : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    ∃ ρ : (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) →*
        Matrix (Fin 2) (Fin 2) (f.coefficientResidueField ιp),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ : MTT.Qbar ≃ₐ[ℚ] MTT.Qbar, A.IsFrobeniusAt σ l →
            Matrix.trace (ρ σ) = Ideal.Quotient.mk (f.coefficientPrime ιp)
                (f.integralCoeff hN hk l) ∧
            Matrix.det (ρ σ) = Ideal.Quotient.mk (f.coefficientPrime ιp)
                (f.integralNebentype (l : ZMod N) *
                  (l : 𝓞 f.coefficientField) ^ (k - 1))) := by
  obtain ⟨ρ, hfinite, hunram, hfrob⟩ :=
    f.exists_adic_matrix_representation hN hk ι ιp
  let red := f.coefficientReduction ιp
  let ρbar := (red.mapMatrix (m := Fin 2)).toMonoidHom.comp ρ
  refine ⟨ρbar, ?_, ?_, ?_⟩
  · let φ : (𝓞 f.coefficientField) ⧸ f.coefficientPrime ιp ^ 1 →+*
        f.coefficientResidueField ιp := Ideal.Quotient.factor (by simp)
    exact (hfinite 1).comp (φ.mapMatrix (m := Fin 2)).toMonoidHom
  · intro l hl hlNp A hA σ hσ
    change red.mapMatrix (m := Fin 2) (ρ σ) = 1
    rw [hunram l hl hlNp A hA σ hσ, map_one]
  · intro l hl hlNp A hA σ hσ
    obtain ⟨htr, hdet⟩ := hfrob l hl hlNp A hA σ hσ
    constructor
    · change Matrix.trace ((ρ σ).map red) = _
      rw [← AddMonoidHom.map_trace, htr]
      exact f.coefficientReduction_algebraMap ιp _
    · change Matrix.det (red.mapMatrix (ρ σ)) = _
      rw [← RingHom.map_det, hdet]
      exact f.coefficientReduction_algebraMap ιp _

end MTT.Eigenform

end BundleResidualMatrixReduction

-- From Solutions/ResidualFiniteDescent.lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section BundleResidualFiniteDescent

namespace HorizontalPadicL

private local instance : IsGalois ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _

/-- An open-kernel homomorphism of the absolute Galois group has a faithful
realization on the Galois group of a finite Galois number field. -/
theorem exists_faithful_finiteGalois_descent
    {G : Type*} [Group G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (hker : IsOpen (ρ.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField F) (_ : IsGalois ℚ F)
      (ρF : (F ≃ₐ[ℚ] F) →* G),
      Function.Injective ρF ∧ ρF.comp (AlgEquiv.restrictNormalHom F) = ρ := by
  let H : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⟨ρ.ker, ρ.ker.isClosed_of_isOpen hker⟩
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField H.1
  have hfix : F.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have : FiniteDimensional ℚ F :=
    (InfiniteGalois.isOpen_iff_finite F).mp (by
      change IsOpen (F.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      rw [hfix]
      exact hker)
  have : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have : F.fixingSubgroup.Normal := hfix.symm ▸ ρ.normal_ker
  have : IsGalois ℚ F := (InfiniteGalois.normal_iff_isGalois F).mp inferInstance
  let e := InfiniteGalois.normalAutEquivQuotient H
  let ρF : (F ≃ₐ[ℚ] F) →* G :=
    (QuotientGroup.kerLift ρ).comp e.symm.toMonoidHom
  refine ⟨F, inferInstance, inferInstance, ρF, ?_, ?_⟩
  · exact (QuotientGroup.kerLift_injective ρ).comp e.symm.injective
  · ext σ
    change QuotientGroup.kerLift ρ (e.symm (AlgEquiv.restrictNormalHom F σ)) = ρ σ
    rw [← InfiniteGalois.normalAutEquivQuotient_apply H σ]
    change QuotientGroup.kerLift ρ (e.symm (e σ)) = ρ σ
    rw [e.symm_apply_apply]
    exact QuotientGroup.kerLift_mk ρ σ

/-- Continuity into a discrete group supplies the open-kernel hypothesis. -/
theorem exists_faithful_finiteGalois_descent_of_continuous
    {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (hρ : Continuous ρ) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField F) (_ : IsGalois ℚ F)
      (ρF : (F ≃ₐ[ℚ] F) →* G),
      Function.Injective ρF ∧ ρF.comp (AlgEquiv.restrictNormalHom F) = ρ := by
  apply exists_faithful_finiteGalois_descent ρ
  exact (isOpen_discrete ({1} : Set G)).preimage hρ

/-- A finite-level representation with values in any monoid descends faithfully
to a finite Galois number field.  In particular this applies to matrix monoids. -/
theorem exists_faithful_finiteGalois_descent_of_finiteLevel
    {M : Type*} [Monoid M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (hfinite : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ L, σ x = x) → ρ σ = 1) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField F) (_ : IsGalois ℚ F)
      (ρF : (F ≃ₐ[ℚ] F) →* M),
      Function.Injective ρF ∧ ρF.comp (AlgEquiv.restrictNormalHom F) = ρ := by
  obtain ⟨L, hL, hρL⟩ := hfinite
  have hle : L.fixingSubgroup ≤ ρ.toHomUnits.ker := by
    intro σ hσ
    apply Units.ext
    simpa using hρL σ ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ)
  have hker : IsOpen (ρ.toHomUnits.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen L)
  obtain ⟨F, hF, hGal, ρF, hinj, heq⟩ := exists_faithful_finiteGalois_descent ρ.toHomUnits hker
  exact ⟨F, hF, hGal, (Units.coeHom M).comp ρF,
    Units.val_injective.comp hinj, by ext σ; exact congrArg (fun ψ : _ →* Mˣ => ((ψ σ) : M)) heq⟩

open NumberField FrobeniusDensity in
/-- Unramifiedness of the absolute representation descends to the ideal inertia
groups of its faithful finite Galois realization. -/
theorem inertia_eq_bot_of_descended_unramified
    {M : Type*} [Monoid M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* M) (hinj : Function.Injective ρF)
    (heq : ρF.comp (AlgEquiv.restrictNormalHom F) = ρ)
    {l : ℕ} (hl : l.Prime)
    (hunr : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime l →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal l)] :
    Q.inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (ne_bot_of_liesOver_ratPrimeIdeal hl)
  have hlQ : (l : 𝓞 F) ∈ Q := by
    have h : (l : ℤ) ∈ Q.under ℤ := by
      rw [← Q.over_def (ratPrimeIdeal l)]
      exact Ideal.subset_span (by simp)
    change algebraMap ℤ (𝓞 F) (l : ℤ) ∈ Q at h
    simpa using h
  apply le_antisymm _ bot_le
  intro τ hτ
  rw [Subgroup.mem_bot]
  apply hinj
  rw [map_one]
  obtain ⟨σ, hσ, P, hP, hlP, hσP⟩ :=
    NumberField.exists_lift_mem_inertia_integralClosure F Q hlQ τ hτ
  have : P.IsMaximal := hP
  obtain ⟨A, hlA, hσA⟩ :=
    ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn P hl hlP σ hσP
  rw [← hσ]
  change (ρF.comp (AlgEquiv.restrictNormalHom F)) σ = 1
  rw [heq]
  exact hunr A hlA σ hσA

end HorizontalPadicL

end BundleResidualFiniteDescent

-- From Solutions/ResidualFrobeniusLift.lean
section BundleResidualFrobeniusLift

open scoped NumberField Pointwise

namespace NumberField

/-- A chosen finite arithmetic Frobenius has an absolute arithmetic Frobenius lift,
expressed using the valuation-subring convention for absolute Galois representations. -/
theorem exists_valuation_frobenius_lift_arithFrobAt
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E] [IsGalois ℚ E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] [Finite (𝓞 E ⧸ Q)] :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
      AlgEquiv.restrictNormal σ E = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q := by
  obtain ⟨Qt, hQt, σ, hQtQ, hσ, hstable, hfrob⟩ :=
    NumberField.exists_isFrobenius_lift_arithFrobAt E ℓ hℓ Q
  let : Qt.IsMaximal := hQt
  let : Qt.LiesOver Q := hQtQ
  have hℓQ : ((ℓ : ℤ) : 𝓞 E) ∈ Q := by
    have hmem := (Ideal.mem_of_liesOver Q (FrobeniusDensity.ratPrimeIdeal ℓ)
      (ℓ : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using hmem
  have hℓQt : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt := by
    have hmem := (Ideal.mem_of_liesOver Qt Q ((ℓ : ℤ) : 𝓞 E)).mp hℓQ
    simpa using hmem
  obtain ⟨A, hA⟩ := NumberField.exists_valuationSubring_eq_localization Qt
  obtain ⟨hAlies, hAfrob⟩ :=
    ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem
      Qt ℓ hℓ hℓQt σ hstable hfrob A hA
  exact ⟨A, σ, hAlies, hAfrob, hσ⟩

end NumberField

end BundleResidualFrobeniusLift

-- From Solutions/ResidualGaloisSolution.lean
set_option autoImplicit false
noncomputable section BundleResidualGaloisSolution

open NumberField HorizontalPadicL FrobeniusDensity

theorem solution {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    Nonempty (EigenformResidualGaloisRepresentationData hN hk f ιp) := by
  obtain ⟨ρ, hfinite, hunram, hfrob⟩ :=
    f.exists_residual_matrix_representation hN hk ι ιp
  obtain ⟨F, hF, hGal, ρF, hinj, heq⟩ :=
    exists_faithful_finiteGalois_descent_of_finiteLevel ρ hfinite
  let : NumberField F := hF
  let : IsGalois ℚ F := hGal
  have hfrobF (l : ℕ) (hl : l.Prime) (hlNp : Nat.Coprime l (N * p))
      (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal l)]
      [Finite (𝓞 F ⧸ Q)] :
      Matrix.trace (ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q)) =
          Ideal.Quotient.mk (f.coefficientPrime ιp) (f.integralCoeff hN hk l) ∧
        Matrix.det (ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q)) =
          Ideal.Quotient.mk (f.coefficientPrime ιp)
            (f.integralNebentype (l : ZMod N) *
              (l : 𝓞 f.coefficientField) ^ (k - 1)) := by
    obtain ⟨A, σ, hA, hσ, hrestrict⟩ :=
      NumberField.exists_valuation_frobenius_lift_arithFrobAt F l hl Q
    have hvalue : ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) = ρ σ := by
      rw [← hrestrict]
      exact congrArg (fun ψ ↦ ψ σ) heq
    rw [hvalue]
    exact hfrob l hl hlNp A hA σ hσ
  refine ⟨{
    kernelField := F
    representation := ρF
    faithful := hinj
    unramified_outside := ?_
    trace_frobenius := ?_
    det_frobenius := ?_ }⟩
  · intro l hl hlNp Q hQ hQlies
    let : Q.IsPrime := hQ
    let : Q.LiesOver (ratPrimeIdeal l) := hQlies
    exact inertia_eq_bot_of_descended_unramified ρ F ρF hinj heq hl
      (hunram l hl hlNp) Q
  · intro l hl hlNp Q hQ hQlies
    let : Q.IsPrime := hQ
    let : Q.LiesOver (ratPrimeIdeal l) := hQlies
    let : Finite (𝓞 F ⧸ Q) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hl)
    exact (hfrobF l hl hlNp Q).1
  · intro l hl hlNp Q hQ hQlies
    let : Q.IsPrime := hQ
    let : Q.LiesOver (ratPrimeIdeal l) := hQlies
    let : Finite (𝓞 F ⧸ Q) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hl)
    exact (hfrobF l hl hlNp Q).2

end BundleResidualGaloisSolution
