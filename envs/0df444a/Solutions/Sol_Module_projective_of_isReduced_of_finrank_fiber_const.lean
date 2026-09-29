-- Prove2me | solution 1 for Module.projective_of_isReduced_of_finrank_fiber_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c5a4f260-47ec-54e1-95db-fceda02f6a4a

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_projective_of_isReduced_of_finrank_fiber_const

set_option autoImplicit false

noncomputable section

universe u v

open scoped TensorProduct

namespace CBCSol

section FittingFree

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

abbrev κ (𝔭 : PrimeSpectrum R) : Type u := 𝔭.asIdeal.ResidueField

theorem span_one_tmul_eq_top (𝔭 : PrimeSpectrum R) :
    Submodule.span (κ 𝔭) (Set.range fun x : M => (1 : κ 𝔭) ⊗ₜ[R] x) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x =>
    have : a ⊗ₜ[R] x = a • ((1 : κ 𝔭) ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add s t hs ht => exact Submodule.add_mem _ hs ht

theorem exists_basis_one_tmul [Module.Finite R M] (𝔭 : PrimeSpectrum R) :
    ∃ (ι : Type v) (_ : Fintype ι) (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M)),
      ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i := by
  obtain ⟨ι, a, -, haspan, hli⟩ :=
    exists_linearIndependent' (κ 𝔭) (fun x : M => (1 : κ 𝔭) ⊗ₜ[R] x)
  haveI : Finite ι := hli.finite_of_isNoetherian
  let _ : Fintype ι := Fintype.ofFinite ι
  refine ⟨ι, inferInstance, a, Module.Basis.mk hli ?_, fun i => ?_⟩
  · rw [haspan, span_one_tmul_eq_top]
  · simp only [Module.Basis.mk_apply, Function.comp_apply]

theorem subsingleton_residue_tensor_coker (𝔭 : PrimeSpectrum R) {ι : Type v} [Fintype ι]
    (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M)) (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) :
    Subsingleton (κ 𝔭 ⊗[R] (M ⧸ LinearMap.range (Fintype.linearCombination R m))) := by
  classical
  set φ := Fintype.linearCombination R m with hφ
  have hrange : LinearMap.range (φ.baseChange (κ 𝔭)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(1 : κ 𝔭) ⊗ₜ[R] Pi.single i 1, ?_⟩
    rw [LinearMap.baseChange_tmul, hb i, hφ, Fintype.linearCombination_apply_single, one_smul]
  have hexact : Function.Exact (φ.baseChange (κ 𝔭))
      ((LinearMap.range φ).mkQ.baseChange (κ 𝔭)) := by
    have := lTensor_exact (κ 𝔭) (LinearMap.exact_map_mkQ_range φ)
      (Submodule.Quotient.mk_surjective _)
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hsurj : Function.Surjective ((LinearMap.range φ).mkQ.baseChange (κ 𝔭)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.Quotient.mk_surjective _)
  have hker : LinearMap.ker ((LinearMap.range φ).mkQ.baseChange (κ 𝔭)) = ⊤ := by
    rw [LinearMap.exact_iff.mp hexact, hrange]
  have hzero : (LinearMap.range φ).mkQ.baseChange (κ 𝔭) = 0 := LinearMap.ker_eq_top.mp hker
  refine ⟨fun p q => ?_⟩
  obtain ⟨p', rfl⟩ := hsurj p
  obtain ⟨q', rfl⟩ := hsurj q
  rw [hzero]
  rfl

theorem baseChange_injective_of_le [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) {ι : Type v}
    [Fintype ι] (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) {𝔮 : PrimeSpectrum R} (hle : 𝔮 ≤ 𝔭) :
    Function.Injective ((Fintype.linearCombination R m).baseChange (κ 𝔮)) := by
  set φ := Fintype.linearCombination R m with hφ
  set M' := M ⧸ LinearMap.range φ
  have h𝔭 : 𝔭 ∉ Module.support R M' := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact subsingleton_residue_tensor_coker 𝔭 m b hb
  have h𝔮 : 𝔮 ∉ Module.support R M' := fun h => h𝔭 (Module.mem_support_mono hle h)
  have hsub : Subsingleton (κ 𝔮 ⊗[R] M') := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton] at h𝔮
    exact h𝔮
  have hexact : Function.Exact (φ.baseChange (κ 𝔮))
      ((LinearMap.range φ).mkQ.baseChange (κ 𝔮)) := by
    have := lTensor_exact (κ 𝔮) (LinearMap.exact_map_mkQ_range φ)
      (Submodule.Quotient.mk_surjective _)
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hsurjφ : Function.Surjective (φ.baseChange (κ 𝔮)) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.exact_iff.mp hexact, LinearMap.ker_eq_top]
    ext x
    exact hsub.elim _ _
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact (inferInstance : IsEmpty (PrimeSpectrum R)).false 𝔮
  haveI : StrongRankCondition R := commRing_strongRankCondition R
  have hdom : Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] (ι → R)) = e := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
      ← hconst 𝔭, Module.finrank_eq_card_basis b]
  have hcod : Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e := hconst 𝔮
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdom.trans hcod.symm)).mpr
    hsurjφ

theorem coeff_mem_of_rel [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) {ι : Type v} [Fintype ι]
    (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) {𝔮 : PrimeSpectrum R} (hle : 𝔮 ≤ 𝔭)
    (x : ι → R) (hx : Fintype.linearCombination R m x = 0) (i : ι) : x i ∈ 𝔮.asIdeal := by
  classical
  have hinj := baseChange_injective_of_le hconst 𝔭 m b hb hle
  have h1x : (1 : κ 𝔮) ⊗ₜ[R] x = 0 := by
    apply hinj
    rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_zero, map_zero]
  have hcoord : TensorProduct.piScalarRight R (κ 𝔮) (κ 𝔮) ι ((1 : κ 𝔮) ⊗ₜ[R] x) i = 0 := by
    rw [h1x, map_zero, Pi.zero_apply]
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul] at hcoord
  rw [← Ideal.ker_algebraMap_residueField 𝔮.asIdeal, RingHom.mem_ker,
    Algebra.algebraMap_eq_smul_one]
  exact hcoord

theorem algebraMap_coeff_eq_zero [IsReduced R] [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R)
    {ι : Type v} [Fintype ι] (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i)
    (x : ι → R) (hx : Fintype.linearCombination R m x = 0) (i : ι) :
    algebraMap R (Localization.AtPrime 𝔭.asIdeal) (x i) = 0 := by
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  have hdis := ((IsLocalization.isPrime_iff_isPrime_disjoint 𝔭.asIdeal.primeCompl
    (Localization.AtPrime 𝔭.asIdeal) P).mp hP)
  let 𝔮 : PrimeSpectrum R := ⟨P.under R, hdis.1⟩
  have hle : 𝔮 ≤ 𝔭 := by
    intro r hr
    by_contra hnot
    exact Set.disjoint_left.mp hdis.2 hnot hr
  have hmem : x i ∈ 𝔮.asIdeal := coeff_mem_of_rel hconst 𝔭 m b hb hle x hx i
  exact Ideal.mem_comap.mp hmem

theorem free_localizedModule_of_isReduced [IsReduced R] [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) :
    Module.Free (Localization.AtPrime 𝔭.asIdeal)
      (LocalizedModule 𝔭.asIdeal.primeCompl M) := by
  classical
  obtain ⟨ι, _, m, b, hb⟩ := exists_basis_one_tmul (M := M) 𝔭
  set Rp := Localization.AtPrime 𝔭.asIdeal
  set S := 𝔭.asIdeal.primeCompl
  set Mp := LocalizedModule S M
  let f : M →ₗ[R] Mp := LocalizedModule.mkLinearMap S M
  let bv : ι → Mp := fun i => f (m i)
  have hspan : Submodule.span Rp (Set.range bv) = ⊤ := by
    let ebc : Rp ⊗[R] M ≃ₗ[Rp] Mp := (IsLocalizedModule.isBaseChange S Rp f).equiv
    let E : κ 𝔭 ⊗[Rp] Mp ≃ₗ[κ 𝔭] κ 𝔭 ⊗[R] M :=
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (κ 𝔭) (κ 𝔭)) ebc.symm)
        ≪≫ₗ TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp (κ 𝔭) (κ 𝔭) M
    refine IsLocalRing.span_eq_top_of_tmul_eq_basis (R := Rp) bv (b.map E.symm) ?_
    intro i
    rw [Module.Basis.map_apply, LinearEquiv.eq_symm_apply, hb i]
    simp only [E, bv, f, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
      LinearEquiv.refl_apply]
    have hsymm : ebc.symm (LocalizedModule.mkLinearMap S M (m i)) = (1 : Rp) ⊗ₜ[R] m i := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rw [hsymm, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  have hli : LinearIndependent Rp bv := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite S c
    choose r hr using hs
    have hrel : f (∑ j, r j • m j) = 0 := by
      have : ∑ j, (algebraMap R Rp (r j)) • bv j = (s : R) • ∑ j, c j • bv j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hr j, smul_assoc]
      rw [hc, smul_zero] at this
      rw [map_sum]
      simpa only [bv, map_smul, algebraMap_smul] using this
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S f).mp hrel
    have hx : Fintype.linearCombination R m (fun j => (t : R) * r j) = 0 := by
      rw [Fintype.linearCombination_apply]
      simp only [mul_smul, ← Finset.smul_sum] at ht ⊢
      exact ht
    have hzero := algebraMap_coeff_eq_zero hconst 𝔭 m b hb _ hx i
    rw [map_mul] at hzero
    have ht_unit : IsUnit (algebraMap R Rp (t : R)) := IsLocalization.map_units Rp t
    have hri : algebraMap R Rp (r i) = 0 := (ht_unit.mul_right_eq_zero).mp hzero
    have hs_unit : IsUnit (algebraMap R Rp (s : R)) := IsLocalization.map_units Rp s
    have : (s : R) • c i = 0 := by rw [← hr i, hri]
    rw [Algebra.smul_def] at this
    exact (hs_unit.mul_right_eq_zero).mp this
  exact Module.Free.of_basis (Module.Basis.mk hli (by rw [hspan]))

theorem projective_of_isReduced_of_finrank_const [IsReduced R] [Module.FinitePresentation R M]
    {e : ℕ} (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e) :
    Module.Projective R M := by
  refine Module.projective_of_localization_maximal (fun I hI => ?_)
  haveI := free_localizedModule_of_isReduced hconst ⟨I, hI.isPrime⟩
  exact Module.Projective.of_free

end FittingFree

end CBCSol

theorem solution {R : Type u} [CommRing R]
    [IsReduced R] {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    {e : ℕ} (h : ∀ 𝔭 : PrimeSpectrum R,
      Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] M) = e) :
    Module.Projective R M :=
  CBCSol.projective_of_isReduced_of_finrank_const h

end
end S_Module_projective_of_isReduced_of_finrank_fiber_const
end P2MW
export P2MW.S_Module_projective_of_isReduced_of_finrank_fiber_const (solution)
