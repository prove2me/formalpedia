-- Prove2me | solution 1 for ModularCurve.rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0c4f7358-e1c5-5e35-9899-20548fa74991

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_EisensteinIdeal
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_JZero_exists_finiteDimensional_fixingSubgroup_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve

namespace C5Prime

variable (p : ℕ) [NeZero p]

theorem galois_smul_hecke_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlg) (x : JZero p) :
    letI := heckeModuleBar p
    σ • (t • x) = t • (σ • x) := by
  letI := heckeModuleBar p
  haveI := smulCommClass_JZero_of_heckeOperatorsCommuteBar p (heckeOperatorsCommuteBar p)
  exact smul_comm σ t x

omit [NeZero p] in
theorem gal_smul_add (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : JZero p) :
    σ • (x + y) = σ • x + σ • y := by
  rw [galois_smul_pic0_def, galois_smul_pic0_def, galois_smul_pic0_def, smul_add]

omit [NeZero p] in
theorem gal_smul_sub (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : JZero p) :
    σ • (x - y) = σ • x - σ • y := by
  rw [galois_smul_pic0_def, galois_smul_pic0_def, galois_smul_pic0_def, smul_sub]

omit [NeZero p] in
theorem gal_mul_smul (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p) :
    (σ * τ) • x = σ • (τ • x) := by
  rw [galois_smul_pic0_def, galois_smul_pic0_def, galois_smul_pic0_def, map_mul, mul_smul]

omit [NeZero p] in
theorem gal_smul_zero (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : σ • (0 : JZero p) = 0 := by
  have h := gal_smul_add p σ 0 0
  rw [add_zero] at h
  have h' : σ • (0 : JZero p) + 0 = σ • (0 : JZero p) + σ • (0 : JZero p) := by rwa [add_zero]
  exact (add_left_cancel h').symm

theorem hecke_smul_zero (c : HeckeAlg) :
    (letI := heckeModuleBar p; c • (0 : JZero p)) = 0 := by
  letI := heckeModuleBar p
  have h : c • ((0 : JZero p) + 0) = c • (0 : JZero p) + c • (0 : JZero p) := smul_add c 0 0
  rw [add_zero] at h
  have h' : c • (0 : JZero p) + 0 = c • (0 : JZero p) + c • (0 : JZero p) := by rwa [add_zero]
  exact (add_left_cancel h').symm

def Good (s : HeckeAlg) : Prop := eisensteinEval p s = 1

omit [NeZero p] in
theorem good_one : Good p 1 := map_one _

omit [NeZero p] in
theorem good_mul {s t : HeckeAlg} (hs : Good p s) (ht : Good p t) : Good p (s * t) := by
  unfold Good at *
  rw [map_mul, hs, ht, mul_one]

omit [NeZero p] in
theorem not_mem_of_good (q : ℕ) [Fact q.Prime] {s : HeckeAlg} (hs : Good p s) :
    s ∉ eisensteinMaximalIdeal p q := by
  rw [mem_eisensteinMaximalIdeal_iff]
  unfold Good at hs
  rw [hs]
  intro hdvd
  have hq1 : q ∣ 1 := by exact_mod_cast hdvd
  exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hq1)

theorem exists_good_smul_eq_zero (y : JZero p)
    (hy : y ∈ eisensteinKernelSubmodule p (heckeModuleBar p)) :
    letI := heckeModuleBar p
    ∃ s : HeckeAlg, Good p s ∧ s • y = 0 := by
  letI := heckeModuleBar p
  change y ∈ eisensteinKernel (JZero p) (eisensteinIdeal p) • (⊤ : Submodule HeckeAlg (JZero p)) at hy
  refine Submodule.smul_induction_on hy (fun γ hγ x _ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · obtain ⟨i, hi, hγi⟩ := hγ
    refine ⟨1 + i, ?_, ?_⟩
    · show eisensteinEval p (1 + i) = 1
      have h0 : eisensteinEval p i = 0 := (mem_eigenIdeal_iff _ _).mp hi
      rw [map_add, map_one, h0, add_zero]
    · rw [← mul_smul]
      exact hγi x
  · obtain ⟨s₁, g₁, e₁⟩ := h₁
    obtain ⟨s₂, g₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, good_mul p g₁ g₂, ?_⟩
    have e₁' : (s₁ * s₂) • y₁ = 0 := by
      rw [mul_comm, mul_smul, e₁]; exact hecke_smul_zero p _
    have e₂' : (s₁ * s₂) • y₂ = 0 := by
      rw [mul_smul, e₂]; exact hecke_smul_zero p _
    rw [smul_add, e₁', e₂', add_zero]

theorem finite_orbit (x : JZero p) :
    (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => σ • x).Finite := by
  classical
  obtain ⟨L₀, hfd, hfix⟩ := JZero.exists_finiteDimensional_fixingSubgroup_smul_eq p x
  haveI := hfd
  let r : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → (L₀ →ₐ[ℚ] AlgebraicClosure ℚ) :=
    fun σ => σ.toAlgHom.comp L₀.val
  have key : ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, r σ = r τ → σ • x = τ • x := by
    intro σ τ h
    have hmem : σ⁻¹ * τ ∈ L₀.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hy' : σ y = τ y := congrArg (fun f : L₀ →ₐ[ℚ] AlgebraicClosure ℚ => f ⟨y, hy⟩) h
      show σ.symm (τ y) = y
      rw [← hy']
      exact σ.symm_apply_apply y
    have hx := hfix _ hmem
    calc σ • x = σ • ((σ⁻¹ * τ) • x) := by rw [hx]
      _ = τ • x := by rw [← gal_mul_smul, mul_inv_cancel_left]
  let φ : (L₀ →ₐ[ℚ] AlgebraicClosure ℚ) → JZero p :=
    fun e => if h : ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, r σ = e then h.choose • x else x
  have hsub : (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => σ • x) ⊆ Set.range φ := by
    rintro _ ⟨σ, rfl⟩
    have h : ∃ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, r σ' = r σ := ⟨σ, rfl⟩
    refine ⟨r σ, ?_⟩
    show (if h : ∃ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, r σ' = r σ then h.choose • x else x) = σ • x
    rw [dif_pos h]
    exact key _ _ h.choose_spec
  exact (Set.finite_range φ).subset hsub

theorem exists_good_forall_smul_sub_eq_zero (x₀ : JZero p)
    (hx₀ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ • x₀ - x₀ ∈ eisensteinKernelSubmodule p (heckeModuleBar p)) :
    letI := heckeModuleBar p
    ∃ S : HeckeAlg, Good p S ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, S • (σ • x₀ - x₀) = 0 := by
  letI := heckeModuleBar p
  classical
  have hfin : (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => σ • x₀ - x₀).Finite := by
    refine ((finite_orbit p x₀).image (fun y => y - x₀)).subset ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨σ • x₀, ⟨σ, rfl⟩, rfl⟩
  have hw : ∀ v ∈ hfin.toFinset, ∃ s : HeckeAlg, Good p s ∧ s • v = 0 := by
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    obtain ⟨σ, rfl⟩ := hv
    exact exists_good_smul_eq_zero p _ (hx₀ σ)
  choose s hs hsv using hw
  let w : JZero p → HeckeAlg := fun v => if hv : v ∈ hfin.toFinset then s v hv else 1
  have hw_mem : ∀ v (hv : v ∈ hfin.toFinset), w v = s v hv := fun v hv => dif_pos hv
  refine ⟨∏ v ∈ hfin.toFinset, w v, ?_, ?_⟩
  · refine Finset.prod_induction w (Good p) (fun a b ha hb => good_mul p ha hb) (good_one p) ?_
    intro v hv
    rw [hw_mem v hv]
    exact hs v hv
  · intro σ
    have hv : σ • x₀ - x₀ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨σ, rfl⟩
    rw [← Finset.prod_erase_mul _ _ hv, mul_smul, hw_mem _ hv, hsv _ hv]
    exact hecke_smul_zero p _

set_option maxHeartbeats 3200000 in
theorem main (q : ℕ) [Fact q.Prime] :
    letI := heckeModuleBar p
    (∀ x : JZero p, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • x = x) →
        eisensteinQuotientMk p (heckeModuleBar p) x = 0 →
        ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ s • x = 0) ∧
    (∀ z ∈ Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)),
        ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧
          ∃ x : JZero p, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • x = x) ∧
            s • z = eisensteinQuotientMk p (heckeModuleBar p) x) := by
  letI := heckeModuleBar p
  refine ⟨?_, ?_⟩
  · intro x _ hx
    have hxmem : x ∈ eisensteinKernelSubmodule p (heckeModuleBar p) := by
      have : (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ x = 0 := hx
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨s, hs, hsx⟩ := exists_good_smul_eq_zero p x hxmem
    exact ⟨s, not_mem_of_good p q hs, hsx⟩
  · intro z hz
    suffices h : ∃ s : HeckeAlg, Good p s ∧ ∃ x : JZero p,
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • x = x) ∧
          s • z = eisensteinQuotientMk p (heckeModuleBar p) x by
      obtain ⟨s, hs, x, hx, e⟩ := h
      exact ⟨s, not_mem_of_good p q hs, x, hx, e⟩
    induction hz using Submodule.span_induction with
    | mem z hzmem =>
      obtain ⟨x₀, hx₀, rfl⟩ := hzmem
      obtain ⟨S, hS, hkill⟩ := exists_good_forall_smul_sub_eq_zero p x₀ hx₀
      refine ⟨S, hS, S • x₀, fun σ => ?_, ?_⟩
      · rw [galois_smul_hecke_smul]
        have h := hkill σ
        rw [smul_sub, sub_eq_zero] at h
        exact h
      · change S • (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ x₀
          = (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ (S • x₀)
        rw [map_smul]
    | zero =>
      exact ⟨1, good_one p, 0, fun σ => gal_smul_zero p σ, by rw [smul_zero, map_zero]⟩
    | add z₁ z₂ _ _ ih₁ ih₂ =>
      obtain ⟨s₁, g₁, x₁, hx₁, e₁⟩ := ih₁
      obtain ⟨s₂, g₂, x₂, hx₂, e₂⟩ := ih₂
      refine ⟨s₁ * s₂, good_mul p g₁ g₂, s₂ • x₁ + s₁ • x₂, fun σ => ?_, ?_⟩
      · rw [gal_smul_add, galois_smul_hecke_smul, galois_smul_hecke_smul, hx₁, hx₂]
      · have e₁' : (s₁ * s₂) • z₁ = (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ (s₂ • x₁) := by
          rw [mul_comm, mul_smul, e₁]
          change s₂ • (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ x₁ = _
          rw [map_smul]
        have e₂' : (s₁ * s₂) • z₂ = (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ (s₁ • x₂) := by
          rw [mul_smul, e₂]
          change s₁ • (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ x₂ = _
          rw [map_smul]
        rw [smul_add, e₁', e₂']
        change _ = (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ (s₂ • x₁ + s₁ • x₂)
        rw [map_add]
    | smul t z _ ih =>
      obtain ⟨s, g, x, hx, e⟩ := ih
      refine ⟨s, g, t • x, fun σ => by rw [galois_smul_hecke_smul, hx], ?_⟩
      rw [← mul_smul, mul_comm, mul_smul, e]
      change t • (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ x
        = (eisensteinKernelSubmodule p (heckeModuleBar p)).mkQ (t • x)
      rw [map_smul]

end C5Prime

theorem solution
    (p : ℕ) [NeZero p] (q : ℕ) [Fact q.Prime] :
    letI := heckeModuleBar p
    (∀ x : JZero p, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • x = x) →
        eisensteinQuotientMk p (heckeModuleBar p) x = 0 →
        ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ s • x = 0) ∧
    (∀ z ∈ Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)),
        ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧
          ∃ x : JZero p, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • x = x) ∧
            s • z = eisensteinQuotientMk p (heckeModuleBar p) x) :=
  C5Prime.main p q

end S_ModularCurve_rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional
end P2MW
export P2MW.S_ModularCurve_rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional (solution)
