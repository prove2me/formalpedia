-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f54efead-a479-5811-9ac3-58bfb9b13d1c

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness
import Theorems.Thm_DrinfeldCurve_isDedekindDomain_coordRing
import Theorems.Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one
import Theorems.Thm_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

namespace SpecialFibre

open TensorProduct

theorem surjective_and_ker_eq_span_pi {B R : Type*} [CommRing B] [CommRing R] {ι : Type*} [Finite ι]
    (p : B) (𝔓 : Ideal B) [𝔓.IsPrime] (hp : p ∈ 𝔓)
    (ρ : B →+* R) (hρs : Function.Surjective ρ) (hρ : ∀ b, ρ b = 0 ↔ b ∈ 𝔓)
    (i₁ : B) (hi₁ : i₁ - 1 ∈ 𝔓) (hprin : ∀ g ∈ 𝔓, ∃ b, g * i₁ = p * b)
    (θ : ι → B ≃+* B) (hθp : ∀ t, θ t p = p)
    (hcover : ∀ Q : Ideal B, Q.IsPrime → p ∈ Q → ∃ t, ∀ z ∈ 𝔓, (θ t).symm z ∈ Q)
    (hsep : ∀ t t', t ≠ t' → ∃ c c' : B, θ t c ∈ 𝔓 ∧ θ t' c' ∈ 𝔓 ∧ c + c' = 1) :
    Function.Surjective (RingHom.pi fun t => ρ.comp (θ t).toRingHom) ∧
      ∀ b, (RingHom.pi fun t => ρ.comp (θ t).toRingHom) b = 0 ↔ b ∈ Ideal.span {p} := by
  classical
  let P : ι → Ideal B := fun t => 𝔓.comap (θ t).toRingHom
  have hPmem : ∀ t b, b ∈ P t ↔ θ t b ∈ 𝔓 := fun t b => Ideal.mem_comap
  have hcop : Pairwise (fun t t' => IsCoprime (P t) (P t')) := by
    intro t t' htt'
    obtain ⟨c, c', hc, hc', hcc'⟩ := hsep t t' htt'
    rw [Ideal.isCoprime_iff_exists]
    exact ⟨c, (hPmem t c).mpr hc, c', (hPmem t' c').mpr hc', hcc'⟩
  refine ⟨?_, ?_⟩
  · intro r
    choose s hs using fun t => hρs (r t)
    obtain ⟨b, hb⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun t => (θ t).symm (s t))
    refine ⟨b, funext fun t => ?_⟩
    have h1 : θ t b - s t ∈ 𝔓 := by
      have := (hPmem t _).mp (hb t)
      simpa [map_sub] using this
    have h2 : ρ (θ t b - s t) = 0 := (hρ _).mpr h1
    rw [map_sub, sub_eq_zero] at h2
    simp only [RingHom.pi_apply, RingHom.coe_comp, Function.comp_apply]
    exact h2.trans (hs t)
  · intro b
    constructor
    · intro hb0
      have hbP : ∀ t, b ∈ P t := by
        intro t
        have := congrFun hb0 t
        simp only [RingHom.pi_apply, RingHom.coe_comp, Function.comp_apply, Pi.zero_apply] at this
        exact (hPmem t b).mpr ((hρ _).mp this)
      let Ib : Ideal B := Submodule.comap (LinearMap.mulRight B b) (Ideal.span {p})
      have hIb : ∀ x, x ∈ Ib ↔ x * b ∈ Ideal.span {p} := fun x => Submodule.mem_comap
      by_contra hbp
      have hIbtop : Ib ≠ ⊤ := by
        intro htop
        have h1 : (1 : B) ∈ Ib := htop ▸ Submodule.mem_top
        rw [hIb, one_mul] at h1
        exact hbp h1
      obtain ⟨Q, hQmax, hIQ⟩ := Ideal.exists_le_maximal Ib hIbtop
      have hpQ : p ∈ Q := hIQ ((hIb p).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)))
      obtain ⟨t, ht⟩ := hcover Q hQmax.isPrime hpQ
      have hθb : θ t b ∈ 𝔓 := (hPmem t b).mp (hbP t)
      obtain ⟨c, hc⟩ := hprin _ hθb
      have hit : (θ t).symm i₁ ∈ Ib := by
        rw [hIb]
        have : (θ t).symm i₁ * b = p * (θ t).symm c := by
          apply (θ t).injective
          rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hθp, mul_comm, hc]
        rw [this]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)
      have hit1 : (θ t).symm i₁ - 1 ∈ Q := by
        have := ht _ hi₁
        rwa [map_sub, map_one] at this
      have h1Q : (1 : B) ∈ Q := by
        have := Q.sub_mem (hIQ hit) hit1
        rwa [sub_sub_cancel] at this
      exact hQmax.ne_top ((Ideal.eq_top_iff_one _).mpr h1Q)
    · intro hb
      rw [Ideal.mem_span_singleton'] at hb
      obtain ⟨c, rfl⟩ := hb
      funext t
      simp only [RingHom.pi_apply, RingHom.coe_comp, Function.comp_apply, Pi.zero_apply, map_mul]
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hθp,
        (hρ p).mpr hp, mul_zero]

theorem formallySmooth_fiber_of_surjective
    {A B k R' : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing k] [Algebra A k]
    (I : Ideal A) [I.IsMaximal] (hk : Function.Surjective (algebraMap A k))
    (hIk : ∀ a, algebraMap A k a = 0 ↔ a ∈ I)
    [CommRing R'] [Algebra k R'] [Algebra.FormallySmooth k R']
    (Φ : B →+* R') (hΦA : ∀ a, Φ (algebraMap A B a) = algebraMap k R' (algebraMap A k a))
    (hΦs : Function.Surjective Φ) (hker : ∀ b, Φ b = 0 → b ∈ I.map (algebraMap A B)) :
    Algebra.FormallySmooth I.ResidueField (I.Fiber B) := by
  classical
  letI algAR' : Algebra A R' := ((algebraMap k R').comp (algebraMap A k)).toAlgebra
  haveI : IsScalarTower A k R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let Φₐ : B →ₐ[A] R' := { Φ with commutes' := fun a => hΦA a }
  have hΦₐ : ∀ b, Φₐ b = Φ b := fun _ => rfl
  set κ := I.ResidueField with hκ
  have hkerle : RingHom.ker (algebraMap A k) ≤ RingHom.ker (algebraMap A κ) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    exact Ideal.algebraMap_residueField_eq_zero.mpr ((hIk a).mp ha)
  letI algkκ : Algebra k κ :=
    ((algebraMap A k).liftOfSurjective hk ⟨algebraMap A κ, hkerle⟩).toAlgebra
  have hkκ : ∀ a, algebraMap k κ (algebraMap A k a) = algebraMap A κ a := fun a =>
    (algebraMap A k).liftOfSurjective_comp_apply hk ⟨algebraMap A κ, hkerle⟩ a
  haveI : IsScalarTower A k κ := IsScalarTower.of_algebraMap_eq (fun a => (hkκ a).symm)

  let ψ : k ⊗[A] B →ₐ[k] R' :=
    Algebra.TensorProduct.lift (Algebra.ofId k R') Φₐ (fun _ _ => Commute.all _ _)
  have hψ : ∀ (c : k) (b : B), ψ (c ⊗ₜ b) = algebraMap k R' c * Φ b := fun c b =>
    Algebra.TensorProduct.lift_tmul _ _ _ c b

  have hkerΦ : ∀ b ∈ RingHom.ker Φₐ,
      (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B) b = 0 := by
    intro b hb
    have hb' : b ∈ I • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]; exact hker b hb
    refine Submodule.smul_induction_on hb' ?_ ?_
    · intro a ha x _
      rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_one, (hIk a).mpr ha, TensorProduct.zero_tmul]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  let χ₀ : (B ⧸ RingHom.ker Φₐ) →ₐ[A] k ⊗[A] B :=
    Ideal.Quotient.liftₐ (RingHom.ker Φₐ) Algebra.TensorProduct.includeRight hkerΦ
  let eΦ : (B ⧸ RingHom.ker Φₐ) ≃ₐ[A] R' := Ideal.quotientKerAlgEquivOfSurjective hΦs
  let χ : R' →ₐ[A] k ⊗[A] B := χ₀.comp (eΦ.symm : R' →ₐ[A] B ⧸ RingHom.ker Φₐ)
  have hχΦ : ∀ z : B, χ (Φ z) = (1 : k) ⊗ₜ z := by
    intro z
    change χ₀ (eΦ.symm (Φₐ z)) = _
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  have hleft : ∀ x, χ (ψ x) = x := by
    intro x
    have : (χ.comp (ψ.restrictScalars A)) = AlgHom.id A _ := by
      apply Algebra.TensorProduct.ext'
      intro c b
      obtain ⟨a, rfl⟩ := hk c
      rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgHom.id_apply, hψ]
      have h1 : algebraMap k R' (algebraMap A k a) * Φ b = Φ (a • b) := by
        rw [Algebra.smul_def, map_mul, hΦA]
      rw [h1, hχΦ, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    exact congrArg (fun f => f x) (congrArg DFunLike.coe this)
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y hxy => ?_, fun r => ?_⟩
    · have := congrArg χ hxy
      rwa [hleft, hleft] at this
    · obtain ⟨b, rfl⟩ := hΦs r
      exact ⟨1 ⊗ₜ b, by rw [hψ, map_one, one_mul]⟩
  let e₂ : k ⊗[A] B ≃ₐ[k] R' := AlgEquiv.ofBijective ψ hbij
  haveI : Algebra.FormallySmooth k (k ⊗[A] B) := .of_equiv e₂.symm
  haveI : Algebra.FormallySmooth κ (κ ⊗[k] (k ⊗[A] B)) := inferInstance
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange A k κ κ B)

end SpecialFibre

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace SpecialFibreAssembly

theorem gamma_le_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    CongruenceSubgroup.Gamma N ≤ CohCarrier.GammaH N H := by
  intro γ hγ
  rw [CohCarrier.mem_GammaH_iff]
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; exact hγ.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨γ, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hγ.2.2.2
  rw [this]; exact one_mem H

scoped instance finiteIndex_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    (CohCarrier.GammaH N H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma_le_gammaH N H)

theorem charP_residueField {A : Type*} [CommRing A] [IsLocalRing A] (q : ℕ) (hq : q.Prime)
    (h : (q : A) ∈ maximalIdeal A) : CharP (ResidueField A) q := by
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  rw [← map_natCast (residue A), residue_eq_zero_iff]
  exact h

end SpecialFibreAssembly
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness.SpecialFibreAssembly"

open SpecialFibreAssembly in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A) :

        Algebra.FormallySmooth (IsLocalRing.maximalIdeal A).ResidueField ((IsLocalRing.maximalIdeal A).Fiber ↥B) := by
  classical
  have hqp : q.Prime := Fact.out

  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K, RingHom.coe_comp]
    exact (algebraMap L ↥K).injective.comp hinjAL
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field A
    rw [hϖ, h0, Ideal.span_singleton_eq_bot]
  have hϖt0 : ϖt ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hpow⟩ := hϖt
    have hexp : q ^ 2 - 1 ≠ 0 := by
      have : 5 ≤ q := hq
      have h25 : 25 ≤ q ^ 2 := by nlinarith
      omega
    rw [h0, zero_pow hexp] at hpow
    have hqA : (q : A) = 0 := by
      have := congrArg (· * (↑hu.unit⁻¹ : A)) hpow
      simpa [mul_assoc, IsUnit.mul_val_inv] using this.symm
    have hqL : (q : L) = 0 := by
      have := congrArg (algebraMap A L) hqA
      simpa using this
    exact hqp.ne_zero (by exact_mod_cast hqL)
  have ht0 : algebraMap A ↥K ϖt ≠ 0 := fun h => hϖt0 (hinjAK (by rw [h, map_zero]))
  have hϖtm : ϖt ∈ maximalIdeal A := by
    obtain ⟨u, hu, hpow⟩ := hϖt
    refine (Ideal.IsMaximal.isPrime inferInstance).mem_of_pow_mem (q ^ 2 - 1) ?_
    rw [hpow]
    exact Ideal.mul_mem_right _ _ hAq
  obtain ⟨a', ha'⟩ : ∃ a' : A, a' * ϖ = ϖt := Ideal.mem_span_singleton'.mp (hϖ ▸ hϖtm)
  have hK' : K = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) := by
    rw [hK]; rfl
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))
      (ModularCurve.translation_mem_GammaH _ _) L K hK' j hj
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hftC : Algebra.FiniteType A ↥(chartAlgFin A (↥K) j) :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).1
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K) j) := Algebra.FiniteType.isNoetherianRing A _

  obtain ⟨h1, h2, h3', h4', h5, h6⟩ :=
    Subalgebra.le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
      (chartAlgFin A (↥K) j) J ϖt ht0 B hB

  obtain ⟨hK1i, -, hK1iii⟩ :=
    ModularCurve.FullLevel.AuxLevel.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
      W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  have hK2 :=
    ModularCurve.FullLevel.AuxLevel.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
      W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁.1
  have hK2c := hK2
  obtain ⟨hcen, hdense, hΨA, hres, hresW, hσm, hSmax1, hSmax2, hflat⟩ := hK2c
  have hK3 :=
    ModularCurve.FullLevel.AuxLevel.map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
      W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ hK1i hcen hdense hres ⟨hSmax1, hSmax2⟩

  haveI hcharκ : CharP (ResidueField A) q := SpecialFibreAssembly.charP_residueField q hqp hAq
  letI : Algebra (ZMod q) (ResidueField A) := ZMod.algebra _ q
  letI inst : Algebra (GaloisField q 2) (ResidueField A) :=
    (IsAlgClosed.lift (R := ZMod q) (S := GaloisField q 2) (M := ResidueField A)).toRingHom.toAlgebra

  obtain ⟨Φ, hιR, hx₀, hx₁, hΦR, tW, cR, ρR, ρ, hΦC, hΦJ, htW1, htW2, hcR, hρRF, hρRx₀, hρRx₁, hρΦ, hρsurj, hρker, hρA⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
      W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ J B hB h1 hK2 hK3 inst

  obtain ⟨-, -, hJle, hJyy, ⟨i₁, hi₁y, hLOC⟩, T, N, hN1, hyT, hTmax, hprod, htransp⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
      W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB

  have hq1 : q ≠ 1 := hqp.one_lt.ne'
  haveI hdomCR : IsDomain (DrinfeldCurve.CoordRing q (ResidueField A)) :=
    DrinfeldCurve.isDomain_coordRing_of_ne_one q hq1 _
  haveI hdedCR : IsDedekindDomain (DrinfeldCurve.CoordRing q (ResidueField A)) :=
    DrinfeldCurve.isDedekindDomain_coordRing q (ResidueField A)
  haveI : IsIntegrallyClosed (DrinfeldCurve.CoordRing q (ResidueField A)) := inferInstance
  haveI : Ring.KrullDimLE 1 (DrinfeldCurve.CoordRing q (ResidueField A)) := inferInstance
  haveI : Algebra.FiniteType (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) :=
    Algebra.FiniteType.of_surjective (DrinfeldCurve.mk q (ResidueField A)) (DrinfeldCurve.mk_surjective q (ResidueField A))
  have hSm : Algebra.Smooth (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) :=
    Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField (ResidueField A)
      (DrinfeldCurve.CoordRing q (ResidueField A))
  haveI : Algebra.FormallySmooth (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) := hSm.formallySmooth

  set ιh : ↥(chartAlgFin A (↥K) j) →+* ↥B := (Subalgebra.inclusion h1).toRingHom with hιhdef
  have hιh : ∀ c : ↥(chartAlgFin A (↥K) j), ιh c = ⟨(c : ↥K), h1 c.2⟩ := fun c => rfl
  set 𝔓 : Ideal ↥B := Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), h1 c.2⟩ : ↥B)) ''
    (y : Set ↥(chartAlgFin A (↥K) j))) with h𝔓def
  have hker : RingHom.ker ρ = 𝔓 := by
    ext b
    rw [RingHom.mem_ker]
    exact hρker b
  haveI h𝔓prime : 𝔓.IsPrime := hker ▸ RingHom.ker_isPrime ρ
  have hy𝔓 : ∀ c : ↥(chartAlgFin A (↥K) j), c ∈ y → ιh c ∈ 𝔓 :=
    fun c hc => Ideal.subset_span ⟨c, hc, rfl⟩
  have h𝔓C : Ideal.comap ιh 𝔓 = y := by
    refine (hy.eq_of_le ?_ ?_).symm
    · intro htop
      apply h𝔓prime.ne_top
      rw [Ideal.eq_top_iff_one] at htop ⊢
      have := Ideal.mem_comap.mp htop
      rwa [map_one] at this
    · intro c hc
      exact Ideal.mem_comap.mpr (hy𝔓 c hc)
  set p : ↥B := algebraMap A ↥B ϖ with hpdef
  have hpι : p = ιh (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ) := by
    apply Subtype.ext
    rw [hιh]
    simp only [hpdef, Subalgebra.coe_algebraMap]
  have hp : p ∈ 𝔓 := by rw [hpι]; exact hy𝔓 _ hϖy
  have hi₁𝔓 : ιh i₁ - 1 ∈ 𝔓 := by
    have := hy𝔓 _ hi₁y
    rwa [map_sub, map_one] at this

  have hprin : ∀ g : ↥B, g ∈ 𝔓 → ∃ b : ↥B, g * ιh i₁ = p * b := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨b, hb⟩ := hLOC c hc
      refine ⟨b, Subtype.ext ?_⟩
      rw [hιh]
      simp only [Subalgebra.coe_mul, hpdef, Subalgebra.coe_algebraMap]
      exact hb
    | zero => exact ⟨0, by rw [zero_mul, mul_zero]⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨b, hb⟩ := hx
      obtain ⟨b', hb'⟩ := hx'
      exact ⟨b + b', by rw [add_mul, hb, hb', mul_add]⟩
    | smul r x _ hx =>
      obtain ⟨b, hb⟩ := hx
      exact ⟨r * b, by rw [smul_eq_mul, mul_assoc, hb]; ring⟩

  have hϖtp : algebraMap A ↥B ϖt = algebraMap A ↥B a' * p := by rw [hpdef, ← map_mul, ha']
  have hcontract : ∀ Q₀ : Ideal ↥B, Q₀.IsPrime → p ∈ Q₀ → ∃ P₂ ∈ T, Ideal.comap ιh Q₀ = P₂ := by
    intro Q₀ hQ₀ hpQ₀
    have hϖtQ : algebraMap A ↥B ϖt ∈ Q₀ := by rw [hϖtp]; exact Ideal.mul_mem_left _ _ hpQ₀
    have hJQ : J ≤ Ideal.comap ιh Q₀ := by
      intro i hi
      exact Ideal.mem_comap.mpr (h6 Q₀ hϖtQ i hi (h1 i.2))
    have hPprime : (Ideal.comap ιh Q₀).IsPrime := Ideal.comap_isPrime ιh Q₀
    have hle : (∏ P ∈ T, P ^ N) ≤ Ideal.comap ιh Q₀ := le_trans hprod hJQ
    obtain ⟨P₂, hP₂T, hP₂le⟩ := (Ideal.IsPrime.prod_le hPprime).mp hle
    have hP₂le' : P₂ ≤ Ideal.comap ιh Q₀ := Ideal.IsPrime.le_of_pow_le hP₂le
    exact ⟨P₂, hP₂T, ((hTmax P₂ hP₂T).eq_of_le hPprime.ne_top hP₂le').symm⟩

  have htr : ∀ t : ↥T, ∃ (τ : ↥K ≃ₐ[L] ↥K)
      (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
      (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ.symm a ∈ chartAlgFin A (↥K) j) ∧
      (∀ f : ↥K, f ∈ B → τ f ∈ B) ∧ (∀ f : ↥K, f ∈ B → τ.symm f ∈ B) ∧
      (t : Ideal ↥(chartAlgFin A (↥K) j)) =
        Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) y := by
    intro t
    obtain ⟨γ, -, -, τ, -, hpres, hsC, hτB, hsB, hP⟩ := htransp t.1 t.2
    exact ⟨τ, hpres, hsC, hτB, hsB, hP⟩
  choose τ hpres hsymmC hτB hsymmB hPeq using htr
  let θ : ↥T → (↥B ≃+* ↥B) := fun t =>
    { toFun := fun b => ⟨τ t (b : ↥K), hτB t _ b.2⟩
      invFun := fun b => ⟨(τ t).symm (b : ↥K), hsymmB t _ b.2⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hθ : ∀ (t : ↥T) (b : ↥B), ((θ t b : ↥B) : ↥K) = τ t (b : ↥K) := fun t b => rfl
  have hθsymm : ∀ (t : ↥T) (b : ↥B), (((θ t).symm b : ↥B) : ↥K) = (τ t).symm (b : ↥K) := fun t b => rfl
  have hθC : ∀ (t : ↥T) (c : ↥(chartAlgFin A (↥K) j)),
      θ t (ιh c) = ιh (((τ t : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hpres t)) c) := by
    intro t c
    apply Subtype.ext
    rw [hθ, hιh, hιh]
    rfl

  have hθA : ∀ (t : ↥T) (a : A), θ t (algebraMap A ↥B a) = algebraMap A ↥B a := by
    intro t a
    apply Subtype.ext
    rw [hθ, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  have hθp : ∀ t : ↥T, θ t p = p := fun t => hθA t ϖ

  have hcover : ∀ Q : Ideal ↥B, Q.IsPrime → p ∈ Q → ∃ t : ↥T, ∀ zz ∈ 𝔓, (θ t).symm zz ∈ Q := by
    intro Q hQ hpQ
    obtain ⟨P₁, hP₁T, hP₁⟩ := hcontract Q hQ hpQ
    refine ⟨⟨P₁, hP₁T⟩, ?_⟩
    have key : 𝔓 ≤ Q.comap (θ ⟨P₁, hP₁T⟩).symm.toRingHom := by
      rw [h𝔓def, Ideal.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      let c' : ↥(chartAlgFin A (↥K) j) := ⟨(τ ⟨P₁, hP₁T⟩).symm (c : ↥K), hsymmC ⟨P₁, hP₁T⟩ _ c.2⟩
      have hc'P : c' ∈ P₁ := by
        have hP := hPeq ⟨P₁, hP₁T⟩
        simp only at hP
        rw [hP, Ideal.mem_comap]
        have : ((τ ⟨P₁, hP₁T⟩ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j)
            (hpres ⟨P₁, hP₁T⟩)) c' = c := by
          apply Subtype.ext
          rw [RingHom.coe_restrict_apply]
          change τ ⟨P₁, hP₁T⟩ ((τ ⟨P₁, hP₁T⟩).symm (c : ↥K)) = (c : ↥K)
          exact (τ ⟨P₁, hP₁T⟩).apply_symm_apply _
        rw [this]; exact hc
      rw [← hP₁, Ideal.mem_comap] at hc'P
      have heq : (θ ⟨P₁, hP₁T⟩).symm.toRingHom ⟨(c : ↥K), h1 c.2⟩ = ιh c' := by
        apply Subtype.ext
        rw [hιh]
        rfl
      rw [heq]; exact hc'P
    intro zz hzz
    exact Ideal.mem_comap.mp (key hzz)

  have hsep : ∀ t t' : ↥T, t ≠ t' → ∃ c c' : ↥B, θ t c ∈ 𝔓 ∧ θ t' c' ∈ 𝔓 ∧ c + c' = 1 := by
    intro t t' htt'
    have hne : (t : Ideal ↥(chartAlgFin A (↥K) j)) ≠ (t' : Ideal ↥(chartAlgFin A (↥K) j)) :=
      fun h => htt' (Subtype.ext h)
    have hsup : (t : Ideal ↥(chartAlgFin A (↥K) j)) ⊔ (t' : Ideal ↥(chartAlgFin A (↥K) j)) = ⊤ :=
      (hTmax t.1 t.2).coprime_of_ne (hTmax t'.1 t'.2) hne
    have h1mem : (1 : ↥(chartAlgFin A (↥K) j)) ∈ (t : Ideal ↥(chartAlgFin A (↥K) j)) ⊔ (t' : Ideal _) := by
      rw [hsup]; exact Submodule.mem_top
    obtain ⟨c, hc, c', hc', hcc'⟩ := Submodule.mem_sup.mp h1mem
    refine ⟨ιh c, ιh c', ?_, ?_, by rw [← map_add, hcc', map_one]⟩
    · rw [hθC]
      apply hy𝔓
      have hP := hPeq t
      have hc2 : c ∈ Ideal.comap ((τ t : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j)
        (hpres t)) y := hP ▸ hc
      exact Ideal.mem_comap.mp hc2
    · rw [hθC]
      apply hy𝔓
      have hP := hPeq t'
      have hc2 : c' ∈ Ideal.comap ((τ t' : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j)
        (hpres t')) y := hP ▸ hc'
      exact Ideal.mem_comap.mp hc2

  obtain ⟨hΦs, hΦker⟩ :=
    SpecialFibre.surjective_and_ker_eq_span_pi p 𝔓 hp ρ hρsurj hρker (ιh i₁) hi₁𝔓 hprin θ hθp hcover hsep
  set ΦT : ↥B →+* (↥T → DrinfeldCurve.CoordRing q (ResidueField A)) :=
    RingHom.pi fun t => ρ.comp (θ t).toRingHom with hΦTdef
  have hk : Function.Surjective (algebraMap A (ResidueField A)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective
  have hIk : ∀ a : A, algebraMap A (ResidueField A) a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_eq_zero_iff a
  have hΦA : ∀ a : A, ΦT (algebraMap A ↥B a) =
      algebraMap (ResidueField A) (↥T → DrinfeldCurve.CoordRing q (ResidueField A)) (algebraMap A (ResidueField A) a) := by
    intro a
    funext t
    rw [Pi.algebraMap_apply]
    simp only [hΦTdef, RingHom.pi_apply, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [hθA, hρA, IsLocalRing.ResidueField.algebraMap_eq]
  have hmapspan : (maximalIdeal A).map (algebraMap A ↥B) = Ideal.span {p} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  have hker' : ∀ b : ↥B, ΦT b = 0 → b ∈ (maximalIdeal A).map (algebraMap A ↥B) := by
    intro b hb
    rw [hmapspan]
    exact (hΦker b).mp hb
  exact SpecialFibre.formallySmooth_fiber_of_surjective (maximalIdeal A) hk hIk ΦT hΦA hΦs hker'

end S_ModularCurve_FullLevel_AuxLevel_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness (solution)
