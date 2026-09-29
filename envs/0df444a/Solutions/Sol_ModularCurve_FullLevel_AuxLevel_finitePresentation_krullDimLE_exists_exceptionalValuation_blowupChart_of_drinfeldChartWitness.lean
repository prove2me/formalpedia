-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/8ebbe5cc-4f43-58dc-9468-ad1ee6083a42

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
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

namespace ExcDVR

open IsLocalRing

theorem charP_residueField {A : Type*} [CommRing A] [IsLocalRing A] (q : ℕ) (hq : q.Prime)
    (h : (q : A) ∈ maximalIdeal A) : CharP (ResidueField A) q := by
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  rw [← map_natCast (residue A), residue_eq_zero_iff]
  exact h

theorem exists_valuationSubring {B K : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field K]
    (val : B →+* K) (hval : Function.Injective val)
    (hfrac : ∀ f : K, ∃ g h : B, val h ≠ 0 ∧ f * val h = val g)
    (𝔓 : Ideal B) [h𝔓 : 𝔓.IsPrime] (p : B) (hp : p ∈ 𝔓) (hp0 : p ≠ 0)
    (i₁ : B) (hi₁ : i₁ ∉ 𝔓) (hprin : ∀ g : B, g ∈ 𝔓 → ∃ b : B, g * i₁ = p * b) :
    ∃ (W : ValuationSubring K) (hBW : ∀ b : B, val b ∈ W),
      maximalIdeal ↥W = Ideal.span {(⟨val p, hBW p⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : B, b ∈ 𝔓 ↔ (⟨val b, hBW b⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : K, f ∈ W ↔ ∃ g h : B, (⟨val h, hBW h⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * val h = val g) := by
  classical
  let Bp := Localization.AtPrime 𝔓
  haveI : IsNoetherianRing Bp := IsLocalization.isNoetherianRing 𝔓.primeCompl Bp inferInstance
  have hval0 : ∀ s : 𝔓.primeCompl, val (s : B) ≠ 0 := by
    intro s h0
    have : (s : B) = 0 := hval (by rw [h0, map_zero])
    have hs : (s : B) ∉ 𝔓 := s.2
    exact hs (by rw [this]; exact 𝔓.zero_mem)
  let φ : Bp →+* K := IsLocalization.lift (M := 𝔓.primeCompl) (g := val)
    (fun s => isUnit_iff_ne_zero.mpr (hval0 s))
  have hφalg : ∀ b : B, φ (algebraMap B Bp b) = val b := fun b => IsLocalization.lift_eq _ b
  have hφmk : ∀ (g : B) (s : 𝔓.primeCompl), φ (IsLocalization.mk' Bp g s) * val (s : B) = val g := by
    intro g s
    have := congrArg φ (IsLocalization.mk'_spec Bp g s)
    rwa [map_mul, hφalg, hφalg] at this
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨g, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔓.primeCompl t
    have h1 := hφmk g s
    rw [ht, zero_mul] at h1
    have hg : g = 0 := hval (by rw [← h1, map_zero])
    rw [hg, IsLocalization.mk'_zero]
  have hinjBp : Function.Injective (algebraMap B Bp) :=
    IsLocalization.injective Bp 𝔓.primeCompl_le_nonZeroDivisors

  set pB : Bp := algebraMap B Bp p with hpBdef
  have hmax : maximalIdeal Bp = Ideal.span {pB} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨b, hb⟩ := hprin g hg
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      have hu : IsUnit (algebraMap B Bp i₁) := (IsLocalization.AtPrime.isUnit_to_map_iff Bp 𝔓 i₁).mpr hi₁
      refine ⟨algebraMap B Bp b * ↑(hu.unit⁻¹), ?_⟩
      have h1 : algebraMap B Bp g * algebraMap B Bp i₁ = pB * algebraMap B Bp b := by
        rw [← map_mul, hb, map_mul]
      calc algebraMap B Bp b * ↑(hu.unit⁻¹) * pB
          = (pB * algebraMap B Bp b) * ↑(hu.unit⁻¹) := by ring
        _ = algebraMap B Bp g * (algebraMap B Bp i₁ * ↑(hu.unit⁻¹)) := by rw [← h1, mul_assoc]
        _ = algebraMap B Bp g := by rw [IsUnit.mul_val_inv, mul_one]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hp
  have hpB0 : pB ≠ 0 := fun h => hp0 (hinjBp (by rw [← hpBdef, h, map_zero]))
  have hne : maximalIdeal Bp ≠ ⊥ := by
    rw [hmax, Ne, Ideal.span_singleton_eq_bot]
    exact hpB0
  have hnotfield : ¬ IsField Bp := fun h => hne (IsLocalRing.isField_iff_maximalIdeal_eq.mp h)
  have hprinc : (maximalIdeal Bp).IsPrincipal := ⟨⟨pB, hmax⟩⟩
  haveI hdvr : IsDiscreteValuationRing Bp :=
    ((IsDiscreteValuationRing.TFAE Bp hnotfield).out 0 4).mpr hprinc

  have hmoi : ∀ x : K, x ∈ φ.range ∨ x⁻¹ ∈ φ.range := by
    intro x
    obtain ⟨g, h, hh0, hx⟩ := hfrac x
    rcases ValuationRing.cond (algebraMap B Bp g) (algebraMap B Bp h) with ⟨c, hc | hc⟩
    ·
      right
      have h1 : val g * φ c = val h := by
        have := congrArg φ hc
        rwa [map_mul, hφalg, hφalg] at this
      have hg0 : val g ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact hh0 h1.symm
      refine ⟨c, ?_⟩
      have hxeq : x = val g * (val h)⁻¹ := by rw [← hx, mul_inv_cancel_right₀ hh0]
      rw [hxeq, mul_inv, inv_inv, ← h1]
      field_simp
    ·
      left
      have h1 : val h * φ c = val g := by
        have := congrArg φ hc
        rwa [map_mul, hφalg, hφalg] at this
      refine ⟨c, ?_⟩
      have : x * val h = φ c * val h := by rw [hx, ← h1, mul_comm]
      exact (mul_left_injective₀ hh0 this).symm
  let W : ValuationSubring K := { φ.range with mem_or_inv_mem' := hmoi }
  have hmemW : ∀ x : K, x ∈ W ↔ ∃ t : Bp, φ t = x := fun x => RingHom.mem_range
  have hBW : ∀ b : B, val b ∈ W := fun b => (hmemW _).mpr ⟨algebraMap B Bp b, hφalg b⟩

  let e0 : Bp →+* ↥W := φ.codRestrict W (fun t => (hmemW _).mpr ⟨t, rfl⟩)
  have he0 : Function.Bijective e0 := by
    refine ⟨fun a b hab => hφinj (congrArg Subtype.val hab), fun w => ?_⟩
    obtain ⟨t, ht⟩ := (hmemW _).mp w.2
    exact ⟨t, Subtype.ext ht⟩
  let e : Bp ≃+* ↥W := RingEquiv.ofBijective e0 he0
  have hecoe : ∀ t : Bp, ((e t : ↥W) : K) = φ t := fun t => rfl
  have healg : ∀ b : B, e (algebraMap B Bp b) = ⟨val b, hBW b⟩ := fun b => Subtype.ext (hφalg b)

  have hunit : ∀ t : Bp, IsUnit (e t) ↔ IsUnit t := by
    intro t
    refine ⟨fun h => ?_, fun h => h.map e⟩
    have := h.map e.symm
    rwa [e.symm_apply_apply] at this
  have hunitB : ∀ b : B, IsUnit (⟨val b, hBW b⟩ : ↥W) ↔ b ∉ 𝔓 := by
    intro b
    rw [← healg, hunit, IsLocalization.AtPrime.isUnit_to_map_iff Bp 𝔓 b, Ideal.mem_primeCompl_iff]
  have hmemmax : ∀ b : B, b ∈ 𝔓 ↔ (⟨val b, hBW b⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro b
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunitB, not_not]

  have hmaxW : maximalIdeal ↥W = Ideal.span {(⟨val p, hBW p⟩ : ↥W)} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨t, rfl⟩ : ∃ t, e t = w := e.surjective w
      have ht : ¬ IsUnit t := fun h => (IsLocalRing.mem_maximalIdeal _).mp hw ((hunit t).mpr h)
      have ht' : t ∈ maximalIdeal Bp := (IsLocalRing.mem_maximalIdeal _).mpr ht
      rw [hmax, Ideal.mem_span_singleton'] at ht'
      obtain ⟨c, rfl⟩ := ht'
      rw [map_mul, healg]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (hmemmax p).mp hp
  have hpW0 : (⟨val p, hBW p⟩ : ↥W) ≠ 0 := by
    intro h
    have : val p = 0 := congrArg Subtype.val h
    exact hp0 (hval (by rw [this, map_zero]))
  have hPIR : IsPrincipalIdealRing ↥W := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have hdvrW : IsDiscreteValuationRing ↥W :=
    { toIsPrincipalIdealRing := hPIR
      toIsLocalRing := inferInstance
      not_a_field' := by
        rw [hmaxW, Ne, Ideal.span_singleton_eq_bot]
        exact hpW0 }
  refine ⟨W, hBW, hmaxW, hdvrW, hmemmax, ?_⟩
  intro f
  constructor
  · intro hf
    obtain ⟨t, rfl⟩ := (hmemW f).mp hf
    obtain ⟨g, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔓.primeCompl t
    refine ⟨g, s, ?_, hφmk g s⟩
    rw [← hmemmax]
    exact Ideal.mem_primeCompl_iff.mp s.2
  · rintro ⟨g, h, hh, hfh⟩
    have hh' : h ∉ 𝔓 := fun hm => hh ((hmemmax h).mp hm)
    have hh0 : val h ≠ 0 := hval0 ⟨h, hh'⟩
    rw [hmemW]
    refine ⟨IsLocalization.mk' Bp g (⟨h, hh'⟩ : 𝔓.primeCompl), ?_⟩
    have h1 := hφmk g ⟨h, hh'⟩
    exact mul_left_injective₀ hh0 (h1.trans hfh.symm)

theorem krullDimLE_one_quotient_of_transport {B : Type*} [CommRing B] (p : B) (𝔓 : Ideal B)
    (hcoht : ∀ Q : Ideal B, Q.IsPrime → 𝔓 ≤ Q → Q = 𝔓 ∨ Q.IsMaximal)
    (htrans : ∀ Q : Ideal B, Q.IsPrime → p ∈ Q → ∃ θ : B ≃+* B,
        𝔓 ≤ Q.comap θ.symm.toRingHom ∧
        ∀ Q₀ : Ideal B, Q₀.IsPrime → p ∈ Q₀ → Q₀ ≤ Q → 𝔓 ≤ Q₀.comap θ.symm.toRingHom) :
    Ring.KrullDimLE 1 (B ⧸ Ideal.span {p}) := by
  rw [Ring.krullDimLE_one_iff]
  intro I hI
  set mk := Ideal.Quotient.mk (Ideal.span {p}) with hmk
  have hmks : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hpQ : ∀ I' : Ideal (B ⧸ Ideal.span {p}), p ∈ Ideal.comap mk I' := by
    intro I'
    rw [Ideal.mem_comap]
    have : mk p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
    rw [this]; exact I'.zero_mem
  set Q := Ideal.comap mk I with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime mk I
  obtain ⟨θ, h𝔓Q, hbelow⟩ := htrans Q hQp (hpQ I)
  set Q' := Ideal.comap θ.symm.toRingHom Q with hQ'
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ Q
  have hback : ∀ Q₁ : Ideal B, Ideal.comap θ.toRingHom (Ideal.comap θ.symm.toRingHom Q₁) = Q₁ := by
    intro Q₁
    rw [Ideal.comap_comap, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.comap_id]
  rcases hcoht Q' hQ'p h𝔓Q with hQ'eq | hQ'max
  ·
    left
    refine ⟨⟨hI, bot_le⟩, ?_⟩
    rintro J ⟨hJ, -⟩ hJI

    set Q₀ := Ideal.comap mk J with hQ₀
    have hQ₀p : Q₀.IsPrime := Ideal.comap_isPrime mk J
    have hQ₀Q : Q₀ ≤ Q := Ideal.comap_mono hJI
    have h1 : 𝔓 ≤ Ideal.comap θ.symm.toRingHom Q₀ := hbelow Q₀ hQ₀p (hpQ J) hQ₀Q
    have h2 : Ideal.comap θ.symm.toRingHom Q₀ ≤ Q' := Ideal.comap_mono hQ₀Q
    have h3 : Ideal.comap θ.symm.toRingHom Q₀ = Q' := le_antisymm h2 (hQ'eq ▸ h1)
    have h4 : Q₀ = Q := by
      have := congrArg (Ideal.comap θ.toRingHom) h3
      rwa [hback, hQ', hback] at this

    intro x hx
    obtain ⟨b, rfl⟩ := hmks x
    have hb : b ∈ Q := Ideal.mem_comap.mpr hx
    rw [← h4] at hb
    exact Ideal.mem_comap.mp hb
  ·
    right
    haveI := hQ'max
    have hQmax : Q.IsMaximal := by
      have := Ideal.comap_isMaximal_of_surjective θ.toRingHom θ.surjective (K := Q')
      rwa [hQ', hback] at this
    have hIeq : I = Ideal.map mk Q := (Ideal.map_comap_of_surjective mk hmks I).symm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mk hmks hQmax with htop | hmax
    · exact absurd (hIeq.trans htop) hI.ne_top
    · rwa [← hIeq] at hmax

end ExcDVR

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace ExcDVRAssembly

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

end ExcDVRAssembly
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness.ExcDVRAssembly"

open ExcDVRAssembly in

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

        Algebra.FinitePresentation A ↥B ∧
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}) ∧

        ∃ (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W),
          (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
          maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
          IsDiscreteValuationRing ↥W ∧
          (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
            ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)) := by
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
  haveI hIFR : IsFractionRing ↥(chartAlgFin A (↥K) j) ↥K :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K) ({j} : Set ↥K)
  have hfracC : ∀ f : ↥K, ∃ g h : ↥(chartAlgFin A (↥K) j), (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K) := by
    intro f
    obtain ⟨x, yy, hyy, hxy⟩ := IsFractionRing.div_surjective (A := ↥(chartAlgFin A (↥K) j)) f
    have hy0 : ((yy : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 := by
      have : (yy : ↥(chartAlgFin A (↥K) j)) ≠ 0 := nonZeroDivisors.ne_zero hyy
      exact fun h => this (Subtype.ext h)
    refine ⟨x, yy, hy0, ?_⟩
    rw [← hxy]
    change (x : ↥K) / (yy : ↥K) * (yy : ↥K) = (x : ↥K)
    rw [div_mul_cancel₀ _ hy0]
  have hftC : Algebra.FiniteType A ↥(chartAlgFin A (↥K) j) :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).1
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K) j) := Algebra.FiniteType.isNoetherianRing A _
  have hJfg : J.FG := IsNoetherian.noetherian J

  obtain ⟨h1, h2, h3', h4', h5, h6⟩ :=
    Subalgebra.le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
      (chartAlgFin A (↥K) j) J ϖt ht0 B hB
  have h3 := h3' hfracC
  have hftB : Algebra.FiniteType A ↥B := h4' hJfg hftC
  haveI hnoethB : IsNoetherianRing ↥B := Algebra.FiniteType.isNoetherianRing A ↥B
  have hFP : Algebra.FinitePresentation A ↥B := (Algebra.FinitePresentation.of_finiteType).mp hftB

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

  haveI hcharκ : CharP (ResidueField A) q := ExcDVR.charP_residueField q hqp hAq
  letI : Algebra (ZMod q) (ResidueField A) := ZMod.algebra _ q
  letI inst : Algebra (GaloisField q 2) (ResidueField A) :=
    (IsAlgClosed.lift (R := ZMod q) (S := GaloisField q 2) (M := ResidueField A)).toRingHom.toAlgebra

  obtain ⟨Φ, hιR, hx₀, hx₁, hΦR, tW, cR, ρR, ρ, hΦC, hΦJ, htW1, htW2, hcR, hρRF, hρRx₀, hρRx₁, hρΦ, hρsurj, hρker, hρA⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
      W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ J B hB h1 hK2 hK3 inst

  obtain ⟨⟨m, hm1, hspanϖt, hym⟩, hRED, hJle, hJyy, ⟨i₁, hi₁y, hLOC⟩, T, N, hN1, hyT, hTmax, hprod, htransp⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
      W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB

  have hq1 : q ≠ 1 := hqp.one_lt.ne'
  haveI hdomCR : IsDomain (DrinfeldCurve.CoordRing q (ResidueField A)) :=
    DrinfeldCurve.isDomain_coordRing_of_ne_one q hq1 _
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
  have hp0 : p ≠ 0 := by
    intro h0
    have : (p : ↥K) = 0 := by rw [h0]; rfl
    rw [hpdef, Subalgebra.coe_algebraMap] at this
    exact hϖ0 (hinjAK (by rw [this, map_zero]))
  have hi₁𝔓 : ιh i₁ ∉ 𝔓 := by
    intro hmem
    have hi₁y' : i₁ ∈ y := by rw [← h𝔓C]; exact Ideal.mem_comap.mpr hmem
    have : (1 : ↥(chartAlgFin A (↥K) j)) ∈ y := by
      have := Ideal.sub_mem _ hi₁y' hi₁y
      rwa [sub_sub_cancel] at this
    exact hy.ne_top ((Ideal.eq_top_iff_one _).mpr this)

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

  obtain ⟨W, hBWv, hmaxW, hdvrW, hmemmax, hfracW⟩ :=
    ExcDVR.exists_valuationSubring (B.val : ↥B →ₐ[A] ↥K).toRingHom (fun a b h => Subtype.ext h) h3 𝔓 p hp hp0
      (ιh i₁) hi₁𝔓 hprin
  have hBW : ∀ f : ↥K, f ∈ B → f ∈ W := fun f hf => hBWv ⟨f, hf⟩
  have hϖW : (⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W) ∈ maximalIdeal ↥W := by
    have := (hmemmax p).mp hp
    exact this

  have hR3a : ∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x := by
    intro x
    constructor
    · intro hxW
      rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact ⟨a, ha⟩
      · by_cases hx0 : x = 0
        · exact ⟨0, by rw [map_zero, hx0]⟩
        by_cases hau : IsUnit a
        · refine ⟨(↑(hau.unit⁻¹) : A), ?_⟩
          have hax : algebraMap A L a * x = 1 := by rw [ha, inv_mul_cancel₀ hx0]
          have : algebraMap A L (↑(hau.unit⁻¹) : A) * algebraMap A L a = 1 := by
            rw [← map_mul, IsUnit.val_inv_mul, map_one]
          calc algebraMap A L ↑hau.unit⁻¹ = algebraMap A L ↑hau.unit⁻¹ * (algebraMap A L a * x) := by rw [hax, mul_one]
            _ = x := by rw [← mul_assoc, this, one_mul]
        · exfalso
          have ham : a ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hau
          rw [hϖ, Ideal.mem_span_singleton'] at ham
          obtain ⟨r, rfl⟩ := ham

          have hrϖW : (⟨algebraMap A ↥K (r * ϖ), hBW _ (B.algebraMap_mem _)⟩ : ↥W) ∈ maximalIdeal ↥W := by
            have : (⟨algebraMap A ↥K (r * ϖ), hBW _ (B.algebraMap_mem _)⟩ : ↥W) =
                ⟨algebraMap A ↥K r, hBW _ (B.algebraMap_mem _)⟩ * ⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ :=
              Subtype.ext (by simp [map_mul])
            rw [this]
            exact Ideal.mul_mem_left _ _ hϖW
          have hprod1 : (⟨algebraMap L ↥K x, hxW⟩ : ↥W) * ⟨algebraMap A ↥K (r * ϖ), hBW _ (B.algebraMap_mem _)⟩ = 1 := by
            apply Subtype.ext
            change algebraMap L ↥K x * algebraMap A ↥K (r * ϖ) = 1
            rw [IsScalarTower.algebraMap_apply A L ↥K, ha, ← map_mul, mul_inv_cancel₀ hx0, map_one]
          have hunit : IsUnit (⟨algebraMap A ↥K (r * ϖ), hBW _ (B.algebraMap_mem _)⟩ : ↥W) :=
            IsUnit.of_mul_eq_one_right _ hprod1
          exact (IsLocalRing.mem_maximalIdeal _).mp hrϖW hunit
    · rintro ⟨a, rfl⟩
      rw [← IsScalarTower.algebraMap_apply A L ↥K]
      have : algebraMap A ↥K a = ((algebraMap A ↥B a : ↥B) : ↥K) := by
        rw [Subalgebra.coe_algebraMap]
      rw [this]
      exact hBW _ (algebraMap A ↥B a).2

  have hR3d : ∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
      ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro b
    have hbW : (b : ↥K) ∈ W := hBW _ (h1 b.2)
    constructor
    · intro hb
      exact ⟨hbW, (hmemmax (ιh b)).mp (hy𝔓 b hb)⟩
    · rintro ⟨hb', hm⟩
      have : ιh b ∈ 𝔓 := (hmemmax (ιh b)).mpr hm
      rw [← h𝔓C]
      exact Ideal.mem_comap.mpr this

  haveI : IsDedekindDomain (DrinfeldCurve.CoordRing q (ResidueField A)) :=
    DrinfeldCurve.isDedekindDomain_coordRing q (ResidueField A)
  have hker𝔓le : ∀ Q : Ideal ↥B, 𝔓 ≤ Q → RingHom.ker ρ ≤ Q := fun Q h => hker ▸ h
  have hcoht : ∀ Q : Ideal ↥B, Q.IsPrime → 𝔓 ≤ Q → Q = 𝔓 ∨ Q.IsMaximal := by
    intro Q hQ h𝔓Q
    have hQ'p : (Ideal.map ρ Q).IsPrime := Ideal.map_isPrime_of_surjective hρsurj (hker𝔓le Q h𝔓Q)
    have hcomap : Ideal.comap ρ (Ideal.map ρ Q) = Q := by
      rw [Ideal.comap_map_of_surjective ρ hρsurj, sup_eq_left]
      exact le_trans (by rw [← RingHom.ker_eq_comap_bot]) (hker𝔓le Q h𝔓Q)
    by_cases hbot : Ideal.map ρ Q = ⊥
    · left
      refine le_antisymm ?_ h𝔓Q
      rw [← hcomap, hbot, ← RingHom.ker_eq_comap_bot, hker]
    · right
      haveI : (Ideal.map ρ Q).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hbot hQ'p
      rw [← hcomap]
      exact Ideal.comap_isMaximal_of_surjective ρ hρsurj

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
  have htrans : ∀ Q : Ideal ↥B, Q.IsPrime → p ∈ Q → ∃ θ : ↥B ≃+* ↥B,
      𝔓 ≤ Q.comap θ.symm.toRingHom ∧
      ∀ Q₀ : Ideal ↥B, Q₀.IsPrime → p ∈ Q₀ → Q₀ ≤ Q → 𝔓 ≤ Q₀.comap θ.symm.toRingHom := by
    intro Q hQ hpQ
    obtain ⟨P₁, hP₁T, hP₁⟩ := hcontract Q hQ hpQ
    obtain ⟨γ, hγq, hγ0, τ, hτ, hpres, hsymmC, hτB, hsymmB, hP₁eq⟩ := htransp P₁ hP₁T
    let θ : ↥B ≃+* ↥B :=
      { toFun := fun b => ⟨τ (b : ↥K), hτB _ b.2⟩
        invFun := fun b => ⟨τ.symm (b : ↥K), hsymmB _ b.2⟩
        left_inv := fun b => Subtype.ext (by simp)
        right_inv := fun b => Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) }
    have hθsymm : ∀ b : ↥B, ((θ.symm b : ↥B) : ↥K) = τ.symm (b : ↥K) := fun b => rfl

    have key : ∀ Q₀ : Ideal ↥B, Q₀.IsPrime → Ideal.comap ιh Q₀ = P₁ → 𝔓 ≤ Q₀.comap θ.symm.toRingHom := by
      intro Q₀ hQ₀ hQ₀P
      rw [h𝔓def, Ideal.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]

      let c' : ↥(chartAlgFin A (↥K) j) := ⟨τ.symm (c : ↥K), hsymmC _ c.2⟩
      have hc'P : c' ∈ P₁ := by
        rw [hP₁eq, Ideal.mem_comap]
        have : ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) c' = c := by
          apply Subtype.ext
          rw [RingHom.coe_restrict_apply]
          change τ (τ.symm (c : ↥K)) = (c : ↥K)
          exact τ.apply_symm_apply _
        rw [this]; exact hc
      rw [← hQ₀P, Ideal.mem_comap] at hc'P
      have heq : θ.symm.toRingHom ⟨(c : ↥K), h1 c.2⟩ = ιh c' := by
        apply Subtype.ext
        rw [hιh]
        rfl
      rw [heq]; exact hc'P
    refine ⟨θ, key Q hQ hP₁, ?_⟩
    intro Q₀ hQ₀ hpQ₀ hQ₀Q
    obtain ⟨P₂, hP₂T, hP₂⟩ := hcontract Q₀ hQ₀ hpQ₀
    have hP₂P₁ : P₂ ≤ P₁ := by
      rw [← hP₂, ← hP₁]; exact Ideal.comap_mono hQ₀Q
    have hP₂eq : P₂ = P₁ := (hTmax P₂ hP₂T).eq_of_le (hTmax P₁ hP₁T).ne_top hP₂P₁
    exact key Q₀ hQ₀ (hP₂.trans hP₂eq)
  have hDIM : Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}) :=
    ExcDVR.krullDimLE_one_quotient_of_transport p 𝔓 hcoht htrans

  refine ⟨hFP, hDIM, W, hBW, hR3a, ?_, hdvrW, hR3d, ?_⟩
  · exact hmaxW
  · intro f
    exact hfracW f

end S_ModularCurve_FullLevel_AuxLevel_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness (solution)
