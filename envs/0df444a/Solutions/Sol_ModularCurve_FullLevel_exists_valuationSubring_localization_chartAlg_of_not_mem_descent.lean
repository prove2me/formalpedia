-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_valuationSubring_localization_chartAlg_of_not_mem_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5eb4ac78-38c7-54b2-9674-2455b0c1e5de

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_aeval_eq_zero_imp_and_finiteDimensional_closure_descent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent
p2m_attr_erase "instance" "DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.RegularProlongation.coe_integersEquiv ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E150D

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem exists_valuationSubring_eq_localization
    {A₀ F : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Field F] [CharZero F] [Algebra A₀ F]
    (ϖ : A₀) (hϖ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ})
    (hinj : Function.Injective (algebraMap A₀ F))
    (s : F) (hT : ∀ p : Polynomial A₀, Polynomial.aeval s p = 0 → p = 0)
    (hFin : FiniteDimensional ↥(Subfield.closure (Set.range (algebraMap A₀ F) ∪ {s})) F)
    (C : Subalgebra A₀ F) (hC : ∀ x : F, x ∈ C ↔ IsIntegral ↥(Algebra.adjoin A₀ ({s} : Set F)) x)
    (𝔭 : Ideal ↥C) [h𝔭p : 𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (hϖ𝔭 : algebraMap A₀ ↥C ϖ ∉ 𝔭) :
    ∃ V₁ : ValuationSubring F, ∀ f : F, f ∈ V₁ ↔ ∃ b c : ↥C, c ∉ 𝔭 ∧ f * (c : F) = (b : F) := by
  classical
  let K₀ := FractionRing A₀
  let φ₀ : K₀ →+* F := IsFractionRing.lift (K := K₀) (g := algebraMap A₀ F) hinj
  letI algK₀ : Algebra K₀ F := φ₀.toAlgebra
  haveI : IsScalarTower A₀ K₀ F := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A₀ F a = φ₀ (algebraMap A₀ K₀ a)
    exact (IsFractionRing.lift_algebraMap (K := K₀) hinj a).symm)

  have hTA : Transcendental A₀ s := fun ⟨p, hp0, hp⟩ => hp0 (hT p hp)
  have hTK : Transcendental K₀ s := fun h => hTA ((IsFractionRing.isAlgebraic_iff A₀ K₀ F).mpr h)
  let θ : K₀[X] →ₐ[K₀] F := Polynomial.aeval s
  have hθinj : Function.Injective θ := transcendental_iff_injective.mp hTK
  letI algKX : Algebra K₀[X] F := θ.toRingHom.toAlgebra
  let K := FractionRing K₀[X]
  let ψ : K →+* F := IsFractionRing.lift (K := K) (g := (θ : K₀[X] →+* F)) hθinj
  letI algK : Algebra K F := ψ.toAlgebra
  haveI : IsScalarTower K₀[X] K F := IsScalarTower.of_algebraMap_eq (fun p => by
    show θ p = ψ (algebraMap K₀[X] K p)
    exact (IsFractionRing.lift_algebraMap (K := K) hθinj p).symm)

  let L₀ : Subfield F := Subfield.closure (Set.range (algebraMap A₀ F) ∪ {s})
  have hAL : ∀ a : A₀, algebraMap A₀ F a ∈ L₀ := fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hsL : s ∈ L₀ := Subfield.subset_closure (Or.inr rfl)
  have hφ₀L : ∀ k : K₀, φ₀ k ∈ L₀ := by
    intro k
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A₀) k
    rw [map_div₀]
    refine div_mem ?_ ?_
    · rw [IsFractionRing.lift_algebraMap]; exact hAL a
    · rw [IsFractionRing.lift_algebraMap]; exact hAL b
  have hθL : ∀ p : K₀[X], θ p ∈ L₀ := by
    intro p
    change Polynomial.aeval s p ∈ L₀
    rw [Polynomial.aeval_eq_sum_range]
    refine Subfield.sum_mem _ (fun i _ => ?_)
    rw [Algebra.smul_def]
    exact mul_mem (hφ₀L _) (pow_mem hsL i)
  have hψL : ∀ k : K, ψ k ∈ L₀ := by
    intro k
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := K₀[X]) k
    rw [map_div₀]
    refine div_mem ?_ ?_
    · rw [IsFractionRing.lift_algebraMap]; exact hθL a
    · rw [IsFractionRing.lift_algebraMap]; exact hθL b
  have hLψ : L₀ ≤ ψ.fieldRange := by
    rw [Subfield.closure_le]
    rintro x (⟨a, rfl⟩ | hx)
    · refine ⟨algebraMap K₀[X] K (Polynomial.C (algebraMap A₀ K₀ a)), ?_⟩
      rw [IsFractionRing.lift_algebraMap]
      change Polynomial.aeval s (Polynomial.C (algebraMap A₀ K₀ a)) = algebraMap A₀ F a
      rw [Polynomial.aeval_C, IsScalarTower.algebraMap_apply A₀ K₀ F]
    · rw [Set.mem_singleton_iff.mp hx]
      refine ⟨algebraMap K₀[X] K Polynomial.X, ?_⟩
      rw [IsFractionRing.lift_algebraMap]
      change Polynomial.aeval s Polynomial.X = s
      exact Polynomial.aeval_X s
  let e₁' : K →+* ↥L₀ := ψ.codRestrict L₀ hψL
  have he₁' : Function.Bijective e₁' := by
    refine ⟨fun a b h => ψ.injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨k, hk⟩ := hLψ y.2
    exact ⟨k, Subtype.ext hk⟩
  let e₁ : ↥L₀ ≃+* K := (RingEquiv.ofBijective e₁' he₁').symm
  haveI : Module.Finite ↥L₀ F := hFin
  haveI : FiniteDimensional K F := by
    refine Module.Finite.of_equiv_equiv e₁ (RingEquiv.refl F) ?_
    ext y
    change ψ (e₁ y) = (y : F)
    have : e₁' (e₁ y) = y := (RingEquiv.ofBijective e₁' he₁').apply_symm_apply y
    exact congrArg Subtype.val this
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap K F).injective).mpr inferInstance
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let D := integralClosure K₀[X] F
  haveI : IsDedekindDomain ↥D := IsIntegralClosure.isDedekindDomain K₀[X] K F ↥D
  haveI : IsFractionRing ↥D F := IsIntegralClosure.isFractionRing_of_finite_extension K₀[X] K F ↥D

  let S := Algebra.adjoin A₀ ({s} : Set F)
  let sS : ↥S := ⟨s, Algebra.self_mem_adjoin_singleton A₀ s⟩
  letI algAS : Algebra A₀[X] ↥S := (Polynomial.aeval (R := A₀) sS).toRingHom.toAlgebra
  letI algAF : Algebra A₀[X] F := (Polynomial.aeval (R := A₀) s).toRingHom.toAlgebra
  letI algAK : Algebra A₀[X] K₀[X] := Polynomial.algebra A₀ K₀
  have hSF : ∀ p : A₀[X], ((algebraMap A₀[X] ↥S p : ↥S) : F) = algebraMap A₀[X] F p := fun p =>
    Polynomial.coe_aeval_mk_apply s _ (p := p)
  haveI : IsScalarTower A₀[X] ↥S F := IsScalarTower.of_algebraMap_eq (fun p => (hSF p).symm)
  haveI : IsScalarTower A₀[X] K₀[X] F := IsScalarTower.of_algebraMap_eq (fun p => by
    show Polynomial.aeval s p = θ (algebraMap A₀[X] K₀[X] p)
    change Polynomial.aeval s p = Polynomial.aeval s (Polynomial.map (algebraMap A₀ K₀) p)
    rw [Polynomial.aeval_map_algebraMap])
  haveI : IsLocalization ((nonZeroDivisors A₀).map (Polynomial.C : A₀ →+* A₀[X])) K₀[X] :=
    Polynomial.isLocalization (nonZeroDivisors A₀) K₀

  haveI : Algebra.IsIntegral A₀[X] ↥S := by
    refine Algebra.IsIntegral.of_surjective (Algebra.ofId A₀[X] ↥S) ?_
    intro y
    have hy : (y : F) ∈ (Polynomial.aeval (R := A₀) s).range :=
      (SetLike.le_def.mp (le_of_eq (Algebra.adjoin_singleton_eq_range_aeval A₀ s))) y.2
    obtain ⟨p, hp⟩ := hy
    refine ⟨p, Subtype.ext ?_⟩
    change ((algebraMap A₀[X] ↥S p : ↥S) : F) = y
    rw [hSF]; exact hp

  have hCD : ∀ x : F, x ∈ C → x ∈ D := by
    intro x hx
    rw [hC] at hx
    have h1 : IsIntegral A₀[X] x := isIntegral_trans (A := ↥S) x hx
    exact (mem_integralClosure_iff K₀[X] F).mpr h1.tower_top

  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hDC : ∀ x : F, x ∈ D → ∃ n : ℕ, algebraMap A₀ F ϖ ^ n * x ∈ C := by
    intro x hx
    have hx' : IsIntegral K₀[X] x := (mem_integralClosure_iff K₀[X] F).mp hx
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      ((nonZeroDivisors A₀).map (Polynomial.C : A₀ →+* A₀[X])) x hx'
    obtain ⟨d, hd, rfl⟩ := hm

    have h2 : IsIntegral ↥S (algebraMap A₀ F d * x) := by
      have := hint.tower_top (A := ↥S)
      convert this using 1 <;> first | rfl |
        (change algebraMap A₀ F d * x = Polynomial.aeval s (Polynomial.C d) * x; rw [Polynomial.aeval_C])

    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    obtain ⟨n, u, hdu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖirr
    refine ⟨n, ?_⟩
    have hud : ((u⁻¹ : A₀ˣ) : A₀) * d = ϖ ^ n := by rw [hdu, ← mul_assoc, Units.inv_mul, one_mul]
    have : algebraMap A₀ F ϖ ^ n * x = algebraMap A₀ F ((u⁻¹ : A₀ˣ) : A₀) * (algebraMap A₀ F d * x) := by
      rw [← mul_assoc, ← map_mul, hud, map_pow]
    rw [this]
    exact C.mul_mem (C.algebraMap_mem _) ((hC _).mpr h2)

  set ϖF : F := algebraMap A₀ F ϖ with hϖFdef
  have hϖC : ∀ n : ℕ, ((algebraMap A₀ ↥C ϖ ^ n : ↥C) : F) = ϖF ^ n := by
    intro n; rw [SubmonoidClass.coe_pow]; rfl
  have hϖn𝔭 : ∀ n : ℕ, algebraMap A₀ ↥C ϖ ^ n ∉ 𝔭 := fun n h =>
    hϖ𝔭 (Ideal.IsPrime.mem_of_pow_mem h𝔭p n h)
  have hϖFC : ∀ n : ℕ, ϖF ^ n ∈ C := fun n => by rw [← hϖC]; exact (algebraMap A₀ ↥C ϖ ^ n).2
  let P : F → Prop := fun y => ∃ (n : ℕ) (c : ↥C), (c : F) = ϖF ^ n * y ∧ c ∈ 𝔭
  have hP_C : ∀ c : ↥C, P (c : F) ↔ c ∈ 𝔭 := by
    intro c
    constructor
    · rintro ⟨n, c', hc', hmem⟩
      have : c' = algebraMap A₀ ↥C ϖ ^ n * c := Subtype.ext (by rw [hc', MulMemClass.coe_mul, hϖC])
      rw [this] at hmem
      exact (h𝔭p.mem_or_mem hmem).resolve_left (hϖn𝔭 n)
    · intro hc; exact ⟨0, c, by simp, hc⟩
  have hP_mul : ∀ z y : F, z ∈ D → P y → P (z * y) := by
    rintro z y hz ⟨n, c, hc, hmem⟩
    obtain ⟨m, hm⟩ := hDC z hz
    refine ⟨m + n, ⟨_, hm⟩ * c, ?_, Ideal.mul_mem_left _ _ hmem⟩
    rw [MulMemClass.coe_mul, hc, pow_add]; change ϖF ^ m * z * (ϖF ^ n * y) = _; ring
  have hP_add : ∀ y₁ y₂ : F, P y₁ → P y₂ → P (y₁ + y₂) := by
    rintro y₁ y₂ ⟨n, c₁, hc₁, hm₁⟩ ⟨k, c₂, hc₂, hm₂⟩
    refine ⟨n + k, algebraMap A₀ ↥C ϖ ^ k * c₁ + algebraMap A₀ ↥C ϖ ^ n * c₂, ?_,
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm₁) (Ideal.mul_mem_left _ _ hm₂)⟩
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, MulMemClass.coe_mul, hϖC, hϖC, hc₁, hc₂, pow_add]; ring
  have hP_zero : P 0 := ⟨0, 0, by simp, 𝔭.zero_mem⟩
  let 𝔓 : Ideal ↥D :=
    { carrier := {y | P (y : F)}
      zero_mem' := by change P ((0 : ↥D) : F); rw [ZeroMemClass.coe_zero]; exact hP_zero
      add_mem' := fun {a b} ha hb => by
        change P ((a + b : ↥D) : F); rw [AddMemClass.coe_add]; exact hP_add _ _ ha hb
      smul_mem' := fun z {y} hy => by
        change P ((z * y : ↥D) : F); rw [MulMemClass.coe_mul]; exact hP_mul _ _ z.2 hy }
  have mem𝔓 : ∀ y : ↥D, y ∈ 𝔓 ↔ P (y : F) := fun _ => Iff.rfl
  have h𝔓prime : 𝔓.IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : ↥D) ∈ 𝔓 := htop ▸ Submodule.mem_top
      obtain ⟨n, c, hc, hmem⟩ := (mem𝔓 1).mp h1
      apply hϖn𝔭 n
      have : c = algebraMap A₀ ↥C ϖ ^ n := Subtype.ext (by rw [hc, hϖC]; simp)
      rwa [this] at hmem
    · intro y z hyz
      obtain ⟨n, c, hc, hmem⟩ := (mem𝔓 _).mp hyz
      obtain ⟨a, ha⟩ := hDC _ y.2
      obtain ⟨b, hb⟩ := hDC _ z.2
      have hprod : (⟨_, ha⟩ * ⟨_, hb⟩ : ↥C) * algebraMap A₀ ↥C ϖ ^ n = algebraMap A₀ ↥C ϖ ^ (a + b) * c := by
        apply Subtype.ext
        rw [MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, hϖC, hϖC, hc, MulMemClass.coe_mul, pow_add]
        change ϖF ^ a * (y : F) * (ϖF ^ b * (z : F)) * ϖF ^ n = ϖF ^ a * ϖF ^ b * (ϖF ^ n * ((y : F) * (z : F)))
        ring
      have hin : (⟨_, ha⟩ * ⟨_, hb⟩ : ↥C) * algebraMap A₀ ↥C ϖ ^ n ∈ 𝔭 := by
        rw [hprod]; exact Ideal.mul_mem_left _ _ hmem
      rcases h𝔭p.mem_or_mem hin with h' | h'
      · rcases h𝔭p.mem_or_mem h' with hy | hz
        · exact Or.inl ((mem𝔓 y).mpr ⟨a, _, rfl, hy⟩)
        · exact Or.inr ((mem𝔓 z).mpr ⟨b, _, rfl, hz⟩)
      · exact ((hϖn𝔭 n) h').elim
  have h𝔓ne : 𝔓 ≠ ⊥ := by
    obtain ⟨c, hc𝔭, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭0
    intro hbot
    have hmem : (⟨(c : F), hCD _ c.2⟩ : ↥D) ∈ 𝔓 := (mem𝔓 _).mpr ((hP_C c).mpr hc𝔭)
    rw [hbot, Ideal.mem_bot] at hmem
    apply hc0
    apply Subtype.ext
    have h1 : (c : F) = ((0 : ↥D) : F) := congrArg Subtype.val hmem
    rw [h1]; rfl

  haveI := h𝔓prime
  let v : IsDedekindDomain.HeightOneSpectrum ↥D := ⟨𝔓, h𝔓prime, h𝔓ne⟩
  refine ⟨(v.valuation F).valuationSubring, fun f => ?_⟩
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hf
    obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v f hf
    have hnd' : f * ((d : ↥D) : F) = ((n : ↥D) : F) := hnd
    obtain ⟨a, ha⟩ := hDC _ n.2
    obtain ⟨b, hb⟩ := hDC _ (d : ↥D).2

    have hd' : ϖF ^ (a + b) * ((d : ↥D) : F) ∈ C := by
      have : ϖF ^ (a + b) * ((d : ↥D) : F) = ϖF ^ a * (ϖF ^ b * ((d : ↥D) : F)) := by rw [pow_add, mul_assoc]
      rw [this]; exact C.mul_mem (hϖFC a) hb
    have hn' : ϖF ^ (a + b) * ((n : ↥D) : F) ∈ C := by
      have : ϖF ^ (a + b) * ((n : ↥D) : F) = ϖF ^ b * (ϖF ^ a * ((n : ↥D) : F)) := by rw [pow_add]; ring
      rw [this]; exact C.mul_mem (hϖFC b) ha
    refine ⟨⟨_, hn'⟩, ⟨_, hd'⟩, ?_, ?_⟩
    · intro hmem
      exact d.2 ((mem𝔓 _).mpr ⟨a + b, ⟨_, hd'⟩, rfl, hmem⟩)
    · change f * (ϖF ^ (a + b) * ((d : ↥D) : F)) = ϖF ^ (a + b) * ((n : ↥D) : F)
      rw [mul_left_comm, hnd']
  · rintro ⟨b, c, hc, hfc⟩
    have hcD : (c : F) ∈ D := hCD _ c.2
    have hbD : (b : F) ∈ D := hCD _ b.2
    have hc𝔓 : (⟨(c : F), hcD⟩ : ↥D) ∉ 𝔓 := fun h => hc ((hP_C c).mp ((mem𝔓 _).mp h))
    have hc0 : (c : F) ≠ 0 := by
      intro h0; apply hc
      have : c = 0 := Subtype.ext h0
      rw [this]; exact 𝔭.zero_mem
    have hvc : v.valuation F (algebraMap ↥D F ⟨(c : F), hcD⟩) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
      exact hc𝔓
    have hvb : v.valuation F (algebraMap ↥D F ⟨(b : F), hbD⟩) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v _
    have hf : f = (algebraMap ↥D F ⟨(b : F), hbD⟩) * (algebraMap ↥D F ⟨(c : F), hcD⟩)⁻¹ := by
      change f = (b : F) * ((c : F))⁻¹
      rw [← hfc, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    rw [hf, map_mul, map_inv₀, hvc, inv_one, mul_one]
    exact hvb

end E150D

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (S : Set ↥F₀) (hS : S = {(⟨_, hjF₀⟩ : ↥F₀)} ∨ S = {(⟨_, hjF₀⟩ : ↥F₀)⁻¹})
    (𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S)) (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S) ϖ₀ ∉ 𝔭) :
    ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀) := by
  classical
  obtain ⟨hT, hFin⟩ := ModularCurve.FullLevel.aeval_eq_zero_imp_and_finiteDimensional_closure_descent q hq M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
  haveI : CharZero ↥F₀ := (RingHom.charZero_iff (algebraMap ↥F₀ ↥(fieldBar q M')).injective).mpr inferInstance
  have hinj : Function.Injective (algebraMap A₀ ↥F₀) := by
    intro a b h
    apply hι
    apply Subtype.ext
    have := congrArg (fun t : ↥F₀ => (t : ↥(fieldBar q M'))) h
    simp only [hj₀] at this
    exact (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).injective this
  haveI := h𝔭

  obtain ⟨s, rfl, hTs, hFins⟩ : ∃ s : ↥F₀, S = {s} ∧ (∀ p : Polynomial A₀, Polynomial.aeval s p = 0 → p = 0) ∧
      FiniteDimensional ↥(Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {s})) ↥F₀ := by
    rcases hS with rfl | rfl
    · exact ⟨_, rfl, hT, hFin⟩
    · refine ⟨_, rfl, ?_, ?_⟩
      ·
        intro p hp
        have hTA : Transcendental A₀ ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) := fun ⟨p, hp0, hp⟩ => hp0 (hT p hp)
        by_contra hp0
        exact hTA (by simpa using (show IsAlgebraic A₀ (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹) from ⟨p, hp0, hp⟩).inv)
      ·
        have heq : Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹}) =
            Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)}) := by
          apply le_antisymm
          · rw [Subfield.closure_le]
            rintro x (hx | hx)
            · exact Subfield.subset_closure (Or.inl hx)
            · rw [Set.mem_singleton_iff.mp hx]
              exact inv_mem (Subfield.subset_closure (Or.inr rfl))
          · rw [Subfield.closure_le]
            rintro x (hx | hx)
            · exact Subfield.subset_closure (Or.inl hx)
            · rw [Set.mem_singleton_iff.mp hx]
              have h : (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀) ∈ Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹}) :=
                Subfield.subset_closure (Or.inr rfl)
              have h2 := inv_mem h
              rwa [inv_inv] at h2
        rw [heq]; exact hFin
  exact E150D.exists_valuationSubring_eq_localization ϖ₀ hϖ₀ hinj s hTs hFins (TwoChartIntegralModel.chartAlg A₀ ↥F₀ {s})
    (fun x => TwoChartIntegralModel.mem_chartAlg_iff A₀ ↥F₀) 𝔭 h𝔭0 hϖ

end S_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent (solution)
