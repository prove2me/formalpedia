-- Prove2me | solution 1 for GlobalTheory.exists_integral_point_through
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:16.103904+00:00
-- url     : https://prove2.me/submissions/9d8e69e8-3783-4e0e-b033-fa553c7f8e32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DimensionQuotientBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PrimeAvoidanceFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIntegralPointThrough
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DimensionQuotientBound_local_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_dvr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_isLocalHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_PrimeAvoidanceFibre_avoid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_PrimeAvoidanceFibre_finite_of_fibre


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (M : Ideal B) (hM : M.IsMaximal) (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≤ M)
    (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ maximalIdeal V := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  set w := algebraMap O B ϖ with hw

  have hw0 : w ≠ 0 := by
    intro h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have h1 : ϖ • (1 : B) = ϖ • (0 : B) := by rw [Algebra.smul_def, mul_one, ← hw, h0, smul_zero]
    exact one_ne_zero (hreg h1)
  have hϖm : ϖ ∈ maximalIdeal O := by rw [hmO]; exact Ideal.mem_span_singleton_self ϖ
  have hwM : w ∈ M := hsp (Ideal.mem_map_of_mem _ hϖm)
  obtain ⟨q, hq, hqM, heq, hwq, hchain⟩ := DimensionQuotientBound.local_step M w e hwM hw0 he
  obtain ⟨s, hsM, hs⟩ := PrimeAvoidanceFibre.avoid M q w hchain

  let D := B ⧸ q
  have : IsDomain D := Ideal.Quotient.isDomain q
  let sb : D := Ideal.Quotient.mk q s
  have hsb : sb ≠ 0 := fun h => hsM (hqM (Ideal.Quotient.eq_zero_iff_mem.1 h))
  let D' := Localization.Away sb
  have hpow : Submonoid.powers sb ≤ nonZeroDivisors D := powers_le_nonZeroDivisors_of_noZeroDivisors hsb
  have : IsDomain D' := IsLocalization.isDomain_localization hpow
  have : IsNoetherianRing D' := IsLocalization.isNoetherianRing (Submonoid.powers sb) D' inferInstance
  have : Algebra.FiniteType O D :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O q) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType O D' := inferInstance
  have hDinj : Function.Injective (algebraMap D D') := IsLocalization.injective D' hpow

  let f : B →+* D' := (algebraMap D D').comp (Ideal.Quotient.mk q)
  have hfO : ∀ c : O, algebraMap O D' c = f (algebraMap O B c) := fun c => by
    rw [IsScalarTower.algebraMap_apply O D D']; rfl
  have hcomapM : ∀ P : Ideal D', P.IsPrime → algebraMap O D' ϖ ∈ P → Ideal.comap f P = M := by
    intro P hP hwP
    refine hs _ (Ideal.comap_isPrime f P) (fun x hx => ?_) ?_ ?_
    · show algebraMap D D' (Ideal.Quotient.mk q x) ∈ P
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]; exact P.zero_mem
    · rw [Ideal.mem_comap, ← hfO]; exact hwP
    · intro hsP
      have hu : IsUnit (algebraMap D D' sb) := IsLocalization.map_units D' ⟨sb, Submonoid.mem_powers sb⟩
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hsP hu)
  have huniq : ∀ P P' : Ideal D', P.IsPrime → P'.IsPrime → algebraMap O D' ϖ ∈ P →
      algebraMap O D' ϖ ∈ P' → P = P' := by
    intro P P' hP hP' hwP hwP'
    have e1 : Ideal.comap (Ideal.Quotient.mk q) (Ideal.comap (algebraMap D D') P) =
        Ideal.comap (Ideal.Quotient.mk q) (Ideal.comap (algebraMap D D') P') := by
      rw [Ideal.comap_comap, Ideal.comap_comap]
      exact (hcomapM P hP hwP).trans (hcomapM P' hP' hwP').symm
    have e2 := Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e1
    rw [← IsLocalization.map_under (Submonoid.powers sb) D' P,
      ← IsLocalization.map_under (Submonoid.powers sb) D' P']
    exact congrArg _ e2
  have hex : ∃ P : Ideal D', P.IsPrime ∧ algebraMap O D' ϖ ∈ P := by
    let Mb := Ideal.map (Ideal.Quotient.mk q) M
    have hMb : Mb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqM)
    have hcMb : Ideal.comap (Ideal.Quotient.mk q) Mb = M := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hqM]
    have hdisj : Disjoint (Submonoid.powers sb : Set D) Mb := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hx
      have : s ^ n ∈ M := by
        rw [← hcMb, Ideal.mem_comap, map_pow]; exact hx
      exact hsM (hM.isPrime.mem_of_pow_mem n this)
    refine ⟨Ideal.map (algebraMap D D') Mb,
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers sb) D' Mb hMb hdisj, ?_⟩
    rw [hfO]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hwM)
  have hfin : Module.Finite O D' := PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ hex huniq

  have hOinj : Function.Injective (algebraMap O D') := by
    rw [injective_iff_map_eq_zero]
    by_contra hne
    push Not at hne
    obtain ⟨c, hc, hc0⟩ := hne
    have hker : RingHom.ker (algebraMap O D') ≠ ⊥ := fun h =>
      hc0 ((RingHom.injective_iff_ker_eq_bot _).2 h (hc.trans (map_zero _).symm))
    have hkp : (RingHom.ker (algebraMap O D')).IsPrime := RingHom.ker_isPrime _
    have hkm : RingHom.ker (algebraMap O D') = maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (hkp.isMaximal hker)
    have hϖk : ϖ ∈ RingHom.ker (algebraMap O D') := by
      rw [hkm, hmO]; exact Ideal.mem_span_singleton_self ϖ
    rw [RingHom.mem_ker, hfO] at hϖk
    apply hwq
    have : algebraMap D D' (Ideal.Quotient.mk q w) = algebraMap D D' 0 := by rw [map_zero]; exact hϖk
    exact Ideal.Quotient.eq_zero_iff_mem.1 (hDinj this)
  have : FaithfulSMul O D' := (faithfulSMul_iff_algebraMap_injective O D').2 hOinj

  let K := FractionRing O
  let L := FractionRing D'
  have : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 (by
    rw [IsScalarTower.algebraMap_eq O D' L]
    exact (IsFractionRing.injective D' L).comp hOinj)
  let _ : Algebra K L := FractionRing.liftAlgebra O L
  have : IsScalarTower O K L := FractionRing.isScalarTower_liftAlgebra O L
  have : Algebra.IsIntegral O D' := Algebra.IsIntegral.of_finite O D'
  have : FiniteDimensional K L := Module.Finite.of_isLocalization O D' (nonZeroDivisors O)
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  have : Algebra.IsSeparable K L := inferInstance
  have hVfin : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L (integralClosure O L)
  have hdvr : IsDiscreteValuationRing (integralClosure O L) := FiniteAlgebraLocalCompletion.cl_dvr O K L

  let g1 : B →ₐ[O] D := Ideal.Quotient.mkₐ O q
  let g2 : D →ₐ[O] D' := IsScalarTower.toAlgHom O D D'
  let g3 : D' →ₐ[O] L := IsScalarTower.toAlgHom O D' L
  let g4 : D' →ₐ[O] integralClosure O L :=
    g3.codRestrict (integralClosure O L) fun x => (Algebra.IsIntegral.isIntegral x).map g3
  refine ⟨integralClosure O L, inferInstance, inferInstance, hdvr, inferInstance, hVfin,
    g4.comp (g2.comp g1), ?_, ?_⟩
  swap
  ·
    have hloc := FiniteAlgebraLocalCompletion.cl_isLocalHom O L
    let P : Ideal D' := Ideal.comap g4 (maximalIdeal (integralClosure O L))
    have hP : P.IsPrime := Ideal.comap_isPrime _ _
    have hϖP : algebraMap O D' ϖ ∈ P := by
      show g4 (algebraMap O D' ϖ) ∈ maximalIdeal (integralClosure O L)
      rw [g4.commutes]
      exact map_nonunit _ ϖ hϖm
    intro x hx
    rw [← hcomapM P hP hϖP] at hx
    exact hx
  intro h0
  have h1 : g3 (g2 (g1 e)) = 0 := congrArg Subtype.val h0
  have h2 : g2 (g1 e) = 0 := (IsFractionRing.injective D' L) (h1.trans (map_zero _).symm)
  have h3 : g1 e = 0 := hDinj (h2.trans (map_zero _).symm)
  exact heq (Ideal.Quotient.eq_zero_iff_mem.1 h3)
end GlobalTheory
