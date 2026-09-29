-- Prove2me | solution 1 for ModularCurve.CharPReduction.exists_coeffMap_eq_of_mem_modularLocalized_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/40fa8ebe-978e-506a-a903-37a25585a8a6

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPReduction_exists_coeffMap_eq_of_mem_modularLocalized_of_monic
set_option autoImplicit false

open AlgebraicCurve

namespace J3C1

open ModularCurve NumberField

section Constants

variable {L : Type*} [Field L]

private noncomputable def genRing_j3 (N : ℕ) [NeZero N] (T : Set L) : Subring (LaurentSeries L) :=
  Subring.closure ((fun c : L => HahnSeries.single (0 : ℤ) c) '' T ∪ {jqModC L, jqNModC L N})

private theorem genRing_mono_j3 (N : ℕ) [NeZero N] {T T' : Set L} (h : T ⊆ T') :
    genRing_j3 N T ≤ genRing_j3 N T' :=
  Subring.closure_mono (Set.union_subset_union_left _ (Set.image_mono h))

private theorem single_mem_genRing_j3 (N : ℕ) [NeZero N] {T : Set L} {c : L} (hc : c ∈ T) :
    HahnSeries.single (0 : ℤ) c ∈ genRing_j3 N T :=
  Subring.subset_closure (Or.inl ⟨c, hc, rfl⟩)

private theorem jqModC_mem_genRing_j3 (N : ℕ) [NeZero N] (T : Set L) :
    jqModC L ∈ genRing_j3 N T :=
  Subring.subset_closure (Or.inr (Set.mem_insert _ _))

private theorem exists_finset_of_mem_modularRing_j3 (A : Subring L) (N : ℕ) [NeZero N]
    {x : LaurentSeries L} (hx : x ∈ CharPReduction.modularRing N A) :
    ∃ T : Finset L, (↑T : Set L) ⊆ A ∧ x ∈ genRing_j3 N (↑T : Set L) := by
  classical
  have hx' : x ∈ Subring.closure (Set.range (CharPReduction.constSeries A) ∪
      {jqModC L, jqNModC L N}) := hx
  refine Subring.closure_induction (p := fun y _ => ∃ T : Finset L, (↑T : Set L) ⊆ A ∧
      y ∈ genRing_j3 N (↑T : Set L)) ?_ ?_ ?_ ?_ ?_ ?_ hx'
  · rintro y (⟨a, rfl⟩ | hy)
    · refine ⟨{(a : L)}, by simp, ?_⟩
      have ha : CharPReduction.constSeries A a = HahnSeries.single (0 : ℤ) (a : L) :=
        algebraMap_laurentSeries_eq_single L a
      rw [ha]
      exact single_mem_genRing_j3 N (by simp)
    · exact ⟨∅, by simp, Subring.subset_closure (Or.inr hy)⟩
  · exact ⟨∅, by simp, zero_mem _⟩
  · exact ⟨∅, by simp, one_mem _⟩
  · rintro y z - - ⟨T, hT, h⟩ ⟨T', hT', h'⟩
    refine ⟨T ∪ T', by rw [Finset.coe_union]; exact Set.union_subset hT hT', add_mem ?_ ?_⟩
    · exact genRing_mono_j3 N (by rw [Finset.coe_union]; exact Set.subset_union_left) h
    · exact genRing_mono_j3 N (by rw [Finset.coe_union]; exact Set.subset_union_right) h'
  · rintro y - ⟨T, hT, h⟩
    exact ⟨T, hT, neg_mem h⟩
  · rintro y z - - ⟨T, hT, h⟩ ⟨T', hT', h'⟩
    refine ⟨T ∪ T', by rw [Finset.coe_union]; exact Set.union_subset hT hT', mul_mem ?_ ?_⟩
    · exact genRing_mono_j3 N (by rw [Finset.coe_union]; exact Set.subset_union_left) h
    · exact genRing_mono_j3 N (by rw [Finset.coe_union]; exact Set.subset_union_right) h'

private theorem genRing_le_range_j3 {R : Type*} [CommRing R] (φ : R →+* L) (N : ℕ) [NeZero N]
    {T : Set L} (hT : T ⊆ Set.range φ) : genRing_j3 N T ≤ (coeffMap φ).range := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨c, hc, rfl⟩ | hx)
  · obtain ⟨d, rfl⟩ := hT hc
    exact ⟨HahnSeries.single 0 d, coeffMap_single φ 0 d⟩
  · rcases hx with rfl | rfl
    · exact ⟨jqModC R, map_jqModC φ⟩
    · refine ⟨jqNModC R N, ?_⟩
      show coeffMap φ (qExpand R N (jqModC R)) = qExpand L N (jqModC L)
      rw [coeffSemilinearAut.coeffMap_qExpand]
      exact congrArg _ (map_jqModC φ)

private theorem eval₂_mem_genRing_j3 (A : ValuationSubring L) (N : ℕ) [NeZero N]
    (p : Polynomial A) {T : Set L} (hT : ∀ n ∈ p.support, ((p.coeff n : A) : L) ∈ T) :
    Polynomial.eval₂ ((algebraMap L (LaurentSeries L)).comp A.subtype) (jqModC L) p ∈
      genRing_j3 N T := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine Subring.sum_mem _ fun n hn => mul_mem ?_ (pow_mem (jqModC_mem_genRing_j3 N T) n)
  have h : ((algebraMap L (LaurentSeries L)).comp A.subtype) (p.coeff n) =
      HahnSeries.single (0 : ℤ) ((p.coeff n : A) : L) :=
    algebraMap_laurentSeries_eq_single L _
  rw [h]
  exact single_mem_genRing_j3 N (hT n hn)

end Constants

section Integral

variable {L : Type*} [Field L]

private theorem mem_of_isIntegral_int_j3 (B : ValuationSubring L) {z : L} (hz : IsIntegral ℤ z) :
    z ∈ B := by
  obtain ⟨p, hp, hpz⟩ := hz
  rw [← B.valuation_le_one_iff z]
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hpz
  have hsum : B.valuation (∑ i ∈ Finset.range p.natDegree, algebraMap ℤ L (p.coeff i) * z ^ i) <
      B.valuation z ^ p.natDegree := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hlt)))
      fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    have hc : B.valuation (algebraMap ℤ L (p.coeff i)) ≤ 1 := by
      rw [B.valuation_le_one_iff, algebraMap_int_eq, eq_intCast]
      exact intCast_mem B _
    calc B.valuation (algebraMap ℤ L (p.coeff i)) * B.valuation z ^ i
        ≤ 1 * B.valuation z ^ i := mul_le_mul_left hc _
      _ = B.valuation z ^ i := one_mul _
      _ < B.valuation z ^ p.natDegree := pow_lt_pow_right₀ hlt hi
  have heq : z ^ p.natDegree =
      -∑ i ∈ Finset.range p.natDegree, algebraMap ℤ L (p.coeff i) * z ^ i :=
    eq_neg_of_add_eq_zero_right hpz
  have h2 : B.valuation (z ^ p.natDegree) < B.valuation z ^ p.natDegree := by
    rw [heq, Valuation.map_neg]
    exact hsum
  rw [map_pow] at h2
  exact lt_irrefl _ h2

end Integral

section DVR

variable (A : ValuationSubring (AlgebraicClosure ℚ))
  (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K₀]

private noncomputable def tau_j3 : 𝓞 K₀ →+* A :=
  ((algebraMap K₀ (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 K₀) K₀)).codRestrict A fun x =>
    mem_of_isIntegral_int_j3 A ((RingOfIntegers.isIntegral_coe x).map
      (algebraMap K₀ (AlgebraicClosure ℚ)).toIntAlgHom)

omit [NumberField K₀] in
private theorem tau_coe_j3 (x : 𝓞 K₀) :
    ((tau_j3 A K₀ x : A) : AlgebraicClosure ℚ) =
      algebraMap K₀ (AlgebraicClosure ℚ) (algebraMap (𝓞 K₀) K₀ x) :=
  rfl

private noncomputable def P_j3 : Ideal (𝓞 K₀) :=
  (IsLocalRing.maximalIdeal A).comap (tau_j3 A K₀)

private scoped instance P_isPrime_j3 : (P_j3 A K₀).IsPrime :=
  inferInstanceAs ((Ideal.comap (tau_j3 A K₀) (IsLocalRing.maximalIdeal A)).IsPrime)

private noncomputable def D_j3 : Subalgebra (𝓞 K₀) K₀ :=
  Localization.subalgebra.ofField K₀ (P_j3 A K₀).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

private noncomputable scoped instance D_algebra_j3 : Algebra (𝓞 K₀) (D_j3 A K₀) :=
  Subalgebra.algebra (D_j3 A K₀)

private noncomputable scoped instance D_algebraK_j3 : Algebra (D_j3 A K₀) K₀ :=
  Subalgebra.toAlgebra (D_j3 A K₀)

private scoped instance D_isScalarTower_j3 : IsScalarTower (𝓞 K₀) (D_j3 A K₀) K₀ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance D_isLocalization_j3 : IsLocalization.AtPrime (D_j3 A K₀) (P_j3 A K₀) :=
  Localization.subalgebra.isLocalization_ofField K₀ _ _

private noncomputable def phi_j3 : D_j3 A K₀ →+* AlgebraicClosure ℚ :=
  (algebraMap K₀ (AlgebraicClosure ℚ)).comp (algebraMap (D_j3 A K₀) K₀)

private theorem phi_apply_j3 (d : D_j3 A K₀) :
    phi_j3 A K₀ d = algebraMap K₀ (AlgebraicClosure ℚ) (algebraMap (D_j3 A K₀) K₀ d) :=
  rfl

private theorem phi_injective_j3 : Function.Injective (phi_j3 A K₀) := fun _ _ h =>
  Subtype.ext ((algebraMap K₀ (AlgebraicClosure ℚ)).injective h)

omit [NumberField K₀] in

private theorem isUnit_tau_j3 {s : 𝓞 K₀} (hs : s ∈ (P_j3 A K₀).primeCompl) :
    IsUnit (tau_j3 A K₀ s) := by
  by_contra hns
  exact hs ((IsLocalRing.mem_maximalIdeal _).mpr hns)

private theorem phi_mem_j3 (d : D_j3 A K₀) : phi_j3 A K₀ d ∈ A := by
  obtain ⟨a, s, hs, hd⟩ : ∃ (a s : 𝓞 K₀) (_ : s ∈ (P_j3 A K₀).primeCompl),
      algebraMap (D_j3 A K₀) K₀ d = algebraMap (𝓞 K₀) K₀ a * (algebraMap (𝓞 K₀) K₀ s)⁻¹ := d.2
  obtain ⟨u, hu⟩ := isUnit_tau_j3 A K₀ hs
  have h1 : algebraMap K₀ (AlgebraicClosure ℚ) (algebraMap (𝓞 K₀) K₀ s) *
      (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
    rw [← tau_coe_j3 A K₀ s, ← hu, ← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [phi_apply_j3, hd, map_mul, map_inv₀, inv_eq_of_mul_eq_one_right h1]
  exact mul_mem (tau_j3 A K₀ a).2 ((u⁻¹ : Aˣ) : A).2

private noncomputable def psi_j3 : D_j3 A K₀ →+* A :=
  (phi_j3 A K₀).codRestrict A (phi_mem_j3 A K₀)

private theorem subtype_comp_psi_j3 : A.subtype.comp (psi_j3 A K₀) = phi_j3 A K₀ :=
  RingHom.ext fun _ => rfl

omit [NumberField K₀] in

private theorem P_ne_bot_j3 {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) : P_j3 A K₀ ≠ ⊥ := by
  intro h
  have hq : ((q : ℕ) : 𝓞 K₀) ∈ P_j3 A K₀ := by
    show tau_j3 A K₀ q ∈ IsLocalRing.maximalIdeal A
    rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at hu'
    exact not_isUnit_zero hu'
  rw [h, Ideal.mem_bot] at hq
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq

private theorem isDiscreteValuationRing_D_j3 (hP : P_j3 A K₀ ≠ ⊥) :
    IsDiscreteValuationRing (D_j3 A K₀) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₀) hP (D_j3 A K₀)

private theorem exists_phi_eq_j3 [IsDiscreteValuationRing (D_j3 A K₀)] (x : K₀)
    (hx : algebraMap K₀ (AlgebraicClosure ℚ) x ∈ A) :
    ∃ d : D_j3 A K₀, phi_j3 A K₀ d = algebraMap K₀ (AlgebraicClosure ℚ) x := by
  haveI : IsFractionRing (D_j3 A K₀) K₀ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (P_j3 A K₀).primeCompl
      (D_j3 A K₀) K₀
  rcases (ValuationRing.iff_isInteger_or_isInteger (D_j3 A K₀) K₀).mp inferInstance x with
    ⟨d, hd⟩ | ⟨d, hd⟩
  · exact ⟨d, by rw [phi_apply_j3]; exact congrArg _ hd⟩
  · by_cases hx0 : x = 0
    · exact ⟨0, by rw [hx0, map_zero, map_zero]⟩
    by_cases hdu : IsUnit d
    · obtain ⟨u, rfl⟩ := hdu
      refine ⟨((u⁻¹ : (D_j3 A K₀)ˣ) : D_j3 A K₀), ?_⟩
      rw [phi_apply_j3]
      refine congrArg _ ?_
      have hd' : algebraMap (D_j3 A K₀) K₀ ((u⁻¹ : (D_j3 A K₀)ˣ) : D_j3 A K₀) = x := by
        rw [map_units_inv, hd, inv_inv]
      exact hd'
    · exfalso
      have hdm : d ∈ IsLocalRing.maximalIdeal (D_j3 A K₀) :=
        (IsLocalRing.mem_maximalIdeal _).mpr hdu
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (P_j3 A K₀) (D_j3 A K₀)] at hdm
      obtain ⟨⟨p, b⟩, hpb⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (P_j3 A K₀).primeCompl (D_j3 A K₀)).mp hdm

      have hpb' : (algebraMap K₀ (AlgebraicClosure ℚ) x)⁻¹ *
          ((tau_j3 A K₀ b : A) : AlgebraicClosure ℚ) = ((tau_j3 A K₀ p : A) : AlgebraicClosure ℚ) := by
        have := congrArg (phi_j3 A K₀) hpb
        rw [map_mul, phi_apply_j3 A K₀ d, hd, map_inv₀] at this
        exact this
      obtain ⟨u, hu⟩ := isUnit_tau_j3 A K₀ b.2

      have hmem : (tau_j3 A K₀ b : A) ∈ IsLocalRing.maximalIdeal A := by
        have hx0' : algebraMap K₀ (AlgebraicClosure ℚ) x ≠ 0 :=
          (map_ne_zero_iff _ (algebraMap K₀ (AlgebraicClosure ℚ)).injective).mpr hx0
        have he : (tau_j3 A K₀ b : A) = ⟨_, hx⟩ * tau_j3 A K₀ p := by
          apply Subtype.ext
          show ((tau_j3 A K₀ b : A) : AlgebraicClosure ℚ) =
            algebraMap K₀ (AlgebraicClosure ℚ) x * ((tau_j3 A K₀ p : A) : AlgebraicClosure ℚ)
          rw [← hpb', ← mul_assoc, mul_inv_cancel₀ hx0', one_mul]
        rw [he]
        exact Ideal.mul_mem_left _ _ p.2
      exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) ⟨u, hu⟩

end DVR

end J3C1
p2m_reactivate "P2MW.S_ModularCurve_CharPReduction_exists_coeffMap_eq_of_mem_modularLocalized_of_monic.J3C1"

open ModularCurve J3C1 in
theorem solution
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (f : LaurentSeries (AlgebraicClosure ℚ))
    (hf : f ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hint : ∃ P : Polynomial (Polynomial A), P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom
        ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        (jqModC (AlgebraicClosure ℚ))) f P = 0) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = f := by
  classical

  obtain ⟨r, s, hs, hfs⟩ := (CharPReduction.mem_localizedAtKer A.toSubring red
    (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hf
  have hs0 : (s : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply (CharPReduction.notMem_redKer_iff A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hs
    rw [show s = 0 from Subtype.ext h0, map_zero]
  obtain ⟨P, hPm, hP⟩ := hint

  obtain ⟨Tr, hTr, hr⟩ := J3C1.exists_finset_of_mem_modularRing_j3 A.toSubring N r.2
  obtain ⟨Ts, hTs, hs'⟩ := J3C1.exists_finset_of_mem_modularRing_j3 A.toSubring N s.2
  let TP : Finset (AlgebraicClosure ℚ) :=
    P.support.biUnion fun i => ((P.coeff i).support.image fun n =>
      (((P.coeff i).coeff n : A) : AlgebraicClosure ℚ))
  have hTP : (↑TP : Set (AlgebraicClosure ℚ)) ⊆ A := by
    intro c hc
    simp only [TP, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe] at hc
    obtain ⟨i, -, n, -, rfl⟩ := hc
    exact ((P.coeff i).coeff n).2
  have hTA : (↑(Tr ∪ Ts ∪ TP) : Set (AlgebraicClosure ℚ)) ⊆ A := by
    rw [Finset.coe_union, Finset.coe_union]
    exact Set.union_subset (Set.union_subset hTr hTs) hTP

  let K₀ : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (↑(Tr ∪ Ts ∪ TP) : Set (AlgebraicClosure ℚ))
  haveI : Finite (↑(Tr ∪ Ts ∪ TP) : Set (AlgebraicClosure ℚ)) := (Finset.finite_toSet _).to_subtype
  haveI : FiniteDimensional ℚ K₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  haveI : CharZero K₀ := charZero_of_injective_algebraMap (algebraMap ℚ K₀).injective
  haveI : NumberField K₀ := NumberField.mk
  haveI : IsDiscreteValuationRing (J3C1.D_j3 A K₀) :=
    J3C1.isDiscreteValuationRing_D_j3 A K₀ (J3C1.P_ne_bot_j3 A K₀ red)

  have hTφ : (↑(Tr ∪ Ts ∪ TP) : Set (AlgebraicClosure ℚ)) ⊆ Set.range (J3C1.phi_j3 A K₀) := by
    intro c hc
    have hcK : c ∈ K₀ := IntermediateField.subset_adjoin ℚ _ hc
    obtain ⟨d, hd⟩ := J3C1.exists_phi_eq_j3 A K₀ ⟨c, hcK⟩ (hTA hc)
    exact ⟨d, hd⟩
  have hle := J3C1.genRing_le_range_j3 (J3C1.phi_j3 A K₀) N hTφ

  have hsub : ∀ {X : Finset (AlgebraicClosure ℚ)}, X ⊆ Tr ∪ Ts ∪ TP →
      J3C1.genRing_j3 N (↑X : Set (AlgebraicClosure ℚ)) ≤ (coeffMap (J3C1.phi_j3 A K₀)).range :=
    fun hX => le_trans (J3C1.genRing_mono_j3 N (Finset.coe_subset.mpr hX)) hle
  obtain ⟨a, ha⟩ : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ (coeffMap (J3C1.phi_j3 A K₀)).range :=
    hsub (Finset.subset_union_left.trans Finset.subset_union_left) hr
  obtain ⟨b, hb⟩ : (s : LaurentSeries (AlgebraicClosure ℚ)) ∈ (coeffMap (J3C1.phi_j3 A K₀)).range :=
    hsub (Finset.subset_union_right.trans Finset.subset_union_left) hs'
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact hs0 hb.symm
  have hfab : f = coeffMap (J3C1.phi_j3 A K₀) a / coeffMap (J3C1.phi_j3 A K₀) b := by
    rw [ha, hb, eq_div_iff hs0, hfs]

  let g : Polynomial A →+* LaurentSeries (AlgebraicClosure ℚ) := Polynomial.eval₂RingHom
    ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
    (jqModC (AlgebraicClosure ℚ))
  have hPg : (P.map g).eval f = 0 := by rw [Polynomial.eval_map]; exact hP
  have hlifts : P.map g ∈ Polynomial.lifts (coeffMap (J3C1.phi_j3 A K₀)) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    by_cases hn : n ∈ P.support
    · refine hsub Finset.subset_union_right (J3C1.eval₂_mem_genRing_j3 A N (P.coeff n) ?_)
      intro m hm
      simp only [TP, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
        Finset.mem_coe]
      exact ⟨n, hn, m, hm, rfl⟩
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
      exact ⟨0, map_zero _⟩
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hPm.map g)
  have hintφ : (coeffMap (J3C1.phi_j3 A K₀)).IsIntegralElem f :=
    ⟨Q, hQm, by rw [Polynomial.eval₂_eq_eval_map, hQ, hPg]⟩

  obtain ⟨c, hc⟩ := ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
    (J3C1.phi_j3 A K₀) (J3C1.phi_injective_j3 A K₀) f ⟨a, b, hb0, hfab⟩ hintφ
  refine ⟨coeffMap (J3C1.psi_j3 A K₀) c, ?_⟩
  rw [coeffMap_coeffMap, J3C1.subtype_comp_psi_j3, hc]

end S_ModularCurve_CharPReduction_exists_coeffMap_eq_of_mem_modularLocalized_of_monic
end P2MW
export P2MW.S_ModularCurve_CharPReduction_exists_coeffMap_eq_of_mem_modularLocalized_of_monic (solution)
