-- Prove2me | solution 1 for ModularCurve.FullLevel.algebraMap_mem_of_le_igusaRing_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/aee02c07-b39f-5aed-988a-d2717b788702

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent

set_option autoImplicit false

noncomputable section

namespace C1ConstInPlace

open IsLocalRing Polynomial

section RootsOfUnity

variable {q : ℕ}

theorem charP_residueField (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) : CharP (ResidueField ↥A) q := by
  rw [CharP.charP_iff_prime_eq_zero hq]
  obtain ⟨hmem, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)).mp hA
  have h1 : ((q : ℕ) : ResidueField ↥A) = residue ↥A ((q : ℕ) : ↥A) := by
    rw [map_natCast]
  have h2 : ((q : ℕ) : ↥A) = ⟨(q : AlgebraicClosure ℚ), hmem⟩ := Subtype.ext (by simp)
  rw [h1, h2]
  exact (residue_eq_zero_iff _).mpr hmax

theorem exists_poly_coeff_not_dvd (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (x : ↥A) :
    ∃ P : ℤ[X], P.eval₂ (algebraMap ℤ ↥A) x = 0 ∧ ∃ i, ¬ (q : ℤ) ∣ P.coeff i := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have halg : IsAlgebraic ℤ (x : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨p, hp0, hpx⟩ := halg
  set P := p.primPart with hP
  have hPx : aeval (x : AlgebraicClosure ℚ) P = 0 := by
    rw [p.eq_C_content_mul_primPart, map_mul, aeval_C] at hpx
    refine (mul_eq_zero.mp hpx).resolve_left ?_
    rw [map_eq_zero_iff _ (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int, content_eq_zero_iff]
    exact hp0
  refine ⟨P, ?_, ?_⟩
  · apply Subtype.val_injective
    have h : ((P.eval₂ (algebraMap ℤ ↥A) x : ↥A) : AlgebraicClosure ℚ) =
        P.eval₂ (algebraMap ℤ (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) := by
      show A.subtype (P.eval₂ (algebraMap ℤ ↥A) x) = _
      rw [hom_eval₂, RingHom.ext_int (A.subtype.comp (algebraMap ℤ ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ))]
      rfl
    rw [h]
    rw [aeval_def] at hPx
    simpa using hPx
  · by_contra hall
    push Not at hall
    have hdvd : C (q : ℤ) ∣ P := (C_dvd_iff_dvd_coeff _ _).mpr hall
    have hu : IsUnit (q : ℤ) := (isPrimitive_primPart p) _ hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact hq.one_lt.ne' (by exact_mod_cast h1)
    · have : (0 : ℤ) ≤ q := Int.natCast_nonneg q
      omega

theorem exists_pow_sub_one_mem_maximalIdeal (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) (x : ↥A) (hx : IsUnit x) :
    ∃ n : ℕ, 0 < n ∧ x ^ n - 1 ∈ maximalIdeal ↥A := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField ↥A) q := charP_residueField hq A hA
  letI : Algebra (ZMod q) (ResidueField ↥A) := ZMod.algebra _ q
  have hxb0 : residue ↥A x ≠ 0 := (residue_ne_zero_iff_isUnit x).mpr hx

  obtain ⟨P, hPx, i, hi⟩ := exists_poly_coeff_not_dvd hq A x
  have hPq0 : P.map (Int.castRingHom (ZMod q)) ≠ 0 := by
    intro h
    have := congrArg (fun r => r.coeff i) h
    simp only [coeff_map, Int.coe_castRingHom, coeff_zero] at this
    exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this)
  have hPqx : aeval (residue ↥A x) (P.map (Int.castRingHom (ZMod q))) = 0 := by
    rw [aeval_def, eval₂_map,
      RingHom.ext_int ((algebraMap (ZMod q) (ResidueField ↥A)).comp (Int.castRingHom (ZMod q)))
        ((residue ↥A).comp (algebraMap ℤ ↥A)),
      ← hom_eval₂, hPx, map_zero]
  have halg : IsAlgebraic (ZMod q) (residue ↥A x) := ⟨_, hPq0, hPqx⟩
  have hint : IsIntegral (ZMod q) (residue ↥A x) := halg.isIntegral

  haveI : FiniteDimensional (ZMod q) ↥(IntermediateField.adjoin (ZMod q) {residue ↥A x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite ↥(IntermediateField.adjoin (ZMod q) {residue ↥A x}) := Module.finite_of_finite (ZMod q)
  obtain ⟨y, hy⟩ : ∃ y : ↥(IntermediateField.adjoin (ZMod q) {residue ↥A x}),
      (y : ResidueField ↥A) = residue ↥A x :=
    ⟨⟨_, IntermediateField.mem_adjoin_simple_self _ _⟩, rfl⟩
  have hy0 : y ≠ 0 := by
    intro h
    apply hxb0
    rw [← hy, h]
    rfl
  have hfin : IsOfFinOrder (Units.mk0 y hy0) := isOfFinOrder_of_finite _
  obtain ⟨n, hn⟩ : ∃ n, n = orderOf (Units.mk0 y hy0) := ⟨_, rfl⟩
  refine ⟨n, hn ▸ hfin.orderOf_pos, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, map_pow, map_one, sub_eq_zero]
  have h : (Units.mk0 y hy0) ^ n = 1 := by
    rw [hn]; exact pow_orderOf_eq_one _
  have h' := congrArg (fun z : (↥(IntermediateField.adjoin (ZMod q) {residue ↥A x}))ˣ =>
      ((z : ↥(IntermediateField.adjoin (ZMod q) {residue ↥A x})) : ResidueField ↥A)) h
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h'
  rw [← hy]
  simpa using h'

end RootsOfUnity

section Valuation

variable {F : Type*} [Field F]

theorem inv_notMem_of_not_isUnit (A : ValuationSubring F) (x : ↥A) (hx0 : x ≠ 0) (hx : ¬ IsUnit x) :
    (x : F)⁻¹ ∉ A := by
  intro h
  apply hx
  refine IsUnit.of_mul_eq_one (⟨_, h⟩ : ↥A) (Subtype.ext ?_)
  have hx0' : (x : F) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  simp [mul_inv_cancel₀ hx0']

theorem inv_mem_maximalIdeal_of_notMem (V : ValuationSubring F) (b : F) (hb : b ∉ V) :
    ∃ h : b⁻¹ ∈ V, (⟨b⁻¹, h⟩ : ↥V) ∈ maximalIdeal ↥V := by
  have hinv : b⁻¹ ∈ V := (V.mem_or_inv_mem b).resolve_left hb
  refine ⟨hinv, ?_⟩
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hb0 : b ≠ 0 := fun h => hb (h ▸ V.zero_mem)
  have hw' : b⁻¹ * (w : F) = 1 := by
    have := congrArg (fun z : ↥V => (z : F)) hw
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  have hwb : (w : F) = b := by
    calc (w : F) = b * (b⁻¹ * (w : F)) := by rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
      _ = b := by rw [hw', mul_one]
  exact hb (hwb ▸ w.2)

end Valuation

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem algebraMap_mem_iff_of_gaussPresentation (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : ValuationSubring ↥(fieldBar q M'))
    (hO : ∀ f : ↥(fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (z : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z ∈ O ↔ z ∈ A := by
  have hcoe : ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z : ↥(fieldBar q M')) :
      LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.single 0 z := by
    rw [← ModularCurve.algebraMap_laurentSeries_eq_single]; rfl
  rw [hO]
  constructor
  · rintro ⟨x, y, hy, hxy⟩
    rw [hcoe] at hxy
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (coeffMap (IsLocalRing.residue ↥A) y).coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (HahnSeries.ext (funext h))
    rw [coeffMap_coeff] at hn
    have hunit : IsUnit (y.coeff n) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn
    have hcoeff := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff n) hxy
    simp only [HahnSeries.coeff_single_zero_mul, coeffMap_coeff] at hcoeff
    obtain ⟨b, hb⟩ := hunit.exists_right_inv
    have hz : z = ((x.coeff n * b : ↥A) : AlgebraicClosure ℚ) := by
      have hb' : ((y.coeff n : ↥A) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := by
        have := congrArg (fun a : ↥A => (a : AlgebraicClosure ℚ)) hb
        simpa using this
      calc z = z * (((y.coeff n : ↥A) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ)) := by
              rw [hb', mul_one]
        _ = (z * ((y.coeff n : ↥A) : AlgebraicClosure ℚ)) * (b : AlgebraicClosure ℚ) := by ring
        _ = ((x.coeff n * b : ↥A) : AlgebraicClosure ℚ) := by
              rw [show z * ((y.coeff n : ↥A) : AlgebraicClosure ℚ) = A.subtype (x.coeff n) from hcoeff]
              rfl
    rw [hz]
    exact SetLike.coe_mem _
  · intro hz
    refine ⟨HahnSeries.single 0 ⟨z, hz⟩, 1, ?_, ?_⟩
    · rw [map_one]; exact one_ne_zero
    · rw [map_one, mul_one, hcoe, coeffMap_single]; rfl

theorem algebraMap_mem_igusaRing_iff (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (ℓ : CuspidalType.ProjLine q) (z : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z ∈ OIg ℓ ↔ z ∈ A := by
  obtain ⟨γ, -, -, hO⟩ := hIg ℓ
  rw [hO, ValuationSubring.mem_comap]
  have : (levelAutBar q M' ζ γ).toAlgHom.toRingHom (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z :=
    (levelAutBar q M' ζ γ).toAlgHom.commutes z
  rw [this]
  exact algebraMap_mem_iff_of_gaussPresentation q M' A _ hIg_inf z

end C1ConstInPlace

end

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

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
    (ℓ : CuspidalType.ProjLine q) (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg ℓ) :
    ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ V := by

  have hconst : ∀ z : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z ∈ OIg ℓ ↔ z ∈ A :=
    C1ConstInPlace.algebraMap_mem_igusaRing_iff q M' A ζ OIg hIg_inf hIg ℓ

  have hmemV : ∀ (b : ↥F₀) (z : AlgebraicClosure ℚ),
      (b : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z → z⁻¹ ∉ A → b ∈ V := by
    intro b z hbz hz
    refine (V.mem_or_inv_mem b).resolve_right fun hbinv => hz ?_
    rw [← hconst]
    have : ((b⁻¹ : ↥F₀) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') z⁻¹ := by
      rw [map_inv₀, ← hbz]; simp
    rw [← this]
    exact hV _ hbinv
  intro a
  by_cases hua : IsUnit a
  ·
    have hux : IsUnit (ι a) := hua.map ι
    obtain ⟨n, hn, hmax⟩ :=
      C1ConstInPlace.exists_pow_sub_one_mem_maximalIdeal (Fact.out : q.Prime) A hA (ι a) hux

    have hbn : (algebraMap A₀ ↥F₀ a) ^ n - 1 ∈ V := by
      have e1 : ((ι a ^ n - 1 : ↥A) : AlgebraicClosure ℚ) = ((ι a : ↥A) : AlgebraicClosure ℚ) ^ n - 1 := by
        push_cast; ring
      have hcoe : (((algebraMap A₀ ↥F₀ a) ^ n - 1 : ↥F₀) : ↥(fieldBar q M')) =
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (((ι a ^ n - 1 : ↥A)) : AlgebraicClosure ℚ) := by
        rw [e1, map_sub, map_pow, map_one, ← hj₀ a]
        push_cast; ring
      by_cases h0 : (ι a ^ n - 1 : ↥A) = 0
      · have : (algebraMap A₀ ↥F₀ a) ^ n - 1 = 0 := by
          apply Subtype.ext
          rw [hcoe, h0]; simp
        rw [this]; exact V.zero_mem
      · refine hmemV _ _ hcoe ?_
        exact C1ConstInPlace.inv_notMem_of_not_isUnit A _ h0 ((mem_maximalIdeal _).mp hmax)

    by_contra hbV
    obtain ⟨hinv, hinvmax⟩ := C1ConstInPlace.inv_mem_maximalIdeal_of_notMem V (algebraMap A₀ ↥F₀ a) hbV
    have hb0 : algebraMap A₀ ↥F₀ a ≠ 0 := fun h => hbV (h ▸ V.zero_mem)
    have hpow : (⟨(algebraMap A₀ ↥F₀ a)⁻¹, hinv⟩ : ↥V) ^ n ∈ maximalIdeal ↥V :=
      Ideal.pow_mem_of_mem _ hinvmax n hn
    have hone : (1 : ↥V) = (⟨(algebraMap A₀ ↥F₀ a)⁻¹, hinv⟩ : ↥V) ^ n * ⟨(algebraMap A₀ ↥F₀ a) ^ n - 1, hbn⟩ +
        (⟨(algebraMap A₀ ↥F₀ a)⁻¹, hinv⟩ : ↥V) ^ n := by
      apply Subtype.ext
      simp only [OneMemClass.coe_one, AddMemClass.coe_add, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_sub, mul_one, sub_add_cancel, inv_pow, inv_mul_cancel₀ (pow_ne_zero n hb0)]
    have h1 : (1 : ↥V) ∈ maximalIdeal ↥V := by
      rw [hone]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpow) hpow
    exact (maximalIdeal.isMaximal ↥V).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  ·
    have hna : ¬ IsUnit (ι a) := fun h => hua (IsLocalHom.map_nonunit a h)
    by_cases ha0 : ι a = 0
    · have : algebraMap A₀ ↥F₀ a = 0 := by
        apply Subtype.ext
        rw [hj₀ a, ha0]; simp
      rw [this]; exact V.zero_mem
    · exact hmemV _ _ (hj₀ a) (C1ConstInPlace.inv_notMem_of_not_isUnit A _ ha0 hna)

end S_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent
end P2MW
export P2MW.S_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent (solution)
