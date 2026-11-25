-- Prove2me | solution 1 for GlobalTheory.isIntegral_iff_mem_span_one_tmul_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:33.075477+00:00
-- url     : https://prove2.me/submissions/51135cf0-197c-477e-ba75-a53c63e5b26f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial
namespace GlobalTheory
open NumberField in
open scoped TensorProduct in
open Polynomial in
variable (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R']
  [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F']
  [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']
  (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L] in
private theorem exists_algebraMap_eq_of_algebraMap_eq_algebraMap {c : F} {a : R'}
    (h : algebraMap F F' c = algebraMap R' F' a) : ∃ r : R, algebraMap R F r = c := by
  rcases ValuationRing.isInteger_or_isInteger R c with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  · by_cases hc : c = 0
    · exact ⟨0, by simp [hc]⟩
    have hF : algebraMap R' F' (algebraMap R R' r * a) = algebraMap R' F' 1 := by
      rw [map_mul, ← h, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', hr,
        ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
    have hu : IsUnit (algebraMap R R' r) :=
      IsUnit.of_mul_eq_one a (IsFractionRing.injective R' F' hF)
    obtain ⟨u, rfl⟩ := (isUnit_of_map_unit (algebraMap R R') r hu)
    refine ⟨(u⁻¹ : Rˣ), ?_⟩
    rw [map_units_inv, hr, inv_inv]
open NumberField in
open scoped TensorProduct in
open Polynomial in
variable (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R']
  [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F']
  [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']
  (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L] in
private theorem isIntegral_of_isIntegral_one_tmul' {y : L}
    (hy : IsIntegral R' ((1 : F') ⊗ₜ[F] y : F' ⊗[F] L)) : IsIntegral R y := by
  obtain ⟨p, hpm, hp⟩ := hy
  have hyF : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  set f := minpoly F y with hf
  set f' : F'[X] := f.map (algebraMap F F') with hf'
  have hfm : f'.Monic := (minpoly.monic hyF).map _
  set t : F' ⊗[F] L := (1 : F') ⊗ₜ[F] y with ht
  have ht' : t = Algebra.TensorProduct.includeRight y := rfl
  have hft : aeval t f' = 0 := by
    rw [hf', aeval_map_algebraMap, ht', aeval_algHom_apply, minpoly.aeval, map_zero]
  set g : F'[X] := p.map (algebraMap R' F') with hg
  have hgt : aeval t g = 0 := by
    rw [hg, aeval_map_algebraMap, aeval_def, hp]
  have hind : LinearIndependent F' fun i : Fin f.natDegree => t ^ (i : ℕ) := by
    have := Module.Flat.linearIndependent_one_tmul (S := F') (linearIndependent_pow (K := F) y)
    convert this using 2 with i
    rw [ht, Algebra.TensorProduct.tmul_pow, one_pow]
  have hdvd : f' ∣ g := by
    rw [← modByMonic_eq_zero_iff_dvd hfm]
    set r := g %ₘ f' with hr
    have hrt : aeval t r = 0 := by
      have := modByMonic_add_div g f'
      rw [← hr] at this
      have h2 := congrArg (aeval t) this
      rw [map_add, map_mul, hft, zero_mul, add_zero, hgt] at h2
      exact h2
    have hdeg : r.degree < f.natDegree := by
      have := degree_modByMonic_lt g hfm
      rwa [hf', degree_map, degree_eq_natDegree (minpoly.ne_zero hyF)] at this
    have hcoeff : ∀ i : Fin f.natDegree, r.coeff i = 0 := by
      rw [Fintype.linearIndependent_iff] at hind
      apply hind
      rw [aeval_eq_sum_range' (p := r) (n := f.natDegree) ?_] at hrt
      · rw [← hrt, Fin.sum_univ_eq_sum_range (fun i => r.coeff i • t ^ i)]
      · by_cases h0 : r = 0
        · rw [h0, natDegree_zero]; exact minpoly.natDegree_pos hyF
        · exact (natDegree_lt_iff_degree_lt h0).2 hdeg
    ext i
    rw [coeff_zero]
    by_cases hi : i < f.natDegree
    · exact hcoeff ⟨i, hi⟩
    · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.1 hi))
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F' hpm (hg ▸ hdvd)
  rw [hfm.leadingCoeff, C_1, mul_one] at hq
  have hlift : f ∈ lifts (algebraMap R F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have : algebraMap F F' (f.coeff i) = algebraMap R' F' (q.coeff i) := by
      rw [← coeff_map, ← hf', ← hq, coeff_map]
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_algebraMap_eq_algebraMap R R' F F' this
    exact ⟨r, hr⟩
  obtain ⟨q', hq'map, -, hq'm⟩ := lifts_and_degree_eq_and_monic hlift (minpoly.monic hyF)
  refine ⟨q', hq'm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq'map, hf, minpoly.aeval]
end GlobalTheory
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial
open GlobalTheory
open NumberField
open scoped TensorProduct
open Polynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Algebra R L] [IsScalarTower R F L] (x : F' ⊗[F] L), IsIntegral R' x ↔ x ∈ Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L)) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres L _ _ _ _ _ _ x
  set M := Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L))
    with hM
  have hMint : ∀ z ∈ M, IsIntegral R' z := by
    intro z hz
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (integralClosure R' (F' ⊗[F] L)))).2
      ?_ hz
    rintro _ ⟨s, hs, rfl⟩
    have hs' : IsIntegral R s := hs
    exact (hs'.map (Algebra.TensorProduct.includeRight.restrictScalars R :
      L →ₐ[R] F' ⊗[F] L)).tower_top
  refine ⟨fun hx => ?_, hMint x⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set ϖ := algebraMap R R' π with hϖdef
  have hmax' : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ} := by
    rw [← hmax, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hϖ : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).2 hmax'
  have happrox : ∀ a : R', ∃ r : R, ∃ b : R', a = algebraMap R R' r + ϖ * b := by
    intro a
    obtain ⟨c, hc⟩ := hres (IsLocalRing.residue R' a)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    rw [IsLocalRing.ResidueField.map_residue] at hc
    have hmem : a - algebraMap R R' r ∈ Ideal.span {ϖ} := by
      rw [← hmax', ← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨r, b, eq_add_of_sub_eq' (hb.symm.trans (mul_comm _ _))⟩
  have hsm : ∀ (c : R) (s : L), algebraMap R R' c • ((1 : F') ⊗ₜ[F] s) =
      (1 : F') ⊗ₜ[F] (algebraMap R L c * s) := by
    intro c s
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R F F', Algebra.algebraMap_eq_smul_one (A := F'),
      TensorProduct.smul_tmul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R R' d ≠ 0 := by
    intro d hd
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
    rw [map_mul, map_pow]
    exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ hϖ.ne_zero)
  have hstep : ∀ z ∈ M, ∃ s ∈ integralClosure R L, ∃ m ∈ M, z = (1 : F') ⊗ₜ[F] s + ϖ • m := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, rfl⟩ := hz
      exact ⟨s, hs, 0, M.zero_mem, by rw [smul_zero, add_zero]⟩
    | zero =>
      exact ⟨0, (integralClosure R L).zero_mem, 0, M.zero_mem,
        by rw [TensorProduct.tmul_zero, smul_zero, add_zero]⟩
    | add z w _ _ hz hw =>
      obtain ⟨s, hs, m, hm, rfl⟩ := hz
      obtain ⟨s', hs', m', hm', rfl⟩ := hw
      exact ⟨s + s', add_mem hs hs', m + m', add_mem hm hm',
        by rw [TensorProduct.tmul_add, smul_add]; abel⟩
    | smul a z _ hz =>
      obtain ⟨s, hs, m, hm, rfl⟩ := hz
      obtain ⟨r, b, rfl⟩ := happrox a
      refine ⟨algebraMap R L r * s, mul_mem (algebraMap_mem _ r) hs,
        b • ((1 : F') ⊗ₜ[F] s) + (algebraMap R R' r + ϖ * b) • m,
        add_mem (M.smul_mem _ (Submodule.subset_span ⟨s, hs, rfl⟩)) (M.smul_mem _ hm), ?_⟩
      rw [← hsm]
      module
  have hden : ∀ z : F' ⊗[F] L, ∃ c : R', c ≠ 0 ∧ c • z ∈ M := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
    | tmul a l =>
      obtain ⟨n, e, he, rfl⟩ := IsFractionRing.div_surjective (A := R') a
      obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (nonZeroDivisors R) l (Algebra.IsIntegral.isIntegral (R := F) l)
      have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
      have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
      refine ⟨e * algebraMap R R' d, mul_ne_zero he0 (hinj _ hd0), ?_⟩
      have hcalc : (e * algebraMap R R' d) • ((algebraMap R' F' n / algebraMap R' F' e) ⊗ₜ[F] l) =
          n • (algebraMap R R' d • ((1 : F') ⊗ₜ[F] l)) := by
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one]
        congr 1
        have : algebraMap R' F' e ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective R' F')).2 he0
        rw [map_mul]
        field_simp
      rw [hcalc, hsm, ← Algebra.smul_def]
      exact M.smul_mem _ (Submodule.subset_span ⟨_, hd, rfl⟩)
    | add z w hz hw =>
      obtain ⟨c, hc, hcz⟩ := hz
      obtain ⟨c', hc', hcw⟩ := hw
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      have : (c * c') • (z + w) = c' • (c • z) + c • (c' • w) := by module
      rw [this]
      exact add_mem (M.smul_mem _ hcz) (M.smul_mem _ hcw)
  have hπL : algebraMap R L π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R F L]
    exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero)
  have hϖF : algebraMap R' F' ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R' F')).2 hϖ.ne_zero
  have hmain : ∀ z : F' ⊗[F] L, IsIntegral R' z → ϖ • z ∈ M → z ∈ M := by
    intro z hz hϖz
    obtain ⟨s, hs, m, hm, hzm⟩ := hstep _ hϖz
    have hy : ϖ • ((1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s)) = (1 : F') ⊗ₜ[F] s := by
      rw [hϖdef, hsm, ← mul_assoc, mul_inv_cancel₀ hπL, one_mul]
    have heq : z = (1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) + m := by
      have h1 : ϖ • z = ϖ • ((1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) + m) := by
        rw [smul_add, hy, hzm]
      rw [← algebraMap_smul F' ϖ z, ← algebraMap_smul F' ϖ (_ + m)] at h1
      exact smul_right_injective _ hϖF h1
    have hyint : IsIntegral R ((algebraMap R L π)⁻¹ * s) := by
      refine isIntegral_of_isIntegral_one_tmul' R R' F F' L ?_
      have : (1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) = z - m := by rw [heq]; abel
      rw [this]
      exact hz.sub (hMint m hm)
    rw [heq]
    exact add_mem (Submodule.subset_span ⟨_, hyint, rfl⟩) hm
  have hpow : ∀ (k : ℕ) (z : F' ⊗[F] L), IsIntegral R' z → ϖ ^ k • z ∈ M → z ∈ M := by
    intro k
    induction k with
    | zero => intro z _ hz; rwa [pow_zero, one_smul] at hz
    | succ k ih =>
      intro z hz hkz
      refine hmain z hz (ih _ ?_ ?_)
      · rw [Algebra.smul_def]
        exact isIntegral_algebraMap.mul hz
      · rwa [smul_smul, ← pow_succ]
  obtain ⟨c, hc, hcx⟩ := hden x
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine hpow k x hx ?_
  have := M.smul_mem (↑u⁻¹ : R') hcx
  rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
end _root_.GlobalTheory
end GlobalTheory
