-- Prove2me | solution 1 for NeronModelInfra.TopFormOrder.ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ae4b89ed-2b2b-51a5-8725-460fa99310c4

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import Theorems.Thm_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer
import Theorems.Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder
open scoped TensorProduct

namespace T5BC

lemma map_two_towers (R R' K K' O₀ O F₀ F : Type u)
    [CommRing R] [CommRing R'] [Algebra R R']
    [Field K] [Algebra R K] [Field K'] [Algebra R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [CommRing O₀] [Algebra R O₀]
    [Field F₀] [Algebra O₀ F₀] [Algebra K F₀] [Algebra R F₀] [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    [CommRing O] [Algebra R' O]
    [Field F] [Algebra O F] [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' K' F]
    [Algebra O₀ O] [Algebra R O] [IsScalarTower R O₀ O] [IsScalarTower R R' O]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F]
    [Algebra K F] [IsScalarTower K K' F] [IsScalarTower K F₀ F]
    (x : Ω[O₀⁄R]) :
    KaehlerDifferential.map K K' F₀ F (KaehlerDifferential.map R K O₀ F₀ x) =
      KaehlerDifferential.map R' K' O F (KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O x)) := by
  have key : ∀ x ∈ Submodule.span O₀ (Set.range (KaehlerDifferential.D R O₀)),
      KaehlerDifferential.map K K' F₀ F (KaehlerDifferential.map R K O₀ F₀ x) =
      KaehlerDifferential.map R' K' O F (KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O x)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      simp only [KaehlerDifferential.map_D]
      congr 1
      rw [← IsScalarTower.algebraMap_apply O₀ F₀ F, Algebra.algebraMap_self, RingHom.id_apply,
        ← IsScalarTower.algebraMap_apply O₀ O F]
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul s y _ hy =>
      rw [(KaehlerDifferential.map R K O₀ F₀).map_smul s y, (KaehlerDifferential.map R R O₀ O).map_smul s y,
        ← IsScalarTower.algebraMap_smul F₀ s ((KaehlerDifferential.map R K O₀ F₀) y),
        (KaehlerDifferential.map K K' F₀ F).map_smul, hy,
        ← IsScalarTower.algebraMap_smul O s ((KaehlerDifferential.map R R O₀ O) y),
        (KaehlerDifferential.map R R' O O).map_smul, (KaehlerDifferential.map R' K' O F).map_smul,
        ← IsScalarTower.algebraMap_smul F (algebraMap O₀ F₀ s),
        ← IsScalarTower.algebraMap_smul F (algebraMap O₀ O s),
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact key x (by rw [KaehlerDifferential.span_range_derivation]; trivial)

lemma addOrd_pow (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] {x : L} (hx : x ≠ 0) (n : ℕ) :
    addOrd O L (x ^ n) = n * addOrd O L x := by
  obtain ⟨hmul, -, hunit, -⟩ := addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer O L
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, ← map_one (algebraMap O L)]
    exact (hunit 1 one_ne_zero).mpr isUnit_one
  | succ n ih => rw [pow_succ, hmul _ _ (pow_ne_zero n hx) hx, ih]; push_cast; ring

end T5BC

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (R R' K K' O₀ O F₀ F : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [Algebra R O] [IsScalarTower R O₀ O] [IsScalarTower R R' O]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F]
    [Algebra K F] [IsScalarTower K K' F] [IsScalarTower K F₀ F]
    (d : ℕ) (b : Module.Basis (Fin d) O₀ (Ω[O₀⁄R]))
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    (hρ : (letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
      topFormMap R' K' O F d (exteriorPower.ιMulti O d
        (fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b i))))) ≠ 0)
    (a : F₀) (ha : a ≠ 0) :
    letI := moduleAlong O₀ F₀ (⋀[F₀]^d (Ω[F₀⁄K]))
    letI := moduleAlong F₀ F (⋀[F]^d (Ω[F⁄K']))
    ord R' K' O d F (topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b))) =
      ord R K O₀ d F₀ (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b)) := by
  classical
  letI iO₀ := moduleAlong O₀ F₀ (⋀[F₀]^d (Ω[F₀⁄K]))
  letI iF₀ := moduleAlong F₀ F (⋀[F]^d (Ω[F⁄K']))
  letI iO := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))

  obtain ⟨hmul₀, hnn₀, hunit₀, hunif₀⟩ := addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer O₀ F₀
  obtain ⟨hmul, hnn, hunit, hunif⟩ := addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer O F

  let e : (O ⊗[O₀] Ω[O₀⁄R]) ≃ₗ[O] Ω[O⁄R'] := LinearEquiv.ofBijective _ hbc
  let c : Module.Basis (Fin d) O (Ω[O⁄R']) := (Algebra.TensorProduct.basis O b).map e
  have hc : (c : Fin d → Ω[O⁄R']) =
      fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b i)) := by
    funext i
    show e (Algebra.TensorProduct.basis O b i) = _
    rw [Algebra.TensorProduct.basis_apply]
    show ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O)
      ((1 : O) ⊗ₜ[O₀] b i) = _
    rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul, LinearMap.restrictScalars_apply]

  obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀ : ⋀[F₀]^d (Ω[F₀⁄K]), ρ₀ = topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b) :=
    ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ⋀[F]^d (Ω[F⁄K']), ρ = topFormMap R' K' O F d (exteriorPower.ιMulti O d c) := ⟨_, rfl⟩

  have hT : topFormMap K K' F₀ F d ρ₀ = ρ := by
    rw [hρ₀def, hρdef]
    show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong K K' F₀ F d)
        (exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R K O₀ F₀ d) (exteriorPower.ιMulti O₀ d b)) =
      exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F d) (exteriorPower.ιMulti O d c)
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong K K' F₀ F d)
        (exteriorPower.ιMulti F₀ d (fun i => KaehlerDifferential.map R K O₀ F₀ (b i))) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    show exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map K K' F₀ F (KaehlerDifferential.map R K O₀ F₀ (b i))) =
      exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O F (c i))
    congr 1
    funext i
    rw [hc]
    exact T5BC.map_two_towers R R' K K' O₀ O F₀ F (b i)

  have hρ' : ρ ≠ 0 := by rw [hρdef, hc]; exact hρ
  have hρ₀ : ρ₀ ≠ 0 := by
    intro h0; apply hρ'; rw [← hT, h0, map_zero]

  have hω : topFormMap K K' F₀ F d (a • ρ₀) = algebraMap F₀ F a • ρ := by
    rw [map_smul, hT]; rfl

  have haF : algebraMap F₀ F a ≠ 0 := (map_ne_zero_iff _ (algebraMap F₀ F).injective).mpr ha
  have hω' : topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b)) =
      algebraMap F₀ F a • topFormMap R' K' O F d (exteriorPower.ιMulti O d c) := by
    rw [← hρ₀def, hω, hρdef]
  have hρc : topFormMap R' K' O F d (exteriorPower.ιMulti O d c) ≠ 0 := by rw [← hρdef]; exact hρ'
  have hρb : topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b) ≠ 0 := by rw [← hρ₀def]; exact hρ₀
  rw [hω', (integralTopForms_eq_span_and_ord_smul_of_basis R' K' O F d c).2 _ haF hρc,
    (integralTopForms_eq_span_and_ord_smul_of_basis R K O₀ F₀ d b).2 _ ha hρb]

  have key : ∀ x : O₀, x ≠ 0 →
      addOrd O F (algebraMap F₀ F (algebraMap O₀ F₀ x)) = addOrd O₀ F₀ (algebraMap O₀ F₀ x) := by
    intro x hx
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hπm : IsLocalRing.maximalIdeal R = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ

    have hπO₀ : IsLocalRing.maximalIdeal O₀ = Ideal.span {algebraMap R O₀ π} := by
      rw [← hO₀, hπm, Ideal.map_span, Set.image_singleton]
    have hπR' : IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' π} := by
      rw [← hRR', hπm, Ideal.map_span, Set.image_singleton]
    have h1O₀ : addOrd O₀ F₀ (algebraMap O₀ F₀ (algebraMap R O₀ π)) = 1 := hunif₀ R hO₀ π hπm
    have h1O : addOrd O F (algebraMap O F (algebraMap R' O (algebraMap R R' π))) = 1 := hunif R' hO _ hπR'

    have hirr₀ : Irreducible (algebraMap R O₀ π) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hπO₀
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hirr₀

    have hπ₀F₀ : algebraMap O₀ F₀ (algebraMap R O₀ π) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr hirr₀.ne_zero
    have hxF₀ : algebraMap O₀ F₀ x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr hx
    have huF₀ : algebraMap O₀ F₀ (u : O₀) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr u.ne_zero

    have e₀ : addOrd O₀ F₀ (algebraMap O₀ F₀ x) = n := by
      have := congrArg (fun y => addOrd O₀ F₀ (algebraMap O₀ F₀ y)) hu
      simp only [map_mul, map_pow] at this
      rw [hmul₀ _ _ hxF₀ huF₀, (hunit₀ _ u.ne_zero).mpr u.isUnit, add_zero,
        T5BC.addOrd_pow O₀ F₀ hπ₀F₀, h1O₀, mul_one] at this
      exact this

    have hOF : ∀ y : O₀, algebraMap F₀ F (algebraMap O₀ F₀ y) = algebraMap O F (algebraMap O₀ O y) := by
      intro y
      rw [← IsScalarTower.algebraMap_apply O₀ F₀ F, ← IsScalarTower.algebraMap_apply O₀ O F]

    have huO : algebraMap O₀ O x * algebraMap O₀ O (u : O₀) = (algebraMap R' O (algebraMap R R' π)) ^ n := by
      rw [← map_mul, hu, map_pow, ← IsScalarTower.algebraMap_apply R O₀ O, IsScalarTower.algebraMap_apply R R' O]
    have hπO : algebraMap R' O (algebraMap R R' π) ≠ 0 := by
      intro h0
      apply IsDiscreteValuationRing.not_a_field O
      rw [← hO, hπR', Ideal.map_span, Set.image_singleton, h0, Ideal.span_singleton_eq_bot]
    have huOunit : IsUnit (algebraMap O₀ O (u : O₀)) := u.isUnit.map _
    have hxO : algebraMap O₀ O x ≠ 0 := by
      intro h0
      have : (algebraMap R' O (algebraMap R R' π)) ^ n = 0 := by rw [← huO, h0, zero_mul]
      exact pow_ne_zero n hπO this
    have hπOF : algebraMap O F (algebraMap R' O (algebraMap R R' π)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O F)).mpr hπO
    have hxOF : algebraMap O F (algebraMap O₀ O x) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O F)).mpr hxO
    have huOF : algebraMap O F (algebraMap O₀ O (u : O₀)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O F)).mpr huOunit.ne_zero
    have e₁ : addOrd O F (algebraMap O F (algebraMap O₀ O x)) = n := by
      have := congrArg (fun y => addOrd O F (algebraMap O F y)) huO
      simp only [map_mul, map_pow] at this
      rw [hmul _ _ hxOF huOF, (hunit _ huOunit.ne_zero).mpr huOunit, add_zero,
        T5BC.addOrd_pow O F hπOF, h1O, mul_one] at this
      exact this
    rw [hOF, e₁, e₀]

  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O₀) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF₀ : algebraMap O₀ F₀ y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr hy0
  have hx0 : x ≠ 0 := by
    intro h0; apply ha; rw [← hxy, h0, map_zero, zero_div]
  have hxF₀ : algebraMap O₀ F₀ x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr hx0
  have hay : a * algebraMap O₀ F₀ y = algebraMap O₀ F₀ x := by
    rw [← hxy, div_mul_cancel₀ _ hyF₀]

  have e₂ : addOrd O₀ F₀ a + addOrd O₀ F₀ (algebraMap O₀ F₀ y) = addOrd O₀ F₀ (algebraMap O₀ F₀ x) := by
    rw [← hmul₀ _ _ ha hyF₀, hay]

  have hyF : algebraMap F₀ F (algebraMap O₀ F₀ y) ≠ 0 := (map_ne_zero_iff _ (algebraMap F₀ F).injective).mpr hyF₀
  have e₃ : addOrd O F (algebraMap F₀ F a) + addOrd O F (algebraMap F₀ F (algebraMap O₀ F₀ y)) =
      addOrd O F (algebraMap F₀ F (algebraMap O₀ F₀ x)) := by
    rw [← hmul _ _ haF hyF, ← map_mul, hay]
  rw [key x hx0, key y hy0] at e₃
  linarith

end S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
end P2MW
export P2MW.S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq (solution)
