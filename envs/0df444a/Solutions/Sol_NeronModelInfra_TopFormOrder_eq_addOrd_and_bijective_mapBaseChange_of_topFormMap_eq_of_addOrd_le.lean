-- Prove2me | solution 1 for NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f70dc11c-2960-5f5f-8397-707f64a6b250

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import Theorems.Thm_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
import Theorems.Thm_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import Theorems.Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le

set_option autoImplicit false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

namespace BenchNSqueeze

theorem kaehlerMap_kaehlerMap
    (R₁ R₂ R₃ O₁ O₂ O₃ : Type u) [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [CommRing O₁] [CommRing O₂] [CommRing O₃]
    [Algebra R₁ R₂] [Algebra R₂ R₃] [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃]
    [Algebra R₁ O₁] [Algebra R₂ O₂] [Algebra R₃ O₃]
    [Algebra O₁ O₂] [Algebra O₂ O₃] [Algebra O₁ O₃] [IsScalarTower O₁ O₂ O₃]
    [Algebra R₁ O₂] [IsScalarTower R₁ O₁ O₂] [IsScalarTower R₁ R₂ O₂]
    [Algebra R₂ O₃] [IsScalarTower R₂ O₂ O₃] [IsScalarTower R₂ R₃ O₃]
    [Algebra R₁ O₃] [IsScalarTower R₁ O₁ O₃] [IsScalarTower R₁ R₃ O₃]
    (x : Ω[O₁⁄R₁]) :
    KaehlerDifferential.map R₂ R₃ O₂ O₃ (KaehlerDifferential.map R₁ R₂ O₁ O₂ x) =
      KaehlerDifferential.map R₁ R₃ O₁ O₃ x := by
  have hx : x ∈ Submodule.span O₁ (Set.range (KaehlerDifferential.D R₁ O₁)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨o, rfl⟩ := hx
      simp only [KaehlerDifferential.map_D]
      rw [← IsScalarTower.algebraMap_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul o x _ hx =>
      rw [LinearMap.map_smul, LinearMap.map_smul, ← hx,
        ← algebraMap_smul O₂ o (KaehlerDifferential.map R₁ R₂ O₁ O₂ x),
        LinearMap.map_smul, algebraMap_smul]

theorem topFormMap_ιMulti (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [Algebra R' O] [CommRing F] [Algebra O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F] (d : ℕ) (v : Fin d → Ω[O⁄R']) :
    topFormMap R' K' O F d (exteriorPower.ιMulti O d v) =
      exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O F (v i)) := by
  letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F d) (exteriorPower.ιMulti O d v) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end BenchNSqueeze

open BenchNSqueeze in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution

    (R K R' K' : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [IsScalarTower R R' K']

    (O₀ F₀ : Type u)
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : F₀) (ha : a ≠ 0)

    (O₁ O' : Type u)
    [CommRing O₁] [Algebra R O₁]
    [CommRing O'] [IsDomain O'] [Algebra R' O'] [Algebra O₁ O'] [Algebra R O']
    [IsScalarTower R O₁ O'] [IsScalarTower R R' O']
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O'))

    (O F : Type u)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra R O] [IsScalarTower R R' O]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [IsScalarTower R O₀ O]
    [Algebra O' O] [IsScalarTower R' O' O] [Algebra O₁ O] [IsScalarTower O₁ O' O] [IsScalarTower R O₁ O]
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower K K' F]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F] [IsScalarTower K F₀ F]
    [Algebra O₁ F] [IsScalarTower O₁ O F] [IsScalarTower R O₁ F]

    (σ : ⋀[F]^d (Ω[F⁄K]))
    (hT : σ = (algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m) •
        topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁))
    (hX : topFormMap K K' F F d σ =
        topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : addOrd O₀ F₀ a ≤ m) :
    m = addOrd O₀ F₀ a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) := by
  classical

  haveI : IsScalarTower R K' F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R K F, IsScalarTower.algebraMap_eq R K K', ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq K K' F])
  haveI : IsScalarTower O₁ O' F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq O₁ O F, IsScalarTower.algebraMap_eq O₁ O' O,
      IsScalarTower.algebraMap_eq O' O F, RingHom.comp_assoc])
  haveI : IsScalarTower R O' F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R O F, IsScalarTower.algebraMap_eq R R' O, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R' O F, IsScalarTower.algebraMap_eq R' O' F, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R R' O'])

  set ϖ' : R' := algebraMap R R' ϖ with hϖ'def
  have hϖ' : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ'} := by
    rw [← hRR', hϖ, Ideal.map_span, Set.image_singleton]

  let eO : (O ⊗[O₀] Ω[O₀⁄R]) ≃ₗ[O] Ω[O⁄R'] := LinearEquiv.ofBijective _ hbc
  let b : Module.Basis (Fin d) O (Ω[O⁄R']) := (Algebra.TensorProduct.basis O b₀).map eO
  have hbcoe : (b : Fin d → Ω[O⁄R']) =
      fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b₀ i)) := by
    funext i
    show eO (Algebra.TensorProduct.basis O b₀ i) = _
    rw [Algebra.TensorProduct.basis_apply]
    show ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O)
      ((1 : O) ⊗ₜ[O₀] b₀ i) = _
    rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul, LinearMap.restrictScalars_apply]

  let eO' : (O' ⊗[O₁] Ω[O₁⁄R]) ≃ₗ[O'] Ω[O'⁄R'] := LinearEquiv.ofBijective _ hbc'
  let b' : Module.Basis (Fin d) O' (Ω[O'⁄R']) := (Algebra.TensorProduct.basis O' b₁).map eO'
  have hb'coe : ∀ i, b' i = KaehlerDifferential.map R R' O₁ O' (b₁ i) := by
    intro i
    show eO' (Algebra.TensorProduct.basis O' b₁ i) = _
    rw [Algebra.TensorProduct.basis_apply]
    show ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O')
      ((1 : O') ⊗ₜ[O₁] b₁ i) = _
    rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul, LinearMap.restrictScalars_apply]
    exact kaehlerMap_kaehlerMap R R R' O₁ O' O' (b₁ i)

  have hgen : topFormMap K K' F F d (topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁)) =
      topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') := by
    rw [topFormMap_topFormMap R K K' O₁ F F d, ← topFormMap_topFormMap R R' K' O₁ O' F d,
      topFormMap_ιMulti R R' O₁ O' d,
      show (⇑b' : Fin d → Ω[O'⁄R']) = fun i => KaehlerDifferential.map R R' O₁ O' (b₁ i) from funext hb'coe]

  set u : O'ˣ := Units.map (algebraMap O₁ O').toMonoidHom w₁ with hudef
  have hu : (u : O') = algebraMap O₁ O' (w₁ : O₁) := rfl
  have hcoef : algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m =
      algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ') ^ m := by
    rw [hu, ← IsScalarTower.algebraMap_apply O₁ O' F, hϖ'def, ← IsScalarTower.algebraMap_apply R R' O',
      ← IsScalarTower.algebraMap_apply R O' F, ← IsScalarTower.algebraMap_apply R O₁ F]
  have hσ' : topFormMap K K' F F d σ =
      (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ') ^ m) •
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') := by
    rw [hT, LinearMap.map_smul, hgen, hcoef]
    try rfl

  obtain ⟨hle, hiff⟩ :=
    NeronModelInfra.TopFormOrder.le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
      R' K' O' O F ϖ' hϖ' hO d b' b m u (topFormMap K K' F F d σ) hσ'

  have hρO : topFormMap R' K' O F d (exteriorPower.ιMulti O d
      (fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b₀ i)))) ≠ 0 := by
    rw [← hbcoe]
    exact (NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R' K' O F d b).1
  have hord1 := NeronModelInfra.TopFormOrder.ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
    R R' K K' O₀ O F₀ F hRR' hO₀ hO d b₀ hbc hρO a ha
  have hρ₀ := (NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R K O₀ F₀ d b₀).1
  have hord2 := (NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis R K O₀ F₀ d b₀).2 a ha hρ₀
  have hordσ : ord R' K' O d F (topFormMap K K' F F d σ) = addOrd O₀ F₀ a := by
    rw [hX]
    exact hord1.trans hord2
  have hm : m = addOrd O₀ F₀ a := le_antisymm (hordσ ▸ hle) hmin
  exact ⟨hm, hiff.mp (by rw [hordσ, hm])⟩

end S_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
end P2MW
export P2MW.S_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le (solution)
