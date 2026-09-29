-- Prove2me | solution 1 for NeronModelInfra.TopFormOrder.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8408d168-d509-5d42-9048-82b1fc7de07b

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import Theorems.Thm_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
import Theorems.Thm_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top

set_option autoImplicit false

p2m_open "NeronModelInfra NeronModelInfra.TopFormOrder"

universe u

namespace BenchOSFC

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
    [IsScalarTower R' O F] [IsScalarTower R' K' F] (n : ℕ) (v : Fin n → Ω[O⁄R']) :
    topFormMap R' K' O F n (exteriorPower.ιMulti O n v) =
      exteriorPower.ιMulti F n (fun i => KaehlerDifferential.map R' K' O F (v i)) := by
  letI := moduleAlong O F (⋀[F]^n (Ω[F⁄K']))
  show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F n) (exteriorPower.ιMulti O n v) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end BenchOSFC

theorem solution
    (R K B B' O : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R]))
    (σ : ⋀[B']^d (Ω[B'⁄K])) (hσ : Submodule.span B' {σ} = ⊤)
    [CommRing O] [IsDomain O] [IsNoetherianRing O] [Algebra B O] [Algebra R O] [IsScalarTower R B O]
    (M : Submonoid B) [IsLocalization M O]
    (hϖ0 : algebraMap R O ϖ ≠ 0) (hϖ : (Ideal.span {algebraMap R O ϖ}).IsPrime) :
    ∃ (b' : Module.Basis (Fin d) O (Ω[O⁄R])) (w : Oˣ) (m : ℤ),
      (∀ i, b' i = KaehlerDifferential.map R R B O (β i)) ∧
      ∀ (F : Type u) [Field F] [Algebra O F] [Algebra R F] [Algebra K F] [Algebra B F] [Algebra B' F]
        [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower B O F] [IsScalarTower R B F]
        [IsScalarTower B B' F] [IsScalarTower K B' F],
        topFormMap K K B' F d σ =
          (algebraMap O F (w : O) * algebraMap O F (algebraMap R O ϖ) ^ m) •
            topFormMap R K O F d (exteriorPower.ιMulti O d b') := by
  classical

  haveI hloc : IsLocalizedModule M (KaehlerDifferential.map R R B O) :=
    KaehlerDifferential.isLocalizedModule_map R B O M
  let b' : Module.Basis (Fin d) O (Ω[O⁄R]) := β.ofIsLocalizedModule O M (KaehlerDifferential.map R R B O)
  have hb' : ∀ i, b' i = KaehlerDifferential.map R R B O (β i) := fun i =>
    β.ofIsLocalizedModule_apply O M (KaehlerDifferential.map R R B O) i

  obtain ⟨-, hlaur⟩ :=
    NeronModelInfra.TopFormOrder.span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
      R K B B' ϖ d β
  obtain ⟨u, hu⟩ := hlaur σ hσ

  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hbk⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R B ϖ)) (u : B')
  obtain ⟨⟨c, ⟨_, l, rfl⟩⟩, hcl⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R B ϖ)) ((u⁻¹ : B'ˣ) : B')
  simp only at hbk hcl

  have hbc' : algebraMap B B' (b * c) = algebraMap B B' (algebraMap R B ϖ ^ (k + l)) := by
    have hu1 : (u : B') * ((u⁻¹ : B'ˣ) : B') = 1 := Units.mul_inv u
    rw [map_mul, ← hbk, ← hcl]
    simp only [map_pow, map_mul, pow_add]
    linear_combination (algebraMap B B' (algebraMap R B ϖ) ^ k * algebraMap B B' (algebraMap R B ϖ) ^ l) * hu1
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R B ϖ)) hbc'
  simp only at hN

  set π : O := algebraMap R O ϖ with hπ
  have hπB : algebraMap B O (algebraMap R B ϖ) = π := (IsScalarTower.algebraMap_apply R B O ϖ).symm
  have hbc : algebraMap B O b * algebraMap B O c = π ^ (k + l) := by
    have := congrArg (algebraMap B O) hN
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hπB] at this
    exact mul_left_cancel₀ (pow_ne_zero N hϖ0) this
  have hb0 : algebraMap B O b ≠ 0 := by
    intro h0; apply pow_ne_zero (k + l) hϖ0; rw [← hbc, h0, zero_mul]

  let L := FractionRing O
  have hπL : algebraMap O L π ≠ 0 := fun e => hϖ0 ((IsFractionRing.injective O L) (by rw [e, map_zero]))
  have hbL : algebraMap O L (algebraMap B O b) ≠ 0 :=
    fun e => hb0 ((IsFractionRing.injective O L) (by rw [e, map_zero]))
  set a : L := algebraMap O L (algebraMap B O b) / algebraMap O L π ^ k with ha
  have ha0 : a ≠ 0 := div_ne_zero hbL (pow_ne_zero _ hπL)
  obtain ⟨n, w, hw⟩ :=
    IsNoetherianRing.exists_unit_mul_zpow_eq_of_span_singleton_isPrime π hϖ hϖ0 a
      ⟨k, algebraMap B O b, by rw [ha, div_mul_cancel₀ _ (pow_ne_zero _ hπL)]⟩
      ⟨l, algebraMap B O c, by
        rw [ha, inv_div, div_mul_eq_mul_div, ← pow_add, div_eq_iff hbL, ← map_pow, ← hbc, map_mul]
        exact mul_comm _ _⟩
      ha0

  have hO : algebraMap B O b * π ^ (-(n + k)).toNat = (w : O) * π ^ (n + k).toNat := by
    apply IsFractionRing.injective O L
    rw [map_mul, map_mul, map_pow, map_pow]
    have e1 : algebraMap O L (algebraMap B O b) = a * algebraMap O L π ^ k := by
      rw [ha, div_mul_cancel₀ _ (pow_ne_zero _ hπL)]
    rw [e1, hw]
    rw [← zpow_natCast (algebraMap O L π) k, ← zpow_natCast (algebraMap O L π) (-(n+k)).toNat,
      ← zpow_natCast (algebraMap O L π) (n+k).toNat, mul_assoc, mul_assoc, ← zpow_add₀ hπL, ← zpow_add₀ hπL]
    congr 2
    have := (n + k).toNat_sub_toNat_neg
    omega
  refine ⟨b', w, n, hb', ?_⟩

  intro F _ _ _ _ _ _ _ _ _ _ _ _
  letI := moduleAlong B' F (⋀[F]^d (Ω[F⁄K]))
  letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K]))
  letI := moduleAlong B B' (⋀[B']^d (Ω[B'⁄K]))

  have hϖF : algebraMap O F (algebraMap R O ϖ) = algebraMap K F (algebraMap R K ϖ) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hϖF0 : algebraMap O F (algebraMap R O ϖ) ≠ 0 := by
    rw [hϖF]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := K) ϖ).map (algebraMap K F)).ne_zero

  have hρ : topFormMap K K B' F d (topFormMap R K B B' d (exteriorPower.ιMulti B d β)) =
      topFormMap R K O F d (exteriorPower.ιMulti O d b') := by
    rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap, BenchOSFC.topFormMap_ιMulti,
      BenchOSFC.topFormMap_ιMulti]
    congr 1
    funext i
    rw [hb', BenchOSFC.kaehlerMap_kaehlerMap R R K B O F]

  have huF : algebraMap B' F (u : B') = algebraMap O F (w : O) * algebraMap O F (algebraMap R O ϖ) ^ n := by
    set p := algebraMap O F π with hp
    have hp0 : p ≠ 0 := hϖF0

    have e1 : algebraMap B' F (u : B') * p ^ k = algebraMap O F (algebraMap B O b) := by
      have := congrArg (algebraMap B' F) hbk
      simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply B B' F] at this
      simp only [IsScalarTower.algebraMap_apply B O F, hπB] at this
      exact this

    have e2 := congrArg (algebraMap O F) hO
    rw [map_mul, map_mul, map_pow, map_pow] at e2
    have e3 : algebraMap B' F (u : B') * p ^ (k + (-(n + k)).toNat) = algebraMap O F (w : O) * p ^ (n + k).toNat := by
      rw [pow_add, ← mul_assoc, e1, e2]
    have h3 : algebraMap B' F (u : B') =
        algebraMap O F (w : O) * p ^ (n + k).toNat * (p ^ (k + (-(n + k)).toNat))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hp0), e3]
    rw [h3, ← zpow_natCast p (n + k).toNat, ← zpow_natCast p (k + (-(n + k)).toNat), ← zpow_neg, mul_assoc,
      ← zpow_add₀ hp0]
    congr 2
    have := (n + k).toNat_sub_toNat_neg
    push_cast
    omega

  have hσ' : σ = (u : B') • topFormMap R K B B' d (exteriorPower.ιMulti B d β) := hu
  rw [hσ', LinearMap.map_smul]
  change algebraMap B' F (u : B') • topFormMap K K B' F d (topFormMap R K B B' d (exteriorPower.ιMulti B d β)) = _
  rw [hρ, huF]

end S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
end P2MW
export P2MW.S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top (solution)
