-- Prove2me | solution 1 for ModularCurve.coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6d1d5283-c44d-57b2-8443-bf33551064d6

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    (hF : ModularCurve.jqModC L ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (hβdef : ModularCurve.HeckeBetaOneDefined N ℓ)
    (hdeg : AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L N ℓ) = ℓ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ)
    (y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ N (N * ℓ)))) :
    letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeBetaOneBar L N ℓ)
    ((ModularCurve.heckeBetaOneBar L N ℓ
        (Algebra.norm (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) y) :
          ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ N (N * ℓ)))) : LaurentSeries L) =
      ∏ i : Fin ℓ, ModularCurve.qTwist (ζ ^ (i : ℕ)) ((y : ↥(ModularCurve.laurentBaseChange L
        (ModularCurve.x1x0FunctionFieldC ℚ N (N * ℓ)))) : LaurentSeries L) := by
  classical

  let F : IntermediateField L (LaurentSeries L) := ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)
  let F' : IntermediateField L (LaurentSeries L) :=
    ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ N (N * ℓ))
  let β : ↥F →ₐ[L] ↥F' := ModularCurve.heckeBetaOneBar L N ℓ
  letI instAlg : Algebra ↥F ↥F' := AlgebraicCurve.algebraAlong β
  letI instMod : Module ↥F ↥F' := Algebra.toModule
  haveI : IsScalarTower L ↥F ↥F' := AlgebraicCurve.isScalarTower_along β
  change ((β (Algebra.norm ↥F y) : ↥F') : LaurentSeries L) =
    ∏ i : Fin ℓ, ModularCurve.qTwist (ζ ^ (i : ℕ)) ((y : ↥F') : LaurentSeries L)
  have hβcoe : ∀ x : ↥F, ((β x : ↥F') : LaurentSeries L) = ModularCurve.qExpand L ℓ (x : LaurentSeries L) :=
    fun x => ModularCurve.coe_heckeBetaOneBar N ℓ hβdef x
  have halg : ∀ x : ↥F, algebraMap ↥F ↥F' x = β x := fun _ => rfl

  haveI : FiniteDimensional ↥F ↥F' := Module.finite_of_finrank_pos (by
    change 0 < AlgebraicCurve.finrankAlong L β
    rw [hdeg]
    exact Nat.pos_of_ne_zero (NeZero.ne ℓ))
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : PerfectField ↥F := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic ↥F ↥F' := Algebra.IsAlgebraic.of_finite ↥F ↥F'
  haveI : Algebra.IsSeparable ↥F ↥F' := Algebra.IsAlgebraic.isSeparable_of_perfectField

  let Ω := AlgebraicClosure (LaurentSeries L)
  let ι : LaurentSeries L →+* Ω := algebraMap (LaurentSeries L) Ω
  have hι : Function.Injective ι := (algebraMap (LaurentSeries L) Ω).injective
  letI algFΩ : Algebra ↥F Ω :=
    (ι.comp ((algebraMap ↥F' (LaurentSeries L)).comp (β : ↥F →ₐ[L] ↥F').toRingHom)).toAlgebra
  have halgΩ : ∀ x : ↥F, algebraMap ↥F Ω x = ι ((β x : ↥F') : LaurentSeries L) := fun _ => rfl

  have hζℓ : ζ ^ ℓ = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)

  let σ : Fin ℓ → (↥F' →ₐ[↥F] Ω) := fun i =>
    { toFun := fun z => ι (ModularCurve.qTwist (ζ ^ (i : ℕ)) (z : LaurentSeries L))
      map_one' := by simp
      map_mul' := fun a b => by simp
      map_zero' := by simp
      map_add' := fun a b => by simp
      commutes' := fun x => by
        have hpow : (ζ ^ (i : ℕ)) ^ (ℓ : ℤ) = 1 := by
          rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, hζℓ, one_pow]
        rw [halgΩ, halg, hβcoe, ModularCurve.qTwist_qExpand, hpow, ModularCurve.qTwist_one_apply] }
  have hσ : ∀ i (z : ↥F'), σ i z = ι (ModularCurve.qTwist (ζ ^ (i : ℕ)) (z : LaurentSeries L)) :=
    fun _ _ => rfl

  let t : ↥F' := ModularCurve.heckeAlphaOneBar L N ℓ ⟨ModularCurve.jqModC L, hF⟩
  have ht : (t : LaurentSeries L) = ModularCurve.jqModC L := ModularCurve.coe_heckeAlphaOneBar N ℓ _
  have hjcoeff : (ModularCurve.jqModC L).coeff (-1) = 1 := by
    have h : (HahnSeries.single (-1 : ℤ) (1 : L) *
        HahnSeries.ofPowerSeries ℤ L (ModularCurve.jNum.map (Int.castRingHom L))).coeff (0 + (-1)) =
        1 * (HahnSeries.ofPowerSeries ℤ L (ModularCurve.jNum.map (Int.castRingHom L))).coeff 0 :=
      HahnSeries.coeff_single_mul_add
    rw [zero_add, one_mul] at h
    rw [ModularCurve.jqModC, h]
    have h0 : (HahnSeries.ofPowerSeries ℤ L (ModularCurve.jNum.map (Int.castRingHom L))).coeff ((0 : ℕ) : ℤ) =
        PowerSeries.coeff 0 (ModularCurve.jNum.map (Int.castRingHom L)) :=
      HahnSeries.ofPowerSeries_apply_coeff _ 0
    rw [Nat.cast_zero] at h0
    rw [h0, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, ModularCurve.constantCoeff_jNum, map_one]
  have hinj : Function.Injective σ := by
    intro i j h
    have h1 : σ i t = σ j t := by rw [h]
    rw [hσ, hσ, ht] at h1
    have h2 := congrArg (fun f : LaurentSeries L => f.coeff (-1)) (hι h1)
    simp only [ModularCurve.qTwist_coeff, hjcoeff, mul_one] at h2

    have h3 : (ζ ^ (i : ℕ)) = ζ ^ (j : ℕ) := by
      have := Units.val_injective (by simpa using h2 : (((ζ ^ (i : ℕ)) ^ (-1 : ℤ) : Lˣ) : L) = (((ζ ^ (j : ℕ)) ^ (-1 : ℤ) : Lˣ) : L))
      simpa using this
    have h4 : ((ζ : L)) ^ (i : ℕ) = (ζ : L) ^ (j : ℕ) := by
      have := congrArg Units.val h3
      simpa [Units.val_pow_eq_pow_val] using this
    exact Fin.ext (hζ.pow_inj i.2 j.2 h4)

  have hcard : Fintype.card (↥F' →ₐ[↥F] Ω) = Fintype.card (Fin ℓ) := by
    rw [AlgHom.card ↥F ↥F' Ω, Fintype.card_fin]
    exact hdeg
  let e : Fin ℓ ≃ (↥F' →ₐ[↥F] Ω) :=
    Equiv.ofBijective σ ((Fintype.bijective_iff_injective_and_card σ).2 ⟨hinj, hcard.symm⟩)

  have key := Algebra.norm_eq_prod_embeddings ↥F Ω y
  apply hι
  rw [← halgΩ, key, map_prod, ← e.prod_comp]
  rfl

end S_ModularCurve_coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq
end P2MW
export P2MW.S_ModularCurve_coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq (solution)
