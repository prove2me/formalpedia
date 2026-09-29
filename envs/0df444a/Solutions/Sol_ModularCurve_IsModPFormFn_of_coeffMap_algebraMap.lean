-- Prove2me | solution 1 for ModularCurve.IsModPFormFn.of_coeffMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c36ef545-6d56-53a5-903c-d8651cd2c135

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open ModularCurve

noncomputable section

namespace ModPFormFnBC

section Up

variable {K₀ K : Type*} [Field K₀] [Field K] (ι : K₀ →+* K)

theorem coeffMap_mem_adjoin (y : LaurentSeries K₀) {a : LaurentSeries K₀}
    (ha : a ∈ Algebra.adjoin K₀ ({y} : Set (LaurentSeries K₀))) :
    coeffMap ι a ∈ Algebra.adjoin K ({coeffMap ι y} : Set (LaurentSeries K)) := by
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact Algebra.subset_adjoin rfl
  | algebraMap c =>

    have : coeffMap ι (algebraMap K₀ (LaurentSeries K₀) c) = algebraMap K (LaurentSeries K) (ι c) := by
      rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem isIntegral_coeffMap (y x : LaurentSeries K₀)
    (hx : IsIntegral (Algebra.adjoin K₀ ({y} : Set (LaurentSeries K₀))) x) :
    IsIntegral (Algebra.adjoin K ({coeffMap ι y} : Set (LaurentSeries K))) (coeffMap ι x) := by
  set A := Algebra.adjoin K₀ ({y} : Set (LaurentSeries K₀))
  set B := Algebra.adjoin K ({coeffMap ι y} : Set (LaurentSeries K))
  let φ : A →+* B :=
    { toFun := fun a => ⟨coeffMap ι a, coeffMap_mem_adjoin ι y a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hcomp : (algebraMap B (LaurentSeries K)).comp φ = (coeffMap ι).comp (algebraMap A (LaurentSeries K₀)) :=
    RingHom.ext fun _ => rfl
  obtain ⟨P, hPm, hPx⟩ := hx
  refine ⟨P.map φ, hPm.map φ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hPx, map_zero]

theorem isIntegral_coeffMap' (y x : LaurentSeries K₀) (y' : LaurentSeries K) (hy : coeffMap ι y = y')
    (hx : IsIntegral (Algebra.adjoin K₀ ({y} : Set (LaurentSeries K₀))) x) :
    IsIntegral (Algebra.adjoin K ({y'} : Set (LaurentSeries K))) (coeffMap ι x) := by
  subst hy; exact isIntegral_coeffMap ι y x hx

theorem up (m : ℕ) (G : LaurentSeries K₀) (hG : IsModPFormFn K₀ m G) : IsModPFormFn K m (coeffMap ι G) := by
  obtain ⟨h1, h2⟩ := hG
  have hj : coeffMap ι (jqModC K₀) = jqModC K := map_jqModC ι
  have hji : coeffMap ι (jqModC K₀)⁻¹ = (jqModC K)⁻¹ := by rw [map_inv₀, hj]
  have hc : coeffMap ι (algebraMap K₀ (LaurentSeries K₀) 1728) = algebraMap K (LaurentSeries K) 1728 := by
    rw [map_ofNat, map_ofNat, map_ofNat]
  refine ⟨?_, ?_⟩
  · have := isIntegral_coeffMap' ι (jqModC K₀) _ (jqModC K) hj h1
    simp only [map_mul, map_pow, map_sub, hj, hc] at this
    exact this
  · have := isIntegral_coeffMap' ι (jqModC K₀)⁻¹ _ (jqModC K)⁻¹ hji h2
    simp only [map_mul, map_pow, map_sub, hj, hc] at this
    exact this

end Up

section Down

variable {K₀ K : Type*} [Field K₀] [Field K] [Algebra K₀ K]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun a b h =>
  HahnSeries.ext (funext fun k => hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h]))

variable [Algebra.IsAlgebraic K₀ K]

theorem isIntegral_of_coeffMap (y x : LaurentSeries K₀)
    (hx : IsIntegral (Algebra.adjoin K ({coeffMap (algebraMap K₀ K) y} : Set (LaurentSeries K)))
      (coeffMap (algebraMap K₀ K) x)) :
    IsIntegral (Algebra.adjoin K₀ ({y} : Set (LaurentSeries K₀))) x := by
  set ι := algebraMap K₀ K with hι
  set A₀ := Algebra.adjoin K₀ ({y} : Set (LaurentSeries K₀)) with hA₀
  set A := Algebra.adjoin K ({coeffMap ι y} : Set (LaurentSeries K)) with hA

  set S : Subring (LaurentSeries K) := A₀.toSubring.map (coeffMap ι) with hS
  have hSA : S ≤ A.toSubring := by
    rintro _ ⟨a, ha, rfl⟩
    exact coeffMap_mem_adjoin ι y ha

  have hyS : coeffMap ι y ∈ S := ⟨y, Algebra.subset_adjoin rfl, rfl⟩
  have hAint : ∀ b ∈ A, IsIntegral S b := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz; subst hz
      exact isIntegral_algebraMap (x := (⟨coeffMap ι y, hyS⟩ : S))
    | algebraMap c =>
      obtain ⟨P, hPm, hPc⟩ := (Algebra.IsIntegral.isIntegral (R := K₀) c)

      have hmemK : ∀ a : K₀, algebraMap K (LaurentSeries K) (ι a) ∈ S := fun a =>
        ⟨algebraMap K₀ (LaurentSeries K₀) a, Subalgebra.algebraMap_mem _ _, by
          rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]⟩
      let ψ : K₀ →+* S :=
        { toFun := fun a => ⟨algebraMap K (LaurentSeries K) (ι a), hmemK a⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun _ _ => Subtype.ext (by simp)
          map_zero' := Subtype.ext (by simp)
          map_add' := fun _ _ => Subtype.ext (by simp) }
      have hcomp : (algebraMap S (LaurentSeries K)).comp ψ = (algebraMap K (LaurentSeries K)).comp ι :=
        RingHom.ext fun _ => rfl
      refine ⟨P.map ψ, hPm.map ψ, ?_⟩
      rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hPc, map_zero]
    | add a b _ _ ha hb => exact ha.add hb
    | mul a b _ _ ha hb => exact ha.mul hb

  letI : Algebra S A := (Subring.inclusion hSA).toAlgebra
  haveI : IsScalarTower S A (LaurentSeries K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral S A := ⟨fun b =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom S A (LaurentSeries K)) Subtype.val_injective).1
      (hAint b b.2)⟩
  have hxS : IsIntegral S (coeffMap ι x) := isIntegral_trans (R := S) (A := A) _ hx

  let φ : A₀ →+* S :=
    { toFun := fun a => ⟨coeffMap ι a, ⟨a, a.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hφ : Function.Surjective φ := by
    rintro ⟨_, a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
  have hcomp : (algebraMap S (LaurentSeries K)).comp φ = (coeffMap ι).comp (algebraMap A₀ (LaurentSeries K₀)) :=
    RingHom.ext fun _ => rfl
  obtain ⟨Q, hQm, hQx⟩ := hxS
  have hl : Q ∈ Polynomial.lifts φ := by
    rw [Polynomial.mem_lifts]; exact Polynomial.map_surjective φ hφ Q
  obtain ⟨Q₀, hQ₀, -, hQ₀m⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hQm
  refine ⟨Q₀, hQ₀m, ?_⟩
  apply coeffMap_injective ι ι.injective
  rw [Polynomial.hom_eval₂, ← hcomp, ← Polynomial.eval₂_map, hQ₀, map_zero]
  exact hQx

omit [Algebra.IsAlgebraic K₀ K] in
theorem isIntegral_of_coeffMap' [Algebra.IsAlgebraic K₀ K] (y x : LaurentSeries K₀) (y' : LaurentSeries K)
    (hy : coeffMap (algebraMap K₀ K) y = y')
    (hx : IsIntegral (Algebra.adjoin K ({y'} : Set (LaurentSeries K))) (coeffMap (algebraMap K₀ K) x)) :
    IsIntegral (Algebra.adjoin K₀ ({y} : Set (LaurentSeries K₀))) x := by
  subst hy; exact isIntegral_of_coeffMap y x hx

theorem down (m : ℕ) (G : LaurentSeries K₀) (hG : IsModPFormFn K m (coeffMap (algebraMap K₀ K) G)) :
    IsModPFormFn K₀ m G := by
  obtain ⟨h1, h2⟩ := hG
  have hj : coeffMap (algebraMap K₀ K) (jqModC K₀) = jqModC K := map_jqModC _
  have hji : coeffMap (algebraMap K₀ K) (jqModC K₀)⁻¹ = (jqModC K)⁻¹ := by rw [map_inv₀, hj]
  have hc : coeffMap (algebraMap K₀ K) (algebraMap K₀ (LaurentSeries K₀) 1728) = algebraMap K (LaurentSeries K) 1728 := by
    rw [map_ofNat, map_ofNat, map_ofNat]
  refine ⟨isIntegral_of_coeffMap' (K := K) (jqModC K₀) _ (jqModC K) hj ?_,
    isIntegral_of_coeffMap' (K := K) (jqModC K₀)⁻¹ _ (jqModC K)⁻¹ hji ?_⟩
  · simp only [map_mul, map_pow, map_sub, hj, hc]; exact h1
  · simp only [map_mul, map_pow, map_sub, hj, hc]; exact h2

end Down

end ModPFormFnBC

end

theorem solution
    {K₀ K : Type*} [Field K₀] [Field K] [Algebra K₀ K] [Algebra.IsAlgebraic K₀ K]
    (m : ℕ) (G : LaurentSeries K₀)
    (hG : IsModPFormFn K m (ModularCurve.coeffMap (algebraMap K₀ K) G)) :
    IsModPFormFn K₀ m G :=
  ModPFormFnBC.down m G hG

end S_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap
end P2MW
export P2MW.S_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap (solution)
