-- Prove2me | solution 1 for GlobalTheory.zp_lift_sqZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:30.519913+00:00
-- url     : https://prove2.me/submissions/d3cd7b0a-6843-472f-a50f-4c786df0b69b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LiftZPMapAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
open Polynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
private theorem isUnit_of_isUnit_map_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (x : R') (hx : IsUnit (π x)) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y', rfl⟩ := hs y
  have h1 : x * y' - 1 ∈ RingHom.ker π := by simp [RingHom.mem_ker, hy]
  have h2 : (x * y' - 1) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  have h3 : IsUnit (x * y' - 1 + 1) := IsNilpotent.isUnit_add_one ⟨2, h2⟩
  rw [sub_add_cancel] at h3
  exact isUnit_of_mul_isUnit_left h3
private theorem ringHom_aeval_eq_aeval_apply {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm
private theorem exists_root_lift_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (f : ℤ[X]) (z : R)
    (hz : Polynomial.aeval z f = 0) (hd : IsUnit (Polynomial.aeval z (derivative f))) :
    ∃ z' : R', π z' = z ∧ Polynomial.aeval z' f = 0 := by
  obtain ⟨z₀, rfl⟩ := hs z
  have hu : IsUnit (Polynomial.aeval z₀ (derivative f)) :=
    isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ (by rwa [ringHom_aeval_eq_aeval_apply])
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h0 : π (Polynomial.aeval z₀ f) = 0 := by rwa [ringHom_aeval_eq_aeval_apply]
  have h1 : -(v * Polynomial.aeval z₀ f) ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_neg, map_mul, h0, mul_zero, neg_zero]
  have h2 : (-(v * Polynomial.aeval z₀ f)) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  refine ⟨z₀ + -(v * Polynomial.aeval z₀ f), ?_, ?_⟩
  · rw [map_add, RingHom.mem_ker.mp h1, add_zero]
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ h2, mul_neg, ← _root_.mul_assoc, hv, _root_.one_mul,
      add_neg_cancel]
private theorem isUnit_aeval_derivative_cyclotomic {R : Type} [CommRing R] (M : ℕ) (hM : M ≠ 0) (hu : IsUnit (M : R))
    (z : R) (hz : Polynomial.aeval z (cyclotomic M ℤ) = 0) :
    IsUnit (Polynomial.aeval z (derivative (cyclotomic M ℤ))) := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one M ℤ
  have h1 : z ^ M = 1 := by
    have := congrArg (Polynomial.aeval z) hg
    rw [map_mul, hz, zero_mul] at this
    simpa [sub_eq_zero] using this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one h1 hM
  have h2 := congrArg (fun q => Polynomial.aeval z (derivative q)) hg
  simp only [derivative_mul, map_add, map_mul, hz, zero_mul, add_zero, derivative_sub,
    derivative_one, sub_zero, derivative_X_pow, map_natCast, map_pow, aeval_X] at h2
  have h3 : IsUnit ((M : R) * z ^ (M - 1)) := hu.mul (hzu.pow _)
  rw [h2] at h3
  exact isUnit_of_mul_isUnit_left h3
private theorem lift_squareZero_general {B R' R : Type} [CommRing B] [CommRing R'] [CommRing R]
    (π : R' →+* R) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (β : B →+* R) (z' : R') (hz : π z' = β ζ) (hz' : Polynomial.aeval z' f = 0) :
    ∃ β' : B →+* R', π.comp β' = β := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R' := AdjoinRoot.lift (algebraMap ℤ R') z' hz'
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z' g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    refine isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ ?_
    simpa using (hS n hn).map β
  refine ⟨IsLocalization.lift hu, IsLocalization.ringHom_ext S' ?_⟩
  refine RingHom.ext fun a => ?_
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  rw [halg, hφ, hα, ringHom_aeval_eq_aeval_apply, ringHom_aeval_eq_aeval_apply, hz]
private theorem isUnit_natCast_of_mem_denominators (p M n : ℕ) (hn : n ∈ liftZP_S p) : IsUnit (n : ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]
private theorem exists_mul_eq_aeval_zeta_of_mem (p M : ℕ) (x : ℂ) (hx : x ∈ ZP p M) :
    ∃ n ∈ liftZP_S p, ∃ g : ℤ[X], x * (n : ℂ) = Polynomial.aeval (zeta M) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add, map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open Polynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution :
  (∀ (p M : ℕ) (R' R : Type) [CommRing R'] [CommRing R] (π : R' →+* R), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → M.Coprime p → M ≠ 0 →
    ∀ β : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R, ∃ β' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R', π.comp β' = β) := by
  intro p M R' R _ _ π hs hk hMp hM β
  have hprim : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M hM
  have hmin : cyclotomic M ℤ = minpoly ℤ (zeta M) :=
    cyclotomic_eq_minpoly hprim (Nat.pos_of_ne_zero hM)
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (zetaZP p M) g : ZP p M) : ℂ)
      = Polynomial.aeval (zeta M) g := fun g => ringHom_aeval_eq_aeval_apply (ZP p M).subtype g _
  have h0 : Polynomial.aeval (zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  have hβ0 : Polynomial.aeval (β (zetaZP p M)) (cyclotomic M ℤ) = 0 := by
    rw [← ringHom_aeval_eq_aeval_apply, h0, map_zero]
  have hMu : IsUnit (M : R) := by simpa using (isUnit_natCast_of_mem_denominators p M M ⟨hM, hMp⟩).map β
  obtain ⟨z', hz, hz'⟩ := exists_root_lift_of_ker_sq_eq_bot π hs hk _ _ hβ0 (isUnit_aeval_derivative_cyclotomic M hM hMu _ hβ0)
  refine lift_squareZero_general π hs hk (cyclotomic M ℤ) (zetaZP p M) (liftZP_S p) h0 ?_
    (isUnit_natCast_of_mem_denominators p M) ?_ β z' hz hz'
  · intro g hg
    rw [hmin]
    refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral (Nat.pos_of_ne_zero hM)) ?_
    rw [← hcoe, hg]
    rfl
  · intro b
    obtain ⟨n, hn, g, hg⟩ := exists_mul_eq_aeval_zeta_of_mem p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩
end GlobalTheory
