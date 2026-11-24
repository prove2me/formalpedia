-- Prove2me | solution 1 for GlobalTheory.CompleteDiscreteValuationRing.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:09.476311+00:00
-- url     : https://prove2.me/submissions/cd3248b4-28f8-4663-98c0-73406ab0c7d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing
namespace GlobalTheory.CompleteDiscreteValuationRing
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A) (g : R →+* A) (t : A),
      Function.Injective g ∧ t ≠ 0 ∧ ¬ IsUnit t ∧ (∀ r ∈ maximalIdeal R, t ∣ g r) ∧
      ∀ i, Associated (g (a i)) (t ^ k i) := by
  classical
  have := Fintype.ofFinite I
  let K := FractionRing V
  let ι : V →+* K := algebraMap V K
  have hι : Function.Injective ι := IsFractionRing.injective V K
  have hψa : ∀ i, ψ (a i) ≠ 0 := fun i => (h i).ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero)
  have ha : ∀ i, a i ≠ 0 := fun i e => hψa i (by rw [e, map_zero])
  let d : Polynomial R := Polynomial.X * Polynomial.C (∏ i, a i)
  have hd : d ≠ 0 := mul_ne_zero Polynomial.X_ne_zero
    (Polynomial.C_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ha i))
  have hle : Submonoid.powers d ≤ nonZeroDivisors (Polynomial R) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let C := Localization.Away d
  have hCd : IsDomain C := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (algebraMap (Polynomial R) C) := IsLocalization.injective C hle
  let e : Polynomial R →+* K := Polynomial.eval₂RingHom (ι.comp ψ) (ι ϖ)
  have hϖK : ι ϖ ≠ 0 := (map_ne_zero_iff ι hι).2 hϖ.ne_zero
  have hed : IsUnit (e d) := by
    refine Ne.isUnit ?_
    simp only [e, d, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C,
      RingHom.comp_apply]
    refine mul_ne_zero hϖK ((map_ne_zero_iff ι hι).2 ?_)
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hψa i
  let φ : C →+* K := IsLocalization.Away.lift d hed
  let τ : C := algebraMap (Polynomial R) C Polynomial.X
  have hRC : ∀ r : R, algebraMap R C r = algebraMap (Polynomial R) C (Polynomial.C r) :=
    fun r => by rw [IsScalarTower.algebraMap_apply R (Polynomial R) C]; rfl
  have hφτ : φ τ = ι ϖ := by
    simp only [φ, τ, IsLocalization.Away.lift_eq, e, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
  have hφr : ∀ r : R, φ (algebraMap R C r) = ι (ψ r) := fun r => by
    simp only [hRC, φ, IsLocalization.Away.lift_eq, e, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, RingHom.comp_apply]
  have hud : IsUnit (algebraMap (Polynomial R) C d) := IsLocalization.Away.algebraMap_isUnit d
  have huτ : IsUnit τ := isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right _ _)) hud
  have hua : ∀ i, IsUnit (algebraMap R C (a i)) := fun i => by
    rw [hRC]
    refine isUnit_of_dvd_unit (map_dvd _ (Dvd.dvd.mul_left (map_dvd _ ?_) _)) hud
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

  have hdiv : ∀ (x y : C) (x' y' : V), IsUnit y → φ x = ι x' → φ y = ι y' → y' ∣ x' →
      ∃ z : C, x = y * z ∧ φ z ∈ ι.range := by
    rintro x y _ y' hy hx' hy' ⟨c, rfl⟩
    obtain ⟨z, rfl⟩ := hy.dvd (a := x)
    refine ⟨z, rfl, c, mul_left_cancel₀ (hy.map φ).ne_zero ?_⟩
    rw [← map_mul, hx', hy', map_mul]
  have hτk : ∀ i, φ (τ ^ k i) = ι (ϖ ^ k i) := fun i => by rw [map_pow, map_pow, hφτ]
  choose u hu hu' using fun i => hdiv (algebraMap R C (a i)) (τ ^ k i) _ _ (huτ.pow _) (hφr _)
    (hτk i) (h i).symm.dvd
  choose w hw hw' using fun i => hdiv (τ ^ k i) (algebraMap R C (a i)) _ _ (hua i) (hτk i)
    (hφr _) (h i).dvd
  obtain ⟨s, hs⟩ := (maximalIdeal R).fg_of_isNoetherianRing
  have hsd : ∀ y : s, ϖ ∣ ψ y := fun y => by
    have h1 : (y : R) ∈ maximalIdeal R := hs ▸ Ideal.subset_span y.2
    have h2 : ψ y ∈ maximalIdeal V := fun h => h1 (hψ.1 _ h)
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h2
  choose z hz hz' using fun y : s => hdiv (algebraMap R C y) τ _ _ huτ (hφr _) hφτ (hsd y)
  let S : Set C := {τ} ∪ Set.range u ∪ Set.range w ∪ Set.range z
  have hS : S.Finite :=
    (((Set.finite_singleton _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)
  let A := Algebra.adjoin R S
  have hft : Algebra.FiniteType R A := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact Subalgebra.fg_def.2 ⟨S, hS, rfl⟩
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hA : ∀ x ∈ A, φ x ∈ ι.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ((rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
      exacts [⟨_, hφτ.symm⟩, hu' i, hw' i, hz' i]
    | algebraMap r => exact ⟨_, (hφr r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have mτ : τ ∈ A := Algebra.subset_adjoin (Or.inl (Or.inl (Or.inl rfl)))
  have mu : ∀ i, u i ∈ A := fun i => Algebra.subset_adjoin (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
  have mw : ∀ i, w i ∈ A := fun i => Algebra.subset_adjoin (Or.inl (Or.inr ⟨i, rfl⟩))
  have mz : ∀ i, z i ∈ A := fun i => Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  refine ⟨A, inferInstance, inferInstance, hN, algebraMap R A, ⟨τ, mτ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : algebraMap R C x = algebraMap R C y := congrArg Subtype.val hxy
    rw [hRC, hRC] at h1
    exact Polynomial.C_injective (hinj h1)
  · exact fun h0 => huτ.ne_zero (congrArg Subtype.val h0)
  · intro h0
    obtain ⟨x, hx⟩ := isUnit_iff_exists_inv.1 h0
    have h1 : τ * (x : C) = 1 := congrArg Subtype.val hx
    obtain ⟨v, hv⟩ := hA x x.2
    have h2 := congrArg φ h1
    rw [map_mul, map_one, hφτ, ← hv, ← map_mul, ← map_one ι] at h2
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (hι h2))
  · intro r hr
    rw [← Ideal.mem_span_singleton, ← Ideal.mem_comap]
    rw [← hs] at hr
    refine Ideal.span_le.2 (fun y hy => ?_) hr
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ⟨⟨_, mz ⟨y, hy⟩⟩, Subtype.ext (hz ⟨y, hy⟩)⟩)
  · intro i
    exact associated_of_dvd_dvd ⟨⟨_, mw i⟩, Subtype.ext (hw i)⟩ ⟨⟨_, mu i⟩, Subtype.ext (hu i)⟩
end GlobalTheory.CompleteDiscreteValuationRing
