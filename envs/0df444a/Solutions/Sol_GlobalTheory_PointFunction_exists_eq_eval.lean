-- Prove2me | solution 1 for GlobalTheory.PointFunction.exists_eq_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:11:23.872967+00:00
-- url     : https://prove2.me/submissions/35d2451b-68db-48bd-ad22-52b8819441f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NonemptyAlgHomAlgebraicClosure
import Theorems.Thm_GlobalTheory_PointFunction_exists_common_factor
import Theorems.Thm_GlobalTheory_PointFunction_valuationSubring_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PointFunction
open IsLocalRing
namespace GlobalTheory.PointFunction
theorem _root_.solution (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h1 : ∀ (k k' : Type) [Field k] [IsAlgClosed k] [Algebra K k] [Field k'] [IsAlgClosed k']
      [Algebra K k'] (φ : A →ₐ[K] k) (χ : k →ₐ[K] k'), W k' (χ.comp φ) = χ (W k φ))
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v) :
    ∃ r : A, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : A →ₐ[K] k),
      W k φ = φ r := by
  let L := FractionRing A
  let Ω := AlgebraicClosure L
  let ι : A →ₐ[K] Ω := IsScalarTower.toAlgHom K A Ω
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsGalois L Ω := inferInstance
  have hinj : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A L Ω]
    exact (algebraMap L Ω).injective.comp (IsFractionRing.injective A L)
  obtain ⟨x, hx⟩ : W Ω ι ∈ Set.range (algebraMap L Ω) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (W Ω ι)).2 fun σ => ?_
    have e : ((σ : Ω →ₐ[L] Ω).restrictScalars K).comp ι = ι := by
      ext a
      exact ((σ : Ω →ₐ[L] Ω).restrictScalars A).commutes a
    have := h1 Ω Ω ι ((σ : Ω →ₐ[L] Ω).restrictScalars K)
    rw [e] at this
    exact this.symm
  have hint : IsIntegral A (W Ω ι) := by
    by_contra hn
    haveI : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
      inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
    obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure A Ω).toSubring) (x := W Ω ι) hn
    exact hxV (valuationSubring_step K A W h2 Ω ι V
      fun a => hV ((integralClosure A Ω).algebraMap_mem a)).1
  have hint' : IsIntegral A x := by
    rw [← hx] at hint
    exact (isIntegral_algebraMap_iff (algebraMap L Ω).injective).1 hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
  have hrw : ι r = W Ω ι := by
    rw [← hx, ← hr]; exact IsScalarTower.algebraMap_apply A L Ω r
  refine ⟨r, fun k _ _ _ φ => ?_⟩
  let q : Ideal A := RingHom.ker φ
  haveI : q.IsPrime := RingHom.ker_isPrime φ
  let f : Localization.AtPrime q →+* Ω := IsLocalization.lift (M := q.primeCompl)
    (g := algebraMap A Ω) fun y => by
      refine isUnit_iff_ne_zero.2 fun h0 => y.2 ?_
      have : (y : A) = 0 := hinj (by rw [h0, map_zero])
      rw [this]; exact q.zero_mem
  have hf : ∀ a, f (algebraMap A _ a) = ι a := fun a => IsLocalization.lift_eq _ a
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hmem : ∀ a, ι a ∈ V := fun a => hf a ▸ hV _
  obtain ⟨-, alg, ψ, hψ, hψr⟩ := valuationSubring_step K A W h2 Ω ι V hmem
  have hψq : ∀ a, ψ a = 0 ↔ a ∈ q := fun a => by
    rw [hψ, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      ← isUnit_map_iff (f.codRestrict V.toSubring hV)]
    have : f.codRestrict V.toSubring hV (algebraMap A _ a) = ⟨ι a, hmem a⟩ := Subtype.ext (hf a)
    rw [this]
  obtain ⟨χ, hχ⟩ := exists_common_factor K A q k φ fun a => Iff.rfl
  obtain ⟨χ', hχ'⟩ := exists_common_factor K A q _ ψ hψq
  have e := hψr r hrw
  rw [← hχ', h1] at e
  rw [← hχ, h1, χ'.toRingHom.injective e]
  rfl
end GlobalTheory.PointFunction
