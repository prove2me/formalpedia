-- Prove2me | solution 1 for GlobalTheory.exists_ringEquiv_extending_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:06.579863+00:00
-- url     : https://prove2.me/submissions/f0ca1e00-8c5c-42fc-9104-f29c97a16d37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingEquivExtendingOfKerLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) →
      ∀ (R : Subring k) (J : Type) (α β : J → k),
        (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) →
        ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  intro k _ _ hroot R J α β hker
  let eα : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval α
  let eβ : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval β
  let S : Subalgebra R k := eα.range
  have hle : ∀ p ∈ RingHom.ker eα.rangeRestrict, eβ p = 0 := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    apply hker
    have := congrArg Subtype.val hp
    simpa using this
  let ψ0 : S →ₐ[R] k := (Ideal.Quotient.liftₐ (RingHom.ker eα.rangeRestrict) eβ hle).comp
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm.toAlgHom
  have hψ0 : ∀ p, ψ0 (eα.rangeRestrict p) = eβ p := by
    intro p
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm
        (eα.rangeRestrict p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    simp only [ψ0, AlgHom.comp_apply]
    erw [h1]
    rfl
  let ψ : S →+* FieldCopy k := ψ0.toRingHom
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    by_contra hne
    have hne' : (s : k) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨n, hn, hsn⟩ := hroot _ hne'
    have hsn' : s ^ n = 1 := Subtype.ext (by simpa using hsn)
    have : ψ s ^ n = 1 := by rw [← map_pow, hsn', map_one]
    rw [hs, zero_pow (by omega)] at this
    exact zero_ne_one this
  letI : Algebra S (FieldCopy k) := ψ.toAlgebra
  haveI : Module.IsTorsionFree S (FieldCopy k) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left
      exact hψinj (h.trans (map_zero ψ).symm)
    · exact Or.inr h
  haveI : Algebra.IsIntegral S k := by
    constructor
    intro x
    by_cases hx : x = 0
    · rw [hx]; exact isIntegral_zero
    · obtain ⟨n, hn, hxn⟩ := hroot x hx
      refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
      simp [hxn]
  let θ' : k →ₐ[S] FieldCopy k := IsAlgClosed.lift
  let θ : k →+* k := θ'.toRingHom
  have hθS : ∀ s : S, θ (s : k) = ψ0 s := by
    intro s
    have := θ'.commutes s
    exact this
  have hθinj : Function.Injective θ := θ.injective
  have hθsurj : Function.Surjective θ := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy, map_zero]⟩
    obtain ⟨n, hn, hyn⟩ := hroot y hy
    let T := Polynomial.nthRootsFinset n (1 : k)
    have hmem : ∀ x : k, x ∈ T ↔ x ^ n = 1 := fun x => Polynomial.mem_nthRootsFinset (by omega) 1
    let f : T → T := fun t => ⟨θ t, (hmem _).2 (by rw [← map_pow, (hmem _).1 t.2, map_one])⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (hθinj (congrArg Subtype.val hab))
    obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.1 hf ⟨y, (hmem y).2 hyn⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  refine ⟨RingEquiv.ofBijective θ ⟨hθinj, hθsurj⟩, ?_, ?_⟩
  · intro r hr
    have hrS : (r : k) ∈ S := ⟨MvPolynomial.C ⟨r, hr⟩, by simp [eα]; rfl⟩
    show θ r = r
    have h2 : (⟨r, hrS⟩ : S) = eα.rangeRestrict (MvPolynomial.C ⟨r, hr⟩) :=
      Subtype.ext (by simp [eα]; rfl)
    rw [show r = ((⟨r, hrS⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]
  · intro j
    show θ (α j) = β j
    have h2 : (⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) = eα.rangeRestrict (MvPolynomial.X j) :=
      Subtype.ext (by simp [eα])
    rw [show α j = ((⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]
end GlobalTheory
