-- Prove2me | solution 1 for GlobalTheory.conductor_prod_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:43.98607+00:00
-- url     : https://prove2.me/submissions/17c631c6-f748-4331-b34a-c6770e075d0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S]
    (e : S ≃+* R × S') (d : S)
    (hd : ∀ c : FractionRing S, IsIntegral S c →
      ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) :
    ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  intro c hc
  let g : S →+* FractionRing R × FractionRing S' :=
    (RingHom.prodMap (algebraMap R (FractionRing R)) (algebraMap S' (FractionRing S'))).comp
      e.toRingHom
  have hgx : ∀ x : S, g x = (algebraMap R (FractionRing R) (e x).1,
      algebraMap S' (FractionRing S') (e x).2) := fun x => rfl
  have hg : ∀ y : nonZeroDivisors S, IsUnit (g y) := by
    intro y
    rw [hgx, Prod.isUnit_iff]
    have h1 : (e y).1 ∈ nonZeroDivisors R := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (z, 0) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).1) this
      simpa using this
    have h2 : (e y).2 ∈ nonZeroDivisors S' := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (0, z) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).2) this
      simpa using this
    exact ⟨IsLocalization.map_units (FractionRing R) (⟨_, h1⟩ : nonZeroDivisors R),
      IsLocalization.map_units (FractionRing S') (⟨_, h2⟩ : nonZeroDivisors S')⟩
  let Θ : FractionRing S →+* FractionRing R × FractionRing S' := IsLocalization.lift hg
  have hΘ : ∀ x : S, Θ (algebraMap S (FractionRing S) x) = g x := fun x =>
    IsLocalization.lift_eq hg x
  have hΘinj : Function.Injective Θ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [(IsFractionRing.injective S (FractionRing S)) h]
    · intro h
      have h' : e x = e y := by
        rw [hgx, hgx] at h
        ext
        · exact IsFractionRing.injective R (FractionRing R) (congrArg Prod.fst h)
        · exact IsFractionRing.injective S' (FractionRing S') (congrArg Prod.snd h)
      rw [e.injective h']

  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
  have hb' : e.symm ((b : R), (1 : S')) ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have hz' := congrArg e hz
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at hz'
    have h1 : (e z).1 * b = 0 := congrArg Prod.fst hz'
    have h2 : (e z).2 * 1 = 0 := congrArg Prod.snd hz'
    rw [mul_right_mem_nonZeroDivisors_eq_zero_iff b.2] at h1
    rw [mul_one] at h2
    apply e.injective
    rw [map_zero]
    ext <;> simp [h1, h2]
  set c := IsLocalization.mk' (FractionRing R) a b with hcdef
  let b' : nonZeroDivisors S := ⟨_, hb'⟩
  let c' : FractionRing S := IsLocalization.mk' (FractionRing S) (e.symm (a, 0)) b'
  have hΘc : Θ c' = (c, 0) := by
    have hs := IsLocalization.mk'_spec (FractionRing S) (e.symm (a, 0)) b'
    have hs2 := congrArg Θ hs
    rw [map_mul, hΘ, hΘ] at hs2
    have hu := hg b'
    have hcs := IsLocalization.mk'_spec (FractionRing R) a b
    rw [← hu.mul_left_inj, hs2]
    rw [hgx, hgx]
    simp only [b', RingEquiv.apply_symm_apply, Prod.mk_mul_mk, map_zero, map_one, mul_one,
      zero_mul]
    rw [hcs]
  have hf : Function.Surjective ((RingHom.fst R S').comp e.toRingHom) := by
    intro r
    exact ⟨e.symm (r, 0), by simp⟩
  have hc' : IsIntegral S c' := by
    obtain ⟨p, hpm, hp⟩ := hc
    obtain ⟨q, hqmap, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
      (f := (RingHom.fst R S').comp e.toRingHom) (p := p)
      ((lifts_iff_coeff_lifts p).mpr (fun n => hf _)) hpm
    refine ⟨X * q, monic_X.mul hqm, ?_⟩
    apply hΘinj
    rw [Polynomial.hom_eval₂, map_zero, hΘc, eval₂_mul, eval₂_X]
    have hfst : (RingHom.fst (FractionRing R) (FractionRing S')).comp
        (Θ.comp (algebraMap S (FractionRing S))) =
        (algebraMap R (FractionRing R)).comp ((RingHom.fst R S').comp e.toRingHom) := by
      ext x
      simp [hΘ, hgx]
    have h1 : (eval₂ (Θ.comp (algebraMap S (FractionRing S))) (c, 0) q).1 = 0 := by
      have := Polynomial.hom_eval₂ q (Θ.comp (algebraMap S (FractionRing S)))
        (RingHom.fst (FractionRing R) (FractionRing S')) (c, 0)
      simp only [RingHom.coe_fst] at this
      rw [this, hfst, ← eval₂_map, hqmap]
      exact hp
    ext
    · simp [h1]
    · simp
  obtain ⟨s, hs⟩ := hd c' hc'
  refine ⟨(e s).1, ?_⟩
  have h := congrArg (fun z => (Θ z).1) hs
  simp only [map_mul, hΘ, hΘc, hgx, Prod.fst_mul] at h
  exact h
end GlobalTheory
