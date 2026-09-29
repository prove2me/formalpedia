-- Prove2me | solution 1 for IsLocalRing.perfectField_residueField_of_isAlgebraic_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3502a1fc-7ce0-5d30-8503-bfc3a2af6c56

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat

set_option autoImplicit false

open Polynomial in
theorem solution
    (L₀ : Type) [Field L₀] [CharZero L₀] [Algebra.IsAlgebraic ℚ L₀]
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsLocalRing A₀] [Algebra A₀ L₀]
    (hinj : Function.Injective (algebraMap A₀ L₀))
    (p : ℕ) [Fact p.Prime] (hp : (p : A₀) ∈ IsLocalRing.maximalIdeal A₀) :
    PerfectField (IsLocalRing.ResidueField A₀) := by
  classical
  have hpκ : ((p : ℕ) : IsLocalRing.ResidueField A₀) = 0 := by
    have : IsLocalRing.residue A₀ (p : A₀) = 0 := by
      rwa [← RingHom.mem_ker, IsLocalRing.ker_residue]
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField A₀) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpκ
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField A₀) := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A₀) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have haL : IsAlgebraic ℚ (algebraMap A₀ L₀ a) := Algebra.IsAlgebraic.isAlgebraic _
    have haZ : IsAlgebraic ℤ (algebraMap A₀ L₀ a) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L₀).mpr haL
    obtain ⟨f, hf0, hf⟩ := haZ
    set g : ℤ[X] := f.primPart with hg
    have hgprim : g.IsPrimitive := f.isPrimitive_primPart

    have heval : ∀ {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (s : S) (r : ℤ[X]),
        φ (aeval s r) = aeval (φ s) r := by
      intro S T _ _ φ s r
      rw [aeval_def, aeval_def, hom_eval₂]
      congr 1
      ext n
      simp
    have hgL : aeval (algebraMap A₀ L₀ a) g = 0 := by
      have h1 : aeval (algebraMap A₀ L₀ a) f = algebraMap ℤ L₀ f.content * aeval (algebraMap A₀ L₀ a) g := by
        conv_lhs => rw [f.eq_C_content_mul_primPart]
        rw [map_mul, aeval_C]
      rw [hf] at h1
      have hc : (algebraMap ℤ L₀ f.content) ≠ 0 := by
        rw [ne_eq, map_eq_zero_iff _ (algebraMap ℤ L₀).injective_int, content_eq_zero_iff]
        exact hf0
      exact (mul_eq_zero.mp h1.symm).resolve_left hc
    have hgA : aeval a g = 0 := by
      apply hinj
      rw [heval, hgL, map_zero]
    have hgκ : aeval (IsLocalRing.residue A₀ a) g = 0 := by
      have h := heval (IsLocalRing.residue A₀) a g
      rw [hgA, map_zero] at h
      exact h.symm

    have hgp : g.map (Int.castRingHom (ZMod p)) ≠ 0 := by
      intro h0
      have hdvd : C (p : ℤ) ∣ g := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have : ((g.coeff i : ℤ) : ZMod p) = 0 := by
          have := congrArg (fun r => r.coeff i) h0
          simpa [coeff_map] using this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
      have hu := (isPrimitive_iff_isUnit_of_C_dvd.mp hgprim) (p : ℤ) hdvd
      rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
      exact (Fact.out : p.Prime).one_lt.ne' hu
    refine ⟨g.map (Int.castRingHom (ZMod p)), hgp, ?_⟩
    rw [aeval_def, eval₂_map,
      RingHom.ext_int ((algebraMap (ZMod p) (IsLocalRing.ResidueField A₀)).comp (Int.castRingHom (ZMod p)))
        (algebraMap ℤ (IsLocalRing.ResidueField A₀)), ← aeval_def]
    exact hgκ
  exact Algebra.IsAlgebraic.perfectField (K := ZMod p)

end S_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat
end P2MW
export P2MW.S_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat (solution)
