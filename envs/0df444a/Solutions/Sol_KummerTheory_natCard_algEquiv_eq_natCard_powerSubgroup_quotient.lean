-- Prove2me | solution 1 for KummerTheory.natCard_algEquiv_eq_natCard_powerSubgroup_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ecd9c115-dd2b-503b-b9c6-bf0456a7fb7d

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient

set_option autoImplicit false

theorem solution (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {n : ℕ} (hμ : (primitiveRoots n K).Nonempty)
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Nat.card (L ≃ₐ[K] L)
      = Nat.card (groupCohomology.Kummer.powerSubgroup K L n ⧸
          ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf (groupCohomology.Kummer.powerSubgroup K L n)) := by
  classical
  rw [← groupCohomology.Kummer.natCard_H1_eq_natCard_quotient (K := K) (L := L) n]
  obtain ⟨ζ, hζmem⟩ := hμ
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hζmem)
  have hζ : IsPrimitiveRoot ζ n := (mem_primitiveRoots hnpos).1 hζmem
  haveI : NeZero n := ⟨hnpos.ne'⟩
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n := hζ.map_of_injective (algebraMap K L).injective

  haveI htriv : (groupCohomology.Kummer.kummerRep K L n).IsTrivial := by
    refine ⟨fun σ => ?_⟩
    apply LinearMap.ext
    intro x
    have hξ : (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) ^ n = 1 := by
      have h := (Additive.toMul x).2
      rw [mem_rootsOfUnity] at h
      have h__af := congrArg Units.val h
      simp at h__af
      exact h__af
    obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one hξ
    have hfix : σ • (Additive.toMul x : rootsOfUnity n L) = Additive.toMul x :=
      Subtype.ext (Units.ext (by
        show σ (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L)
          = ((Additive.toMul x : rootsOfUnity n L) : Lˣ)
        rw [← hi, map_pow, AlgEquiv.commutes]))
    rw [LinearMap.id_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, hfix]
    rfl

  have h1 : Nat.card (groupCohomology.H1 (groupCohomology.Kummer.kummerRep K L n))
      = Nat.card (Additive (L ≃ₐ[K] L) →+ Additive (rootsOfUnity n L)) :=
    Nat.card_congr (groupCohomology.H1IsoOfIsTrivial
      (groupCohomology.Kummer.kummerRep K L n)).toLinearEquiv.toEquiv
  have h2 : Nat.card (Additive (L ≃ₐ[K] L) →+ Additive (rootsOfUnity n L))
      = Nat.card ((L ≃ₐ[K] L) →* rootsOfUnity n L) :=
    (Nat.card_congr (MonoidHom.toAdditive (α := L ≃ₐ[K] L) (β := rootsOfUnity n L))).symm

  have h3 : Nat.card ((L ≃ₐ[K] L) →* rootsOfUnity n L) = Nat.card ((L ≃ₐ[K] L) →* Lˣ) := by
    refine Nat.card_congr ⟨fun f => (rootsOfUnity n L).subtype.comp f,
      fun f => f.codRestrict (rootsOfUnity n L)
        (fun σ => by rw [mem_rootsOfUnity, ← map_pow, hexp, map_one]),
      fun f => by ext; rfl, fun f => by ext; rfl⟩

  have h4 : Nat.card ((L ≃ₐ[K] L) →* Lˣ) = Nat.card (L ≃ₐ[K] L) := by
    letI : CommGroup (L ≃ₐ[K] L) := { toGroup := inferInstance, mul_comm := hcomm }
    have hexp' : Monoid.exponent (L ≃ₐ[K] L) ∣ n := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    haveI : NeZero (Monoid.exponent (L ≃ₐ[K] L)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    haveI : HasEnoughRootsOfUnity L (Monoid.exponent (L ≃ₐ[K] L)) := by
      obtain ⟨d, hd⟩ := hexp'
      exact ⟨⟨algebraMap K L ζ ^ d, hζL.pow hnpos (by rw [hd, mul_comm])⟩, inferInstance⟩
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) L
    exact Nat.card_congr e.toEquiv
  exact (h1.trans (h2.trans (h3.trans h4))).symm

end S_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient
end P2MW
export P2MW.S_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient (solution)
