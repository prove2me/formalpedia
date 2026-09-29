-- Prove2me | solution 1 for NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1f056c71-5376-5cbc-b9df-3c2f08052790

import Mathlib
import Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

namespace P2mCycloChebPack

open NumberField

set_option linter.unusedSectionVars false

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem under_int_eq_span_of_natCast_mem {p : ℕ} (hp : p.Prime) (Q : Ideal (𝓞 L)) (hQ : Q ≠ ⊤)
    (hpQ : (p : 𝓞 L) ∈ Q) : Q.under ℤ = Ideal.span {(p : ℤ)} := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp))
      (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp.ne_zero)
  refine (hmax.eq_of_le ?_ ?_).symm
  · intro h
    apply hQ
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ Q.under ℤ := by rw [h]; exact Submodule.mem_top
    rw [Ideal.under_def, Ideal.mem_comap, map_one] at h1
    exact h1
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap,
      map_natCast]
    exact hpQ

theorem card_int_quot_span (p : ℕ) : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

variable (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]

theorem algEquiv_eq_of_apply_eq {ζ : L} (hζ : IsPrimitiveRoot ζ m) {σ τ : L ≃ₐ[K] L}
    (h : σ ζ = τ ζ) : σ = τ := by
  apply hζ.autToPow_injective K
  have hσ := hζ.autToPow_spec K σ
  have hτ := hζ.autToPow_spec K τ
  have hpow : ζ ^ ((hζ.autToPow K σ : ZMod m)).val = ζ ^ ((hζ.autToPow K τ : ZMod m)).val := by
    rw [hσ, hτ, h]
  have hval := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow
  exact Units.ext (ZMod.val_injective m hval)

theorem exists_isArithFrobAt_int [IsGalois K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (τ : L ≃ₐ[K] L) {p : ℕ} (hp : p.Prime) (v : Ideal (𝓞 K)) [hv : v.IsMaximal]
    (hvp : Ideal.absNorm v = p) (hτ : τ ζ = ζ ^ p) :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ (p : 𝓞 L) ∈ Q ∧ IsArithFrobAt ℤ τ Q := by
  classical

  have hcop : p.Coprime m := by
    have hprim : IsPrimitiveRoot (ζ ^ p) m := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    exact (hζ.pow_iff_coprime (NeZero.pos m) p).mp hprim

  have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) ≤ v := by
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := by
      intro x y hxy
      have h' : algebraMap (𝓞 K) L x = algebraMap (𝓞 K) L y := by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
          IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, hxy]
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K L, IsScalarTower.algebraMap_apply (𝓞 K) K L] at h'
      exact RingOfIntegers.coe_injective ((algebraMap K L).injective h')
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨Q, hQmax, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v hker
  haveI : Q.IsMaximal := hQmax
  have hunder : Q.under (𝓞 K) = v := hQv

  have hpv : (p : 𝓞 K) ∈ v := by rw [← hvp]; exact Ideal.absNorm_mem v
  have hpQ : (p : 𝓞 L) ∈ Q := by
    have : algebraMap (𝓞 K) (𝓞 L) (p : 𝓞 K) ∈ Q := by
      rw [← Ideal.mem_comap]
      show (p : 𝓞 K) ∈ Q.under (𝓞 K)
      rw [hunder]
      exact hpv
    rwa [map_natCast] at this

  have hcardK : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = p := by
    rw [hunder, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hvp]
  have hQtop : Q ≠ ⊤ := hQmax.ne_top
  have hunderZ : Q.under ℤ = Ideal.span {(p : ℤ)} := under_int_eq_span_of_natCast_mem hp Q hQtop hpQ
  have hcardZ : Nat.card (ℤ ⧸ Q.under ℤ) = p := by rw [hunderZ, card_int_quot_span]

  have hmQ : (m : 𝓞 L) ∉ Q := by
    intro hm
    have hmZ : (m : ℤ) ∈ Q.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hm
    rw [hunderZ, Ideal.mem_span_singleton] at hmZ
    have hpm : p ∣ m := by exact_mod_cast hmZ
    have hp1 : p = 1 := Nat.Coprime.eq_one_of_dvd hcop hpm
    exact hp.one_lt.ne' hp1

  haveI : Finite (𝓞 L ⧸ Q) := Q.finiteQuotientOfFreeOfNeBot (by
    rintro rfl
    have : (p : 𝓞 L) = 0 := (Ideal.mem_bot).mp hpQ
    exact hp.ne_zero (by exact_mod_cast this))
  set φ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q with hφdef
  have hφ : IsArithFrobAt (𝓞 K) φ Q := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q

  set ζ' : 𝓞 L := hζ.toInteger with hζ'def
  have hζ'pow : ζ' ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hφζ' : φ • ζ' = ζ' ^ p := by
    have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hφ hζ'pow hmQ
    rw [hcardK] at h
    exact h
  have hφζ : φ ζ = ζ ^ p := by
    have h := congrArg (fun x : 𝓞 L => (x : L)) hφζ'
    simp only [map_pow] at h
    simp [hζ'def, hζ.coe_toInteger] at h
    exact h

  have hφτ : φ = τ := algEquiv_eq_of_apply_eq m hζ (hφζ.trans hτ.symm)
  refine ⟨Q, hQmax, hpQ, ?_⟩
  intro x
  have hx := hφ x
  rw [hcardK, hφτ] at hx
  rw [hcardZ]
  exact hx

end P2mCycloChebPack

open NumberField in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ τ P := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m)
    (NeZero.ne m)
  obtain ⟨p, hp, hpS, v, hv, hvp, hτ⟩ :=
    NumberField.exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension K L m hζ τ S
  haveI := hv
  obtain ⟨Q, hQ, hpQ, hfrob⟩ := P2mCycloChebPack.exists_isArithFrobAt_int m hζ τ hp v hvp hτ
  exact ⟨p, hp, hpS, Q, hQ, hpQ, hfrob⟩

end S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
end P2MW
export P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (solution)
