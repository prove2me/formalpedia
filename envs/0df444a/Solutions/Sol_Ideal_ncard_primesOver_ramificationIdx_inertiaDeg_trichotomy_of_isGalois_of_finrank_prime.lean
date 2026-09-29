-- Prove2me | solution 1 for Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/aa6655e5-a3c6-5015-939b-a769a46c724c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime

set_option autoImplicit false

open NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hℓ : (Module.finrank K L).Prime)
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p] :
    ((p.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = Module.finrank K L ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = Module.finrank K L) := by
  classical
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 L) Gal(L/K)
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) hp,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := p) (q := P),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L] at hmain
  set g := (p.primesOver (𝓞 L)).ncard with hg
  set e := p.ramificationIdx' P with he
  set f := p.inertiaDeg' P with hf
  set ℓ := Module.finrank K L with hℓdef
  have hprime : ℓ.Prime := hℓ
  have hprod : g * (e * f) = ℓ := hmain

  have hdvd_g : g ∣ ℓ := ⟨e * f, hprod.symm⟩
  rcases (Nat.dvd_prime hprime).mp hdvd_g with hg1 | hgl
  ·
    have hef : e * f = ℓ := by simpa [hg1] using hprod
    have hdvd_e : e ∣ ℓ := ⟨f, hef.symm⟩
    rcases (Nat.dvd_prime hprime).mp hdvd_e with he1 | hel
    ·
      have hfl : f = ℓ := by simpa [he1] using hef
      exact Or.inr (Or.inr ⟨hg1, he1, hfl⟩)
    ·
      have hf1 : f = 1 := by
        have : ℓ * f = ℓ * 1 := by rw [mul_one, ← hel]; exact hel ▸ hef
        exact Nat.eq_of_mul_eq_mul_left hprime.pos this
      exact Or.inr (Or.inl ⟨hg1, hel, hf1⟩)
  ·
    have hef : e * f = 1 := by
      have : ℓ * (e * f) = ℓ * 1 := by rw [mul_one]; exact hgl ▸ hprod
      exact Nat.eq_of_mul_eq_mul_left hprime.pos this
    exact Or.inl ⟨hgl, Nat.eq_one_of_mul_eq_one_right hef, Nat.eq_one_of_mul_eq_one_left hef⟩

end S_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
end P2MW
export P2MW.S_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime (solution)
