-- Prove2me | solution 1 for GlobalTheory.NormSquareRamified.jacobiSym_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:14.454882+00:00
-- url     : https://prove2.me/submissions/8bc62b58-0a8a-4244-b776-a440ba4dce0f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitNormOfIsCoprime
import Theorems.Thm_GlobalTheory_NormSquareRamified_isUnit_norm_of_isCoprime
import Theorems.Thm_GlobalTheory_NormSquareRamified_exists_sq_sub_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormSquareRamified
namespace GlobalTheory.NormSquareRamified
theorem _root_.solution {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {q : ℤ} (hq : ¬ (p : ℤ) ∣ q) (s : F) (hs : s * s = ((q * p : ℤ) : F)) (y : 𝓞 F)
    (hy : IsCoprime y (p : 𝓞 F)) : jacobiSym (Algebra.norm ℤ y) p = 1 := by
  have := Fact.mk hp
  obtain ⟨A, hA⟩ := exists_sq_sub_norm hp hq s hs y
  have hu := isUnit_norm_of_isCoprime p y hy
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hu.ne_zero]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hA
  push_cast at hA
  refine ⟨(A : ZMod p) / 2, ?_⟩
  field_simp
  linear_combination -hA
end GlobalTheory.NormSquareRamified
