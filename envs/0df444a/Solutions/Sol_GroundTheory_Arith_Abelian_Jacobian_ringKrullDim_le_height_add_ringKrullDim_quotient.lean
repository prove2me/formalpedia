-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_le_height_add_ringKrullDim_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:07.849961+00:00
-- url     : https://prove2.me/submissions/e5e77ef4-794d-4bda-8a13-9c4655836d18

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_quotient_add_one_le
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_le_ringKrullDim_quotient_add_one
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_map_quotient_add_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian GroundTheory.Arith.Abelian.Jacobian
open Algebra Cardinal
universe u
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution : ∀ (n : ℕ) (A : Type u) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A], ringKrullDim A = n →
    ∀ (p : Ideal A) [p.IsPrime], ringKrullDim A ≤ p.height + ringKrullDim (A ⧸ p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ hA p _
  have _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  by_cases hp : p = ⊥
  · subst hp
    rw [Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    simp
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  obtain ⟨p₁, hp₁min, hp₁le⟩ :=
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 ha)
  have _ : p₁.IsPrime := hp₁min.1.1
  have hp₁ne : p₁ ≠ ⊥ := fun h => ha0 (by
    have := hp₁min.1.2 (Ideal.mem_span_singleton_self a)
    rw [h] at this
    simpa using this)
  have hht : p₁.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp₁min) ?_
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hp₁ne)
    simpa using this
  have hC1 := ringKrullDim_le_ringKrullDim_quotient_add_one k p₁ hht
  have hdrop := ringKrullDim_quotient_add_one_le p₁ hp₁ne
  obtain ⟨m, hm, -⟩ := exists_ringKrullDim_eq_trdeg (k := k) (A := A ⧸ p₁)
  have hmn : m < n := by
    rw [hm, hA] at hdrop
    have : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ n := by exact_mod_cast hdrop
    have : m + 1 ≤ n := by exact_mod_cast this
    omega
  have _ : (p.map (Ideal.Quotient.mk p₁)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have ih' := ih m hmn (A ⧸ p₁) hm (p.map (Ideal.Quotient.mk p₁))
  have e : ringKrullDim ((A ⧸ p₁) ⧸ p.map (Ideal.Quotient.mk p₁)) = ringKrullDim (A ⧸ p) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hp₁le)
  have hh := height_map_quotient_add_one_le hp₁le hp₁ne
  rw [e] at ih'
  calc ringKrullDim A ≤ ringKrullDim (A ⧸ p₁) + 1 := hC1
    _ ≤ ((p.map (Ideal.Quotient.mk p₁)).height + ringKrullDim (A ⧸ p)) + 1 := by gcongr
    _ = (((p.map (Ideal.Quotient.mk p₁)).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (A ⧸ p) := by
      push_cast
      ring
    _ ≤ p.height + ringKrullDim (A ⧸ p) := by gcongr; exact_mod_cast hh
end GroundTheory.Arith.Abelian.Jacobian
