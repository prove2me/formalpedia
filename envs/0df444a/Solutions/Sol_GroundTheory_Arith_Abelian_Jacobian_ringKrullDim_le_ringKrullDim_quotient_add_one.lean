-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_le_ringKrullDim_quotient_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:26.568315+00:00
-- url     : https://prove2.me/submissions/fecc332d-902e-4a8a-93ca-3e840e880a07

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_of_normalization
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_sub_one_le_trdeg_quotient_span_prime
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_eq_of_isIntegral


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
include k
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution (p : Ideal A) [p.IsPrime]
    (hp : p.height = 1) : ringKrullDim A ≤ ringKrullDim (A ⧸ p) + 1 := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have _ : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hint x⟩
  have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hdimA : ringKrullDim A = s := ringKrullDim_eq_of_normalization k g hinj hint
  set q : Ideal (MvPolynomial (Fin s) k) := p.under (MvPolynomial (Fin s) k) with hq
  have hpne : p ≠ ⊥ := fun h => by rw [h, Ideal.height_bot] at hp; exact zero_ne_one hp
  have hqne : q ≠ ⊥ := Ideal.under_ne_bot _ hpne

  have hqle : q.height ≤ 1 := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p
    rw [← hp, h]
    exact le_self_add

  obtain ⟨f, hfq, hf⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (inferInstance : q.IsPrime) hqne
  have hspan : Ideal.span {f} = q := by
    by_contra hne
    have hlt : Ideal.span {f} < q :=
      lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).2 hfq) hne
    have _ : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf
    have h0 : (⊥ : Ideal (MvPolynomial (Fin s) k)) < Ideal.span {f} := by
      rw [bot_lt_iff_ne_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact hf.ne_zero
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [Ideal.height_bot, zero_add] at h1
    have : (2 : ℕ∞) ≤ q.height := le_trans (by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (Ideal.span {f}).height + 1 := by gcongr) h2
    exact absurd (this.trans hqle) (by decide)

  have hdimq : ringKrullDim (A ⧸ p) = ringKrullDim (MvPolynomial (Fin s) k ⧸ q) :=
    GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Ideal.algebraMap_quotient_injective)

  have _ : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf
  obtain ⟨m, hm, htr⟩ := exists_ringKrullDim_eq_trdeg (k := k)
    (A := MvPolynomial (Fin s) k ⧸ Ideal.span {f})
  have hsm : s - 1 ≤ m := by
    have := sub_one_le_trdeg_quotient_span_prime k hf
    rw [htr] at this
    exact_mod_cast this
  rw [hdimA, hdimq, ← hspan, hm]
  have : s ≤ m + 1 := by omega
  exact_mod_cast this
end GroundTheory.Arith.Abelian.Jacobian
