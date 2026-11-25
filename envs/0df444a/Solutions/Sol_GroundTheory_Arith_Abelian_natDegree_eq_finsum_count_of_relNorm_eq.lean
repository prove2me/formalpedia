-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.natDegree_eq_finsum_count_of_relNorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:21.933803+00:00
-- url     : https://prove2.me/submissions/6d0b80e1-6b5a-4198-b5d9-ac09a0fc739a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Theorems.Thm_GroundTheory_Arith_Abelian_relNorm_XYIdeal
import Theorems.Thm_GroundTheory_Arith_Abelian_finite_support_count
import Theorems.Thm_GroundTheory_Arith_Abelian_finsum_count_XYIdeal
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {I : Ideal W.toAffine.CoordinateRing} (hI : I ≠ 0)
    {p : F[X]} (hp : Ideal.relNorm F[X] I = Ideal.span {p}) :
    (p.natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime generalizing p with
  | h₁ => exact absurd rfl hI
  | h₂ I hu =>
    rw [Ideal.isUnit_iff.mp hu, Ideal.relNorm_top, eq_comm, Ideal.span_singleton_eq_top] at hp
    rw [Ideal.isUnit_iff.mp hu, FractionalIdeal.coeIdeal_top]
    simp [FractionalIdeal.count_one, natDegree_eq_zero_of_isUnit hp]
  | h₃ a P ha hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have := Ideal.isPrime_of_prime hP
    obtain ⟨x, y, h, rfl⟩ := exists_eq_XYIdeal W hP0
    obtain ⟨g, hg⟩ : ∃ g, Ideal.relNorm F[X] a = Ideal.span {g} :=
      ⟨_, (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
    have hg0 : g ≠ 0 := by
      rintro rfl
      have hb : Ideal.relNorm F[X] a = ⊥ := by rw [hg]; simp
      exact ha (Ideal.relNorm_eq_bot_iff.mp hb)
    rw [map_mul, relNorm_XYIdeal W h, hg, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_span_singleton] at hp
    have hdeg : p.natDegree = ((X - C x) * g).natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hp).symm
    have hc0 : ((XYIdeal W.toAffine x (C y) : Ideal _) :
        FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hP0
    have ha0 : (a : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr ha
    rw [hdeg, natDegree_mul (X_sub_C_ne_zero x) hg0, natDegree_X_sub_C,
      FractionalIdeal.coeIdeal_mul]
    simp_rw [FractionalIdeal.count_mul _ _ hc0 ha0]
    rw [finsum_add_distrib (finite_support_count W _) (finite_support_count W _),
      finsum_count_XYIdeal W h, ← ih ha hg]
    push_cast
    ring
end GroundTheory.Arith.Abelian
