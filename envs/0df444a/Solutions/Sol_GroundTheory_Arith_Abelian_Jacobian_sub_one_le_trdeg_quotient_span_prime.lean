-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.sub_one_le_trdeg_quotient_span_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:29.195887+00:00
-- url     : https://prove2.me/submissions/ee205a46-68c8-4881-a4cd-9868db5ba408

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne

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
variable (k : Type u) [Field k]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution {s : ℕ} {g : MvPolynomial (Fin s) k} (hg : Prime g) :
    ((s - 1 : ℕ) : Cardinal) ≤ trdeg k (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) := by
  classical
  have hg0 : g ≠ 0 := hg.ne_zero

  obtain ⟨i, hi⟩ : ∃ i, g.degreeOf i ≠ 0 := by
    by_contra! h
    have hv : g.vars = ∅ := by
      ext i
      simp [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, h i]
    rw [MvPolynomial.vars_eq_empty_iff_eq_C] at hv
    have hc : g.coeff 0 ≠ 0 := fun h0 => hg0 (by rw [hv, h0, map_zero])
    exact hg.not_isUnit (hv ▸ ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C))
  let x : {j : Fin s // j ≠ i} → MvPolynomial (Fin s) k ⧸ Ideal.span {g} :=
    fun j => Ideal.Quotient.mk _ (MvPolynomial.X j.1)
  have hx : AlgebraicIndependent k x := by
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
    intro h hh
    have e' : (MvPolynomial.aeval x : MvPolynomial _ k →ₐ[k] _) =
        (Ideal.Quotient.mkₐ k (Ideal.span {g})).comp (MvPolynomial.rename Subtype.val) :=
      MvPolynomial.algHom_ext fun j => by simp [x]
    have e : MvPolynomial.aeval x h =
        Ideal.Quotient.mk _ (MvPolynomial.rename Subtype.val h) := by
      rw [e']
      rfl
    rw [e, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hh
    obtain ⟨c, hc⟩ := hh
    have hdeg : (MvPolynomial.rename Subtype.val h).degreeOf i = 0 := by
      by_contra hne
      rw [← ne_eq, ← MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hne
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename _ _ hne)
      exact j.2 hj
    by_cases hc0 : c = 0
    · rw [hc0, mul_zero] at hc
      exact MvPolynomial.rename_injective _ Subtype.val_injective (by simpa using hc)
    · rw [hc, MvPolynomial.degreeOf_mul_eq hg0 hc0] at hdeg
      omega
  have h1 := hx.lift_cardinalMk_le_trdeg
  have hcard : Fintype.card {j : Fin s // j ≠ i} = s - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  rw [Cardinal.mk_fintype, hcard, Cardinal.lift_natCast] at h1
  simpa using h1
end GroundTheory.Arith.Abelian.Jacobian
