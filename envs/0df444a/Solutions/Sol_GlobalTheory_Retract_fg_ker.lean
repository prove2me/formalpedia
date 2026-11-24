-- Prove2me | solution 1 for GlobalTheory.Retract.fg_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:32.232477+00:00
-- url     : https://prove2.me/submissions/b40b5f29-68f4-4f8e-a35e-ea4293f7d9f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (s : A →ₐ[R] B) (p : B →ₐ[R] A) (h : p.comp s = AlgHom.id R A)
include h
namespace GlobalTheory.Retract
theorem _root_.solution [Algebra.FiniteType R B] : (RingHom.ker p.toRingHom).FG := by
  classical
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := B)
  refine ⟨t.image fun b ↦ b - s (p b), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    have : p (s (p b)) = p b := congr($h (p b))
    simp [RingHom.mem_ker, this]
  · set I : Ideal B := Ideal.span (↑(t.image fun b ↦ b - s (p b)) : Set B)
    have key : Ideal.Quotient.mkₐ R I = (Ideal.Quotient.mkₐ R I).comp (s.comp p) := by
      refine AlgHom.ext_of_adjoin_eq_top ht fun b hb ↦ ?_
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hb))
    intro b hb
    have hb' : p b = 0 := hb
    have := congr($key b)
    simp only [AlgHom.comp_apply, hb', map_zero, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
end GlobalTheory.Retract
