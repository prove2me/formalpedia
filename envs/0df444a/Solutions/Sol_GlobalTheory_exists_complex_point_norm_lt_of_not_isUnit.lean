-- Prove2me | solution 1 for GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:45.131263+00:00
-- url     : https://prove2.me/submissions/0172f7fb-bc36-49ac-8cef-9a55d57c5175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
import Theorems.Thm_GlobalTheory_SmallPoint_exists_small_of_curve
import Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_finiteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
      (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 →
      ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧
        ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  intro K B _ _ _ _ _ σ n w u q hu hq
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) K) B := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Nontrivial (B ⧸ Ideal.span {u}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨p₀, hp₀⟩ := exists_ringHom_extend_of_finiteType K (B ⧸ Ideal.span {u}) ℂ σ
  let p : B →+* ℂ := p₀.comp (Ideal.Quotient.mk _)
  have hpu : p u = 0 := by
    change p₀ (Ideal.Quotient.mk _ u) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self u), map_zero]
  obtain ⟨r, hr, c, hc⟩ :=
    (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) K) q).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hq)
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, MvPolynomial.eval z (MvPolynomial.map σ r) ≠ 0 := by
    by_contra! h
    exact hr (MvPolynomial.map_injective σ σ.injective
      (MvPolynomial.funext (by simpa using h)))
  let Ψ : MvPolynomial (Fin d) K →+* ℂ[X] := MvPolynomial.eval₂Hom (C.comp σ)
    fun j => C (p (g (MvPolynomial.X j))) + X * C (z j - p (g (MvPolynomial.X j)))
  have hΨ0 : p.comp (algebraMap (MvPolynomial (Fin d) K) B) = (evalRingHom 0).comp Ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · have : p (g (MvPolynomial.C a)) = σ a := by
        rw [MvPolynomial.algHom_C]
        exact hp₀ a
      exact this.trans (by simp [Ψ])
    · simp [Ψ]
      rfl
  have hΨ1 : (evalRingHom 1).comp Ψ = (MvPolynomial.eval z).comp (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_) <;> simp [Ψ]
  have hΨr : Ψ r ≠ 0 := fun h => hz (by
    have := DFunLike.congr_fun hΨ1 r
    simpa [h] using this.symm)
  obtain ⟨M, hM⟩ := SmallPoint.exists_small_of_curve Ψ p hΨ0 w hpu hΨr
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨s, φ, hφ, h1, h2, h3⟩ := hM ε hε
  refine ⟨φ, RingHom.ext fun a => ?_, fun h => h1 ?_, h2, h3⟩
  · have := DFunLike.congr_fun hφ (MvPolynomial.C a)
    rw [RingHom.comp_apply, ← MvPolynomial.algHom_C g]
    exact this.trans (by simp [Ψ])
  · have := DFunLike.congr_fun hφ r
    rw [RingHom.comp_apply, hc, map_mul, h, zero_mul] at this
    exact this.symm
end GlobalTheory
