-- Prove2me | solution 1 for GlobalTheory.DefectSumCompare.pow_finrank_eq_span_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:09:22.748426+00:00
-- url     : https://prove2.me/submissions/31b38622-3d4c-4cf7-8892-f7e12d612f91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open GlobalTheory GlobalTheory.DefectSumCompare
namespace GlobalTheory.DefectSumCompare
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hfix : ∀ σ : E ≃ₐ[ℚ] E, σ • I = I) :
    I ^ Module.finrank ℚ E = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} := by
  classical
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hσ : ∀ σ : E ≃ₐ[ℚ] E, Ideal.span {σ • x} = I ^ h := by
    intro σ
    have : σ • (I ^ h) = I ^ h := by rw [smul_pow', hfix]
    rw [← this, hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 E) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
    apply RingOfIntegers.ext
    have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : E)
    rw [← Algebra.coe_norm_int] at h1
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_prod, map_intCast]
    rw [map_intCast] at h1
    exact h1
  have h2 : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} ^ h = (I ^ Module.finrank ℚ E) ^ h := by
    rw [Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    have h3 : Ideal.span {(((Algebra.norm ℤ x).natAbs : ℕ) : 𝓞 E)} =
        Ideal.span {((Algebra.norm ℤ x : ℤ) : 𝓞 E)} := by
      rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
      · conv_rhs => rw [h4]
        rw [Int.cast_natCast]
      · conv_rhs => rw [h4]
        rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
    rw [h3, hnorm, ← Ideal.prod_span_singleton]
    simp only [hσ]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      ← pow_mul, ← pow_mul, mul_comm]
  exact (pow_left_injective hpos h2).symm
end GlobalTheory.DefectSumCompare
