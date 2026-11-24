-- Prove2me | solution 1 for GlobalTheory.LocalDifferentProduct.prod_normDifferentV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:49:11.781055+00:00
-- url     : https://prove2.me/submissions/0ab7f708-62e1-4600-a566-1a4f2093fd2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
import Theorems.Thm_GlobalTheory_LocalDifferentProduct_finprod_card_quot_map
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
open GlobalTheory GlobalTheory.LocalDifferentProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
namespace GlobalTheory.LocalDifferentProduct
namespace _root_.GlobalTheory.LocalDifferentProduct
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → (∀ x : E, star x = σ x) →
    _root_.Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (_root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F)).Finite ∧
      ((∏ᶠ v, _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F v : ℕ) : ℝ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F = (2 * _root_.Formalism.HermitianLatticesTheory.vInv E) ^ _root_.Formalism.HermitianLatticesTheory.fDeg E := by
  intro F E _ _ _ _ _ _ σ hcm hstar hun
  have hD : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h := _root_.GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hD
  have h2 : ∏ᶠ v, _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F v = Ideal.absNorm (differentIdeal ℤ (𝓞 F)) := h.2
  refine ⟨h.1, ?_, ?_⟩
  · rw [h2, NumberField.absNorm_differentIdeal F (𝓞 F)]
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr, Nat.cast_natAbs]
  · have hrank : Module.finrank F E = 2 := hcm.2.2.1
    have hD1 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨θ, t, ht, hθt⟩ := hun.2.2 P hP
      have hσ : σ (algebraMap (𝓞 E) E θ) = algebraMap (𝓞 E) E t := by rw [ht, hstar]
      set x : E := algebraMap (𝓞 E) E θ with hx
      have hxσ : x - σ x = algebraMap (𝓞 E) E (θ - t) := by rw [hσ, map_sub]
      have hxσ0 : x - σ x ≠ 0 := by
        rw [hxσ]
        intro h
        apply hθt
        rw [(map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h]
        exact P.zero_mem
      have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
      have hdeg : (minpoly F x).natDegree = 2 := by
        have h1 := minpoly.natDegree_le (A := F) x
        rw [hrank] at h1
        have h0 := minpoly.natDegree_pos hint
        have hne1 : (minpoly F x).natDegree ≠ 1 := by
          intro h
          obtain ⟨f, hf⟩ := minpoly.natDegree_eq_one_iff.mp h
          apply hxσ0
          rw [← hf, AlgHom.commutes, sub_self]
        omega
      have htopF : IntermediateField.adjoin F {x} = ⊤ := by
        refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
        rw [IntermediateField.adjoin.finrank hint, hdeg, IntermediateField.finrank_top', hrank]
      have htop : Algebra.adjoin F {x} = ⊤ := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htopF,
          IntermediateField.top_toSubalgebra]
      have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ htop
      have hfac : (minpoly F x).map (algebraMap F E) = (X - C x) * (X - C (σ x)) := by
        set q := (minpoly F x).map (algebraMap F E) with hqdef
        have hq : q.IsRoot x := by
          rw [IsRoot, hqdef, eval_map_algebraMap, minpoly.aeval]
        have hqσ : q.IsRoot (σ x) := by
          rw [IsRoot, hqdef, eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
        set r := q /ₘ (X - C x) with hrdef
        have hqr : (X - C x) * r = q := mul_divByMonic_eq_iff_isRoot.mpr hq
        have hqmonic : q.Monic := (minpoly.monic hint).map _
        have hrmonic : r.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C x) (hqr ▸ hqmonic)
        have hrdeg : r.natDegree = 1 := by
          rw [hrdef, natDegree_divByMonic _ (monic_X_sub_C x), natDegree_X_sub_C, hqdef,
            natDegree_map, hdeg]
        have hr := hrmonic.eq_X_add_C hrdeg
        have hrσ : r.eval (σ x) = 0 := by
          have h := hqσ
          rw [IsRoot, ← hqr, eval_mul, eval_sub, eval_X, eval_C] at h
          exact (mul_eq_zero.mp h).resolve_left (by
            intro h'
            apply hxσ0
            rw [← neg_sub, h', neg_zero])
        have hc0 : r.coeff 0 = -σ x := by
          rw [hr, eval_add, eval_X, eval_C] at hrσ
          linear_combination hrσ
        rw [← hqr, hr, hc0, C_neg, ← sub_eq_add_neg]
      have hθint : IsIntegral (𝓞 F) x :=
        (Algebra.IsIntegral.isIntegral (R := 𝓞 F) θ).map (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E)
      have hmapE : (minpoly (𝓞 F) θ).map (algebraMap (𝓞 F) E) = (X - C x) * (X - C (σ x)) := by
        rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 E) E) θ, ← hx,
          IsScalarTower.algebraMap_eq (𝓞 F) F E, ← Polynomial.map_map,
          ← minpoly.isIntegrallyClosed_eq_field_fractions' F hθint, hfac]
      have hval : algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) = x - σ x := by
        rw [← aeval_algebraMap_apply, ← hx, ← eval_map_algebraMap, ← derivative_map, hmapE]
        simp [derivative_mul]
      have hder : aeval θ (derivative (minpoly (𝓞 F) θ)) = θ - t :=
        FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [hval, hxσ])
      exact hθt (hder ▸ hle hmem)
    have hnat : (discr E).natAbs = (discr F).natAbs ^ 2 := by
      rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E),
        hD1, Ideal.absNorm_top, one_mul, hrank]
    have hE : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
      have h' : ((discr E).natAbs : ℝ) = ((discr F).natAbs : ℝ) ^ 2 := by exact_mod_cast hnat
      rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs] at h'
      exact h'
    have hN : (0 : ℝ) < Fintype.card (InfinitePlace E) := by
      exact_mod_cast Fintype.card_pos
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr _root_.Formalism.HermitianLatticesTheory.vInv _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [hE, mul_div_cancel₀ _ (two_ne_zero' ℝ), ← Real.rpow_natCast _ (Fintype.card (InfinitePlace E)),
      ← Real.rpow_natCast |(discr F : ℝ)| 2, ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_mul (abs_nonneg _)]
    have hexp : ((2 : ℕ) : ℝ) * (1 / (2 * (Fintype.card (InfinitePlace E) : ℝ))) *
        (Fintype.card (InfinitePlace E) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_one]
end _root_.GlobalTheory.LocalDifferentProduct
end GlobalTheory.LocalDifferentProduct
