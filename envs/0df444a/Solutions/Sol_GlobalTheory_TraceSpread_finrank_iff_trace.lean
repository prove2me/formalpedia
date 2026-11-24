-- Prove2me | solution 1 for GlobalTheory.TraceSpread.finrank_iff_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:26.558126+00:00
-- url     : https://prove2.me/submissions/51e0c0b5-c28f-44eb-a936-f4fb13b12956

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Theorems.Thm_GlobalTheory_TraceSpread_exists_embedding
import Theorems.Thm_GlobalTheory_TraceSpread_trace_eq_sum
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.TraceSpread
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
private lemma intTrace_cast_eq_sum_embeddings {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (a : 𝓞 E) :
    ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K) = ∑ φ : E →+* K, φ a := by
  have h₁ := Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E) a
  have h₂ := trace_eq_sum_embeddings (K := ℚ) (L := E) K (x := (a : E))
  calc ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K)
      = algebraMap ℚ K (algebraMap ℤ ℚ (Algebra.intTrace ℤ (𝓞 E) a)) := by simp
    _ = algebraMap ℚ K (Algebra.trace ℚ E (algebraMap (𝓞 E) E a)) := by rw [h₁]
    _ = ∑ σ : E →ₐ[ℚ] K, σ (a : E) := h₂
    _ = ∑ φ : E →+* K, φ a :=
      (Fintype.sum_equiv (RingHom.equivRatAlgHom E K) _ _ fun φ => rfl).symm
end GlobalTheory.TraceSpread
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TraceSpread
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.TraceSpread
namespace _root_.GlobalTheory.TraceSpread
theorem _root_.solution (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) {K : Type} [Field K]
    [IsAlgClosed K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [Module.Finite K V] (ρ : 𝓞 E →+* Module.End K V) (s : K)
    (hs : s ^ 2 = -(H.d : K)) :
    (∀ τ : 𝓞 E →+* K, (τ H.rt = s → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ τ) = p) ∧
      (τ H.rt ≠ s → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ τ) = q)) ↔
    ∀ a, 2 * s * LinearMap.trace K V (ρ a) =
      (p + q) * s * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K) +
      (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : K) := by
  have hroot : ∀ τ : 𝓞 E →+* K, τ H.rt = s ∨ τ H.rt = -s := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [hs, ← map_pow, H.rt_sq, map_neg, map_natCast]
  have hs0 : s ≠ 0 := by
    rintro rfl
    have hd : (H.d : K) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
    apply hd
    have := hs
    rw [zero_pow two_ne_zero] at this
    exact neg_eq_zero.mp this.symm
  constructor
  · intro hmult a
    rw [_root_.GlobalTheory.TraceSpread.trace_eq_sum, intTrace_cast_eq_sum_embeddings,
      intTrace_cast_eq_sum_embeddings, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [show ((H.rt * a : 𝓞 E) : E) = (H.rt : E) * (a : E) from map_mul (algebraMap (𝓞 E) E) _ _,
      map_mul]
    rcases hroot (φ.comp (algebraMap (𝓞 E) E)) with h | h
    · rw [(hmult _).1 h]
      have h' : φ (H.rt : E) = s := h
      rw [h']
      ring
    · have hne : (φ.comp (algebraMap (𝓞 E) E)) H.rt ≠ s := by
        rw [h]; intro h'; exact hs0 (by linear_combination -h' / 2)
      rw [(hmult _).2 hne]
      have h' : φ (H.rt : E) = -s := h
      rw [h']
      ring
  · intro hid τ
    obtain ⟨φ, rfl⟩ := _root_.GlobalTheory.TraceSpread.exists_embedding τ
    let c : (E →+* K) → K := fun ψ =>
      2 * s * (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (ψ.comp (algebraMap (𝓞 E) E))) : K) -
        ((p + q) * s + (p - q) * ψ (H.rt : E))
    have hli := (linearIndependent_monoidHom (𝓞 E) K).comp
      (fun ψ : E →+* K => ((ψ.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* K) : 𝓞 E →* K))
      (fun ψ₁ ψ₂ h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        (RingHom.ext fun x => DFunLike.congr_fun h x))
    have hc : c φ = 0 := by
      refine Fintype.linearIndependent_iff.mp hli c ?_ φ
      funext a
      rw [Finset.sum_apply, Pi.zero_apply]
      have h₁ := hid a
      rw [_root_.GlobalTheory.TraceSpread.trace_eq_sum, intTrace_cast_eq_sum_embeddings,
        intTrace_cast_eq_sum_embeddings, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun ψ _ => ?_) h₁
      change c ψ * ψ (a : E) = _
      rw [show ((H.rt * a : 𝓞 E) : E) = (H.rt : E) * (a : E) from map_mul (algebraMap (𝓞 E) E) _ _,
        map_mul]
      simp only [c]
      ring
    have hd2 : (2 : K) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
    simp only [c, sub_eq_zero] at hc
    constructor
    · intro h
      have h' : φ (H.rt : E) = s := h
      rw [h'] at hc
      have hm : (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : K)
          = p := mul_left_cancel₀ hd2 (by linear_combination hc)
      exact_mod_cast hm
    · intro h
      have h'' := (hroot (φ.comp (algebraMap (𝓞 E) E))).resolve_left h
      have h' : φ (H.rt : E) = -s := h''
      rw [h'] at hc
      have hm : (Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : K)
          = q := mul_left_cancel₀ hd2 (by linear_combination hc)
      exact_mod_cast hm
end _root_.GlobalTheory.TraceSpread
end GlobalTheory.TraceSpread
