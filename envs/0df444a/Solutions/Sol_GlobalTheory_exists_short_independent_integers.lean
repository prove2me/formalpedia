-- Prove2me | solution 1 for GlobalTheory.exists_short_independent_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:19.329375+00:00
-- url     : https://prove2.me/submissions/e9bfdda5-f7e6-4055-90a9-8efc8d4fa025

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsShortIndependentIntegers
import Theorems.Thm_GlobalTheory_finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual
import Theorems.Thm_GlobalTheory_trace_eq_sum_complexEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_transference_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module Submodule
open scoped nonZeroDivisors
namespace GlobalTheory
namespace ShortIntegers
section Pairing
variable {V : Type} [AddCommGroup V] [Module ℚ V]
end Pairing
variable {K : Type} [Field K] [NumberField K]
end ShortIntegers
open NumberField Module Submodule in
open scoped nonZeroDivisors in
private lemma sum_embeddings_eq_zero_of_conjugate_neg {K : Type} [Field K] [NumberField K] (f : (K →+* ℂ) → ℝ)
    (hf : ∀ σ, f (NumberField.ComplexEmbedding.conjugate σ) = - f σ) : ∑ σ, f σ = 0 := by
  have h := Equiv.sum_comp (NumberField.ComplexEmbedding.involutive_conjugate K).toPerm f
  simp only [Function.Involutive.coe_toPerm, hf, Finset.sum_neg_distrib] at h
  linarith
open NumberField Module Submodule in
open scoped nonZeroDivisors in
private lemma inner_realCoords_one_neg_one_eq_trace {K : Type} [Field K] [NumberField K] {M : ℕ}
    (e : Fin M ≃ (K →+* ℂ)) (x y : K) :
    inner ℝ (_root_.GlobalTheory.ShortIntegers.realCoords e 1 x) (_root_.GlobalTheory.ShortIntegers.realCoords e (-1) y)
      = ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) := by
  have ht := congrArg Complex.re (_root_.GlobalTheory.trace_eq_sum_complexEmbeddings (x * y))
  simp [PiLp.inner_apply, _root_.GlobalTheory.ShortIntegers.realCoords]
  simp at ht
  rw [ht, Equiv.sum_comp e (fun σ => ((σ y).re + -(σ y).im) * ((σ x).re + (σ x).im)),
    ← Finset.sum_sub_distrib]
  have h0 := sum_embeddings_eq_zero_of_conjugate_neg (K := K) (fun σ => (σ x).im * (σ y).re - (σ x).re * (σ y).im)
    (by intro σ; simp [NumberField.ComplexEmbedding.conjugate_coe_eq]; ring)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring
open NumberField Module Submodule in
open scoped nonZeroDivisors in
private lemma norm_sq_realCoords_eq_sum_norm_sq {K : Type} [Field K] [NumberField K] {M : ℕ}
    (e : Fin M ≃ (K →+* ℂ)) {ε : ℝ} (hε : ε ^ 2 = 1) (x : K) :
    ‖_root_.GlobalTheory.ShortIntegers.realCoords e ε x‖ ^ 2 = ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [_root_.GlobalTheory.ShortIntegers.realCoords, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs,
    sq_abs]
  rw [Equiv.sum_comp e (fun σ => ((σ x).re + ε * (σ x).im) ^ 2)]
  have h0 := sum_embeddings_eq_zero_of_conjugate_neg (K := K) (fun σ => 2 * ε * (σ x).re * (σ x).im)
    (by intro σ; simp [NumberField.ComplexEmbedding.conjugate_coe_eq])
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  linear_combination (σ x).im ^ 2 * hε
end GlobalTheory
end

set_option autoImplicit false
open NumberField Module Submodule
open scoped nonZeroDivisors
open GlobalTheory
open NumberField Module Submodule
open scoped nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (K : Type) [Field K] [NumberField K] :
    ∃ ω : Fin (Module.finrank ℚ K) → 𝓞 K, LinearIndependent ℚ (fun k => (ω k : K)) ∧
      ∀ (s : K →+* ℂ) k, ‖s (ω k : K)‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  set n := Module.finrank ℚ K with hn
  let e : Fin n ≃ (K →+* ℂ) := (Fintype.equivFinOfCardEq (NumberField.Embeddings.card K ℂ)).symm
  let φ := _root_.GlobalTheory.ShortIntegers.realCoords e 1
  let ψ := _root_.GlobalTheory.ShortIntegers.realCoords e (-1)
  have hpair : ∀ x y : K, inner ℝ (φ x) (ψ y) = ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) :=
    inner_realCoords_one_neg_one_eq_trace e
  let eι : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin n :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis (NumberField.integralBasis K)).symm
  let α : Module.Basis (Fin n) ℚ K := (NumberField.integralBasis K).reindex eι
  let β := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) α
  have hαβ : ∀ i j, Algebra.trace ℚ K (α i * β j) = if i = j then 1 else 0 := by
    intro i j
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left]
  have hli : LinearIndependent ℝ (fun j => ψ (β j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (fun v => inner ℝ (φ (α i)) v) hc
    simp only [inner_sum, inner_smul_right, hpair, hαβ, inner_zero_right] at h
    simpa [apply_ite (Rat.cast : ℚ → ℝ), mul_ite] using h
  have hliφ : LinearIndependent ℝ (fun j => φ (α j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (fun v => inner ℝ v (ψ (β i))) hc
    simp only [sum_inner, inner_smul_left, hpair, hαβ, inner_zero_left] at h
    simpa [apply_ite (Rat.cast : ℚ → ℝ), mul_ite] using h
  haveI : NeZero n := ⟨(Module.finrank_pos (R := ℚ) (M := K)).ne'⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bφ := basisOfLinearIndependentOfCardEqFinrank hliφ hcard
  have hα_int : ∀ j, α j = algebraMap (𝓞 K) K (RingOfIntegers.basis K (eι.symm j)) := by
    intro j
    simp [α, NumberField.integralBasis_apply]
  have hdual : ∀ c : Fin n → ℤ,
      (∑ i, (c i : ℚ) • β i) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    intro c
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
    have hspan : algebraMap (𝓞 K) K a' ∈ Submodule.span ℤ (Set.range α) := by
      rw [show Set.range α = Set.range (NumberField.integralBasis K) from
        Module.Basis.range_reindex _ _]
      exact (NumberField.mem_span_integralBasis K).mpr ⟨a', rfl⟩
    refine Submodule.span_induction (p := fun x _ =>
      (Algebra.traceForm ℚ K) (∑ i, (c i : ℚ) • β i) x ∈ (algebraMap ℤ ℚ).range)
      ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨k, rfl⟩
      refine ⟨c k, ?_⟩
      rw [map_sum, LinearMap.sum_apply]
      simp [Algebra.traceForm_apply, mul_comm (β _) (α k), hαβ]
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro m x _ hx
      rw [map_zsmul]
      exact zsmul_mem hx m
  set D : ℝ := |((NumberField.discr K : ℤ) : ℝ)| with hDdef
  have hD : 0 < D := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set lam : ℝ := D ^ (-(1 / (n : ℝ))) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hD _
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have hxz : ∑ i, c i • b i = ψ (∑ i, (c i : ℚ) • β i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul, Int.cast_smul_eq_zsmul, coe_basisOfLinearIndependentOfCardEqFinrank]
    rw [hxz] at hx0 ⊢
    have hz0 : (∑ i, (c i : ℚ) • β i) ≠ 0 := by
      rintro h
      apply hx0
      rw [h, map_zero]
    have hle := _root_.GlobalTheory.finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual (hdual c) hz0
    rw [← norm_sq_realCoords_eq_sum_norm_sq e (ε := -1) (by norm_num)] at hle
    have hlam2 : lam ^ 2 ≤ (n : ℝ) * D ^ (-2 / (n : ℝ)) := by
      rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
      have : -(1 / (n : ℝ)) * ((2 : ℕ) : ℝ) = -2 / (n : ℝ) := by push_cast; ring
      rw [this]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hD.le _) hn1
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (hlam2.trans hle)
  obtain ⟨y, hyli, hyint, hynorm⟩ := _root_.ReciprocityTheory.ChartRestriction.G.T0.transference_dual b lam hlam0 hmin
  choose m hm using hyint
  let ω : Fin n → 𝓞 K := fun i => ∑ j, m i j • RingOfIntegers.basis K (eι.symm j)
  have hω : ∀ i, ((ω i : 𝓞 K) : K) = ∑ j, (m i j : ℚ) • α j := by
    intro i
    simp [ω, hα_int, Int.cast_smul_eq_zsmul]
  have hy : ∀ i, y i = φ (ω i) := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis b fun j => ?_
    rw [hm, coe_basisOfLinearIndependentOfCardEqFinrank, hpair, hω, Finset.sum_mul, map_sum]
    simp [smul_mul_assoc, hαβ]
  refine ⟨ω, ?_, ?_⟩
  · have h := hyli.restrict_scalars' ℚ
    rw [show y = fun k => φ (ω k) from funext hy] at h
    exact LinearIndependent.of_comp φ h
  · intro s k
    have hsq : ‖s (ω k : K)‖ ^ 2 ≤ ‖y k‖ ^ 2 := by
      rw [hy, norm_sq_realCoords_eq_sum_norm_sq e (ε := 1) (by norm_num)]
      exact Finset.single_le_sum (f := fun σ : K →+* ℂ => ‖σ (ω k : K)‖ ^ 2)
        (fun σ _ => sq_nonneg _) (Finset.mem_univ s)
    have h1 : ‖s (ω k : K)‖ ≤ ‖y k‖ :=
      le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
    have h2 : (n : ℝ) ^ 2 / lam = (n : ℝ) ^ 2 * D ^ (1 / (n : ℝ)) := by
      rw [hlam, Real.rpow_neg hD.le, div_inv_eq_mul]
    calc ‖s (ω k : K)‖ ≤ (n : ℝ) ^ 2 / lam := h1.trans (hynorm k)
      _ = (n : ℝ) ^ 2 * D ^ (1 / (n : ℝ)) := h2
      _ ≤ (n : ℝ) ^ 3 * D ^ (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 (by norm_num))
          (Real.rpow_nonneg hD.le _)
end _root_.GlobalTheory
end GlobalTheory
