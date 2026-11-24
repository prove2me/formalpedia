-- Prove2me | solution 1 for GlobalTheory.HilbFam.coef_support_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:40.969615+00:00
-- url     : https://prove2.me/submissions/7211f5fe-b934-4712-b20f-0ecf0916b461

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLatticeLevelTraceDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyRealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinCoeffSupportTraceFinite
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HilbFam_sum_realEmb_eq_trace
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latM_eq_dual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma le_one_and_mem_latM_of_hasLevel {F : Type} [Field F] [NumberField F] {N : ℕ}
    {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {x : F}
    (h : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) :
    ((B : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) ∧ (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A ∧
      (N : F) * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A := by
  obtain ⟨h1, h2⟩ := h
  have mem : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.split A B x ↔
      v 0 ∈ (B : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A :=
    fun v ↦ Iff.rfl
  have std : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.stdLat F ↔
      ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := by
    intro v; simp [_root_.GlobalTheory.HilbFam.stdLat, Submodule.mem_pi]
  have one_mem : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have zero_mem' : (0 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.zero_mem _
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    have hv : ![b, b * x] ∈ _root_.GlobalTheory.HilbFam.split A B x :=
      (mem _).2 ⟨by simpa using hb, by
        simpa using FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)⟩
    have := ((std _).1 (h2 hv)) 0
    simp only [Matrix.cons_val_zero] at this
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨y, hy⟩
  · have hv := h1 ![0, 1] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := ((mem _).1 hv).2
    simpa [Algebra.smul_def] using this
  · have hv := h1 ![1, 0] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := FractionalIdeal.mem_coe.1
      (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 ((mem _).1 hv).2))
    simpa [Algebra.smul_def] using this
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma mem_and_totally_pos_of_coeff_ne_zero {F : Type} [Field F] [NumberField F]
    {k N : ℕ} {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k A B a₀ a)
    (hN : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) {ξ : F}
    (hξ0 : ξ ≠ 0) (hξ : a ξ ≠ 0) :
    ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := by
  obtain ⟨-, -, hsupp, -⟩ := ha
  obtain ⟨hmem, hpos⟩ := hsupp ξ hξ0 hξ
  refine ⟨?_, hpos⟩
  have hB := (le_one_and_mem_latM_of_hasLevel hN).1
  have hle : ((A * B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : FractionalIdeal (𝓞 F)⁰ F) ≤ A := by
    rw [Units.val_mul]
    calc (A : FractionalIdeal (𝓞 F)⁰ F) * B ≤ A * 1 := by gcongr
      _ = A := mul_one _
  exact hle hmem
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma sum_realEmbeddings_eq_trace {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] (y : F) :
    ∑ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i y = ((Algebra.trace ℚ F y : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  exact _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace F y
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma trace_mul_int_of_mem_latM {F : Type} [Field F] [NumberField F]
    {A : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {y ξ : F} (hy : y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A)
    (hξ : ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F)) : ∃ c : ℤ, Algebra.trace ℚ F (y * ξ) = c := by
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual A.ne_zero] at hy
  obtain ⟨c, hc⟩ := hy ξ hξ
  exact ⟨c, by simpa [Algebra.traceForm_apply] using hc.symm⟩
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_support_trace_natCast_and_finite {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] {k : ℕ} {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    {N : ℕ} (hN : 0 < N) (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a)
    (hlev : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x)) :
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite := by
  have hNF : (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 := (le_one_and_mem_latM_of_hasLevel hlev).2.1
  have hpos : ∀ ξ, a ξ ≠ 0 → ξ ≠ 0 → ξ ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := fun ξ hξ hξ0 ↦
    mem_and_totally_pos_of_coeff_ne_zero ha hlev hξ0 hξ

  have hbound : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
    intro ξ hξ i
    rw [← sum_realEmbeddings_eq_trace]
    exact Finset.single_le_sum (fun j _ ↦ (hξ j).le) (Finset.mem_univ i)
  have htr_nonneg : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      0 ≤ Algebra.trace ℚ F ξ := by
    intro ξ hξ
    have : (0 : ℝ) ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
      rw [← sum_realEmbeddings_eq_trace]
      exact Finset.sum_nonneg fun j _ ↦ (hξ j).le
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    by_cases hξ0 : ξ = 0
    · exact ⟨0, by simp [hξ0]⟩
    obtain ⟨hmem, hξpos⟩ := hpos ξ hξ hξ0
    obtain ⟨c, hc⟩ := trace_mul_int_of_mem_latM hNF hmem
    have hc' : (N : ℚ) * Algebra.trace ℚ F ξ = c := by
      rw [← hc, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
    have hc0 : 0 ≤ c := by
      have : (0 : ℚ) ≤ c := hc' ▸ mul_nonneg (Nat.cast_nonneg _) (htr_nonneg ξ hξpos)
      exact_mod_cast this
    exact ⟨c.toNat, by rw [hc']; exact_mod_cast (Int.toNat_of_nonneg hc0).symm⟩
  · intro n
    obtain ⟨d, hd0, hd⟩ := (𝔞 : FractionalIdeal (𝓞 F)⁰ F).isFractional
    set D : F := algebraMap (𝓞 F) F d with hD
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0
    set M : ℝ := (∑ φ : F →+* ℂ, ‖φ D‖) * ((n : ℝ) / N) with hM
    have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ M
    refine (hfin.image fun z ↦ z / D).subset ?_
    rintro ξ ⟨hξ, htr⟩
    refine ⟨D * ξ, ⟨?_, ?_⟩, by field_simp⟩
    · by_cases hξ0 : ξ = 0
      · simpa [hξ0] using isIntegral_zero
      obtain ⟨r, hr⟩ := hd ξ (hpos ξ hξ hξ0).1
      have hDξ : D * ξ = algebraMap (𝓞 F) F r := by rw [hr, Algebra.smul_def]
      rw [hDξ]
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro φ
      have hMnn : 0 ≤ M := by rw [hM]; positivity
      rw [map_mul, norm_mul]
      by_cases hξ0 : ξ = 0
      · simpa [hξ0] using hMnn
      have hξpos := (hpos ξ hξ hξ0).2
      have hφ := IsTotallyReal.complexEmbedding_isReal φ
      have htrq : Algebra.trace ℚ F ξ = n / N := by
        rw [eq_div_iff (by exact_mod_cast hN.ne')]
        rw [mul_comm]; exact htr
      have hφξ : ‖φ ξ‖ ≤ (n : ℝ) / N := by
        rw [← ComplexEmbedding.IsReal.coe_embedding_apply hφ, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hξpos _)]
        calc ComplexEmbedding.IsReal.embedding hφ ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) :=
              hbound ξ hξpos _
          _ = (n : ℝ) / N := by rw [htrq]; push_cast; ring
      have hφD : ‖φ D‖ ≤ ∑ ψ : F →+* ℂ, ‖ψ D‖ :=
        Finset.single_le_sum (fun ψ _ ↦ norm_nonneg (ψ D)) (Finset.mem_univ φ)
      rw [hM]
      exact mul_le_mul hφD hφξ (norm_nonneg _) (Finset.sum_nonneg fun ψ _ ↦ norm_nonneg _)
end GlobalTheory.HilbFam
end

set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
namespace _root_.GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F)
    (N : ℕ), 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a →
    _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) →
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite :=
  fun _ _ _ _ _ _ _ _ _ _ _ hN ha hlev ↦ coeff_support_trace_natCast_and_finite hN ha hlev
end _root_.GlobalTheory.HilbFam
end GlobalTheory.HilbFam
