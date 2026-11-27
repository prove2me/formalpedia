-- Prove2me | solution 1 for MohP3.HilbertBurch.exact_of_signedMinors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:29.894267+00:00
-- url     : https://prove2.me/submissions/1b140b88-c589-4650-8cf2-e2970b7ada26

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
public import Theorems.Thm_MohP3_HilbertBurch_det_augment
public import Theorems.Thm_MohP3_HilbertBurch_cofactor_column
public import Theorems.Thm_MohP3_HilbertBurch_mulVec_injective_of_minor_ne_zero
attribute [local simp] MohP3.HilbertBurch.rowMap_apply

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
variable {S : Type*} [CommRing S] [IsDomain S]
namespace MohP3.HilbertBurch
theorem _root_.solution (Φ : Matrix (Fin 4) (Fin 3) S) (f : Fin 4 → S) (c : S)
    (hc : IsUnit c)
    (hm : ∀ i : Fin 4, (-1) ^ (i : ℕ) * maximalMinor Φ i = c * f i)
    (hrel : f ᵥ* Φ = 0)
    (s t : S) (hs : s ∈ Ideal.span (Set.range f)) (ht : t ∈ Ideal.span (Set.range f))
    (hs0 : s ≠ 0)
    (hreg : ∀ u : S, t * u ∈ Ideal.span {s} → u ∈ Ideal.span {s}) :
    Function.Injective (Matrix.mulVecLin Φ) ∧
      LinearMap.range (Matrix.mulVecLin Φ) = LinearMap.ker (rowMap f) := by
  -- some generator is nonzero, hence some maximal minor is nonzero
  have hf : ∃ i, f i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hs0
    have : Set.range f ⊆ {0} := by
      rintro _ ⟨i, rfl⟩
      simp [hcon i]
    have := Ideal.span_mono this hs
    simpa using this
  obtain ⟨i₀, hi₀⟩ := hf
  have hminor : maximalMinor Φ i₀ ≠ 0 := by
    intro h0
    have := hm i₀
    rw [h0, mul_zero] at this
    exact hi₀ ((mul_eq_zero.mp this.symm).resolve_left hc.ne_zero)
  have hinj := mulVec_injective_of_minor_ne_zero Φ i₀ hminor
  refine ⟨hinj, ?_⟩
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    change (Φ *ᵥ v) ⬝ᵥ f = 0
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, hrel, zero_dotProduct]
  · intro a ha
    rw [LinearMap.mem_ker, rowMap_apply] at ha
    -- `c f_j a ∈ im Φ` for every `j`
    have hcol : ∀ j : Fin 4, ∃ w : Fin 3 → S, (c * f j) • a = Φ *ᵥ w := by
      intro j
      obtain ⟨w, hw⟩ := cofactor_column a Φ j
      have hdet : (augment a Φ).det = 0 := by
        rw [det_augment]
        have : ∀ i : Fin 4, (-1) ^ (i : ℕ) * a i * maximalMinor Φ i = c * (a i * f i) := by
          intro i
          have := hm i
          linear_combination a i * this
        simp only [this, ← Finset.mul_sum]
        rw [show (∑ i : Fin 4, a i * f i) = a ⬝ᵥ f from rfl, ha, mul_zero]
      refine ⟨-w, ?_⟩
      ext r
      have := hw r
      rw [hdet, ite_self, hm j] at this
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_neg, Pi.neg_apply]
      linear_combination this
    -- hence `c e a ∈ im Φ` for every `e ∈ (f)`
    have hideal : ∀ e ∈ Ideal.span (Set.range f), ∃ W : Fin 3 → S, (c * e) • a = Φ *ᵥ W := by
      intro e he
      obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp he
      choose w hw using hcol
      refine ⟨∑ j, β j • w j, ?_⟩
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, ← hw, Finset.mul_sum, Finset.sum_smul, smul_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp only [smul_eq_mul]
      ring
    obtain ⟨Ws, hWs⟩ := hideal s hs
    obtain ⟨Wt, hWt⟩ := hideal t ht
    -- `s Wt = t Ws` by injectivity
    have hst : s • Wt = t • Ws := by
      apply hinj
      change Φ *ᵥ (s • Wt) = Φ *ᵥ (t • Ws)
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← hWs, ← hWt, smul_smul, smul_smul]
      congr 1
      ring
    -- so every coordinate of `Ws` is divisible by `s`
    have hdiv : ∀ r, ∃ V, Ws r = s * V := by
      intro r
      have h1 : t * Ws r ∈ Ideal.span {s} := by
        have := congrFun hst r
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [← this]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self s)
      obtain ⟨V, hV⟩ := Ideal.mem_span_singleton'.mp (hreg _ h1)
      exact ⟨V, by rw [← hV, mul_comm]⟩
    choose V hV using hdiv
    have hWsV : Ws = s • V := by
      ext r
      simp [hV r]
    rw [hWsV, Matrix.mulVec_smul] at hWs
    -- cancel `s`, then `c`
    have hca : c • a = Φ *ᵥ V := by
      ext r
      have := congrFun hWs r
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      apply mul_left_cancel₀ hs0
      linear_combination this
    refine ⟨hc.unit⁻¹.val • V, ?_⟩
    change Φ *ᵥ (hc.unit⁻¹.val • V) = a
    rw [Matrix.mulVec_smul, ← hca, smul_smul]
    simp
end MohP3.HilbertBurch
