-- Prove2me | solution 1 for GlobalTheory.Mem.PartialZeta.im_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:53.340828+00:00
-- url     : https://prove2.me/submissions/ac136e7e-7c8c-466d-b0ad-33b1d24f1ee3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.PartialZeta
theorem _root_.solution [IsTotallyComplex K] (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) :
    (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ≠ 0 := by
  intro him
  have h2 : Module.finrank ℚ K = 2 := by
    rw [← RingOfIntegers.rank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h
    exact b.ne_zero 0 (RingOfIntegers.ext (by simpa using h))
  have ha0 : φ (b 0 : K) ≠ 0 := (map_ne_zero φ).2 hb0
  have hca0 : starRingEnd ℂ (φ (b 0 : K)) ≠ 0 := (map_ne_zero _).2 ha0
  set y : K := (b 1 : K) / (b 0 : K) with hy
  have hφy : (φ y).im = 0 := by
    have hq : φ y = (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)) /
        (Complex.normSq (φ (b 0 : K)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_div_mul_left _ _ hca0, hy, map_div₀]
    rw [hq, Complex.div_ofReal_im, him, zero_div]
  by_cases hyq : y ∈ Set.range (algebraMap ℚ K)
  · obtain ⟨q, hq⟩ := hyq
    have hK : (q.den : K) * (b 1 : K) = (q.num : K) * (b 0 : K) := by
      have hd : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
      have h1 : (b 1 : K) = (q : K) * (b 0 : K) := by
        rw [← eq_ratCast (algebraMap ℚ K) q, hq, hy, div_mul_cancel₀ _ hb0]
      rw [h1, Rat.cast_def]
      field_simp
    have hz : (-q.num) • b 0 + ((q.den : ℤ)) • b 1 = 0 := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.coe_eq_algebraMap] at hK ⊢
      simp only [zsmul_eq_mul, map_add, map_mul, map_intCast, map_neg, map_zero, map_natCast]
      push_cast at hK ⊢
      linear_combination hK
    have := Fintype.linearIndependent_iff.1 b.linearIndependent ![-q.num, (q.den : ℤ)]
      (by simpa [Fin.sum_univ_two] using hz) 1
    simp at this
  · have hli : LinearIndependent ℚ ![(1 : K), y] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have hg1 : g 1 = 0 := by
        by_contra hne
        apply hyq
        refine ⟨-(g 0) / g 1, ?_⟩
        rw [eq_ratCast]
        push_cast
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hg
        rw [div_eq_iff (by exact_mod_cast hne)]
        linear_combination -hg
      have hg0 : g 0 = 0 := by
        rw [hg1, zero_smul, add_zero, smul_eq_zero] at hg
        simpa using hg
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
    have hreal : ∀ x : K, (φ x).im = 0 := by
      intro x
      have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), y]) := htop ▸ Submodule.mem_top
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hx
      simp [Fin.sum_univ_two, Rat.smul_def, hφy]
    have hR : ComplexEmbedding.IsReal φ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.2 (hreal x)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex
      (InfinitePlace.mk φ))) (InfinitePlace.isReal_mk_iff.2 hR)
end GlobalTheory.Mem.PartialZeta
