-- Prove2me | solution 1 for GlobalTheory.CMTransference.cmApproximation_transference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:22.858955+00:00
-- url     : https://prove2.me/submissions/e7a2bc81-3a1d-4778-bd19-1237c95650d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
import Theorems.Thm_GlobalTheory_CMTransference_exists_short_family
import Theorems.Thm_GlobalTheory_CMTransference_finrank_eq_two_mul
import Theorems.Thm_GlobalTheory_CMTransference_exists_ratBasis
import Theorems.Thm_GlobalTheory_CMTransference_discr_smul_mem
import Theorems.Thm_GlobalTheory_CMTransference_norm_emb_sub_sq
import Theorems.Thm_GlobalTheory_CMTransference_norm_emb_sq
import Theorems.Thm_GlobalTheory_CMTransference_norm_embDual_sq
import Theorems.Thm_GlobalTheory_CMTransference_majSq_intCast_smul
import Theorems.Thm_GlobalTheory_CMTransference_normSq_le_majSq
import Theorems.Thm_GlobalTheory_CMTransference_inner_emb_embDual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BabaiCovering_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
namespace GlobalTheory.CMTransference
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.FD.CoveringRadiusStatement := by
  classical
  intro K _ _ _ ι _ _ r p S σ Q L la hσ hcm _ hla _ hQ hL hsd hmin μ
  set d : ℝ := |(discr K : ℝ)| with hd
  have hd0 : 0 < d := abs_pos.2 (by exact_mod_cast discr_ne_zero K)

  have hdual : ∀ z : Fin r → K, z ≠ 0 → (∀ y ∈ L, ∃ k : ℤ, traceForm S z y = k) →
      la ^ 2 ≤ d ^ 2 * majSq σ Q z := by
    intro z hz0 hz
    obtain ⟨i, hi⟩ := hmin _ (discr_smul_mem hsd hz)
      (smul_ne_zero (by exact_mod_cast discr_ne_zero K) hz0)
    have := hi.trans (normSq_le_majSq σ Q i _)
    rwa [majSq_intCast_smul, ← sq_abs (discr K : ℝ)] at this
  have hnd : (traceForm S).Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun z hz => ?_
    by_contra hz0
    obtain ⟨m, hm⟩ := exists_nat_gt (d ^ 2 * majSq σ Q z / la ^ 2)
    have hm0 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h1 := hdual (((m + 1 : ℕ) : ℚ)⁻¹ • z) (smul_ne_zero (inv_ne_zero hm0) hz0)
      (fun y _ => ⟨0, by rw [map_smul, LinearMap.smul_apply, hz y]; simp⟩)
    have h2 := majSq_intCast_smul σ Q ((m + 1 : ℕ) : ℤ) (((m + 1 : ℕ) : ℚ)⁻¹ • z)
    rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
      mul_inv_cancel₀ hm0, one_smul] at h2
    rw [div_lt_iff₀ (by positivity), h2] at hm
    push_cast at hm h1
    have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ((m : ℝ) + 1))
    have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h5 : 0 < la ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg h4 h4) h5.le, mul_nonneg h4 h5.le]
  obtain ⟨n, b, hb⟩ := exists_ratBasis hL
  let b' := (traceForm S).dualBasis hnd b
  have hV : finrank ℝ (EuclideanSpace ℂ (ι × Fin r)) = 2 * (Fintype.card ι * r) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
      Fintype.card_prod, Fintype.card_fin]
  have hK : finrank ℚ (Fin r → K) = 2 * (Fintype.card ι * r) := by
    rw [← Module.finrank_mul_finrank ℚ K, finrank_eq_two_mul hσ hcm, Module.finrank_fin_fun,
      mul_assoc]
  have hn : Fintype.card (Fin n) = finrank ℝ (EuclideanSpace ℂ (ι × Fin r)) := by
    rw [hV, ← hK, finrank_eq_card_basis b]
  have hinner : ∀ i j, inner ℝ (emb σ Q (b i)) (embDual p σ Q (b' j)) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [inner_emb_embDual hσ hcm hQ, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have hli : LinearIndependent ℝ fun i => emb σ Q (b i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun v => inner ℝ v (embDual p σ Q (b' j))) hg
    simpa [sum_inner, real_inner_smul_left, hinner] using this
  let B : Basis (Fin n) ℝ (EuclideanSpace ℂ (ι × Fin r)) :=
    Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hn).ge
  have hB : ∀ i, B i = emb σ Q (b i) := fun i => Basis.mk_apply _ _ _
  have hBmem : ∀ x ∈ span ℤ (Set.range B), ∃ l ∈ L, emb σ Q l = x := by
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    refine ⟨∑ i, c i • b i, (hb _).2
      (sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _), ?_⟩
    simp only [map_sum, map_zsmul, hB]
  have hlam : 0 < 2 * la / d := by positivity
  have hmin' : ∀ x ∈ span ℤ (Set.range fun j => embDual p σ Q (b' j)), x ≠ 0 →
      2 * la / d ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : ∑ i, c i • embDual p σ Q (b' i) = embDual p σ Q (∑ i, c i • b' i) := by
      simp only [map_sum, map_zsmul]
    rw [hw] at hx0 ⊢
    have h1 := hdual (∑ i, c i • b' i) (fun h => hx0 (by rw [h, map_zero])) (by
      intro y hy
      obtain ⟨e, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 ((hb y).1 hy)
      refine ⟨∑ i, c i * e i, ?_⟩
      have hbb : ∀ i j, traceForm S (b' i) (b j) = if j = i then 1 else 0 :=
        LinearMap.BilinForm.apply_dualBasis_left hnd b
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, hbb]
      simp [mul_comm])
    refine (pow_le_pow_iff_left₀ hlam.le (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_embDual_sq, div_pow, div_le_iff₀ (by positivity)]
    linarith
  have hinner' : ∀ i j, inner ℝ (B i) (embDual p σ Q (b' j)) = if i = j then (1 : ℝ) else 0 :=
    fun i j => by rw [hB, hinner]
  set t : ℕ := Fintype.card ι * r with ht
  have hμ : μ = 4 * (t : ℝ) ^ 3 * (d / la) := by
    simp only [μ, ReciprocityTheory.ChartRestriction.G.FD.d5mu, ht]
    push_cast
    ring
  have htt : (t : ℝ) ≤ (t : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero t
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hq : 0 < d / la := by positivity
  have hbound : ((2 * t : ℕ) : ℝ) ^ 2 / (2 * la / d) = 2 * (t : ℝ) ^ 2 * (d / la) := by
    push_cast
    field_simp
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨x, hx, hxb⟩ := ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering.cover B _ hinner' _ hlam hmin'
      (WithLp.toLp 2 fun ik : ι × Fin r => w ik.1 ik.2)
    obtain ⟨l, hl, rfl⟩ := hBmem x hx
    refine ⟨l, hl, ?_⟩
    rw [norm_emb_sub_sq, hV, hbound] at hxb
    refine hxb.trans ?_
    rw [hμ]
    push_cast
    have h1 := mul_le_mul_of_nonneg_right htt
      (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ 4 * (d / la) ^ 2)
    have h2 : (0 : ℝ) ≤ (t : ℝ) ^ 6 * (d / la) ^ 2 := by positivity
    nlinarith
  · obtain ⟨y, hy, hyli, hyn⟩ := exists_short_family B _ hinner' _ hlam hmin'
    choose l hl hly using fun i => hBmem _ (hy i)
    have hlZ : LinearIndependent ℤ l := by
      refine LinearIndependent.of_comp (emb σ Q).toIntLinearMap ?_
      have : (emb σ Q).toIntLinearMap ∘ l = y := funext hly
      rw [this]
      exact hyli.restrict_scalars' ℤ
    have hlQ : LinearIndependent ℚ l := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hlZ
    have hspQ : span ℚ (Set.range l) = ⊤ :=
      hlQ.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hV, hK])
    have hspK : ⊤ ≤ span K (Set.range l) := fun x _ =>
      span_le_restrictScalars ℚ K _ (hspQ ▸ mem_top)
    let c := (Basis.ofSpan hspK).reindex
      ((Basis.ofSpan hspK).indexEquiv (Pi.basisFun K (Fin r)))
    have hc : ∀ j, ∃ i, l i = c j := fun j =>
      Basis.ofSpan_subset hspK ⟨_, (Basis.reindex_apply _ _ j).symm⟩
    refine ⟨c, fun j => ?_, c.linearIndependent, fun j => ?_⟩
    · obtain ⟨i, hi⟩ := hc j
      exact hi ▸ hl i
    · obtain ⟨i, hi⟩ := hc j
      have h0 := hyn i
      rw [← hi, ← norm_emb_sq, hly]
      refine pow_le_pow_left₀ (norm_nonneg _) (h0.trans ?_) 2
      rw [hV, hbound, hμ]
      have h1 := mul_le_mul_of_nonneg_right htt
        (by positivity : (0 : ℝ) ≤ (t : ℝ) * (d / la))
      have h2 : (0 : ℝ) ≤ (t : ℝ) ^ 3 * (d / la) := by positivity
      nlinarith
end GlobalTheory.CMTransference
