-- Prove2me | solution 1 for GlobalTheory.InertField.isField_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:00:52.31561+00:00
-- url     : https://prove2.me/submissions/0561beed-aa90-4f21-b91c-6bb1c8076267

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Theorems.Thm_GlobalTheory_InertField_exists_not_congr
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


section
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
namespace GlobalTheory.InertField
open scoped TensorProduct in
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial in
private lemma exists_integer_valuation_sub_lt_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (s : F) (hs : v.valuation F s ≤ 1) :
    ∃ r : 𝓞 F, v.valuation F (s - algebraMap (𝓞 F) F r) < 1 := by
  classical
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) s
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hne := v.intValuation_ne_zero _ hd0
  have hex : ∃ m : ℕ, ¬ v.intValuation d ≤ WithZero.exp (-((m : ℕ) : ℤ)) := by
    refine ⟨(-(v.intValuation d).log).toNat + 1, fun h => ?_⟩
    nth_rewrite 1 [← WithZero.exp_log hne] at h
    rw [WithZero.exp_le_exp] at h
    omega
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact this (by simpa using v.intValuation_le_one d)
  obtain ⟨c, hc⟩ : ∃ c, Nat.find hex = c + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  have hdc : v.intValuation d ≤ WithZero.exp (-((c : ℕ) : ℤ)) := by
    have := Nat.find_min hex (show c < Nat.find hex by omega)
    simpa using this
  have hdc1 : ¬ v.intValuation d ≤ WithZero.exp (-((c + 1 : ℕ) : ℤ)) := by
    rw [← hc]; exact Nat.find_spec hex
  have hmemc : d ∈ v.asIdeal ^ c := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd]; exact hdc
  have hnmem : d ∉ v.asIdeal ^ (c + 1) := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd]; exact hdc1
  have hsup : Ideal.span {d} ⊔ v.asIdeal ^ (c + 1) = v.asIdeal ^ c := by
    have hle : Ideal.span {d} ⊔ v.asIdeal ^ (c + 1) ≤ v.asIdeal ^ c :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hmemc) (Ideal.pow_le_pow_right (by omega))
    obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
    have hdvd : v.asIdeal ^ c * L ∣ v.asIdeal ^ c * v.asIdeal := by
      rw [← hL, ← pow_succ]; exact Ideal.dvd_iff_le.mpr le_sup_right
    have hLv : L ∣ v.asIdeal := (mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)).mp hdvd
    have hvL : v.asIdeal ≤ L := Ideal.le_of_dvd hLv
    by_cases htop : L = ⊤
    · rw [hL, htop, Ideal.mul_top]
    · have hEq : v.asIdeal = L := v.isMaximal.eq_of_le htop hvL
      exfalso
      apply hnmem
      have hdL : d ∈ v.asIdeal ^ c * L := by
        rw [← hL]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self d)
      rwa [← hEq, ← pow_succ] at hdL
  have hnval : v.intValuation n ≤ v.intValuation d := by
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at hs
    have hpos : 0 < v.intValuation d := zero_lt_iff.mpr hne
    rwa [div_le_one₀ hpos] at hs
  have hn : n ∈ Ideal.span {d} ⊔ v.asIdeal ^ (c + 1) := by
    rw [hsup, ← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd]
    exact hnval.trans hdc
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hn
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨e, ?_⟩
  have heq : algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d - algebraMap (𝓞 F) F e
      = algebraMap (𝓞 F) F z / algebraMap (𝓞 F) F d := by
    rw [← hyz, map_add, map_mul]
    field_simp
    ring
  rw [heq, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    div_lt_one₀ (zero_lt_iff.mpr hne)]
  have hz' : v.intValuation z ≤ WithZero.exp (-((c + 1 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]; exact hz
  exact lt_of_le_of_lt hz' (not_le.mp hdc1)
open scoped TensorProduct in
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial in
private lemma exists_quadratic_root_mod_of_adic_root {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (b c : 𝓞 F) (β : v.adicCompletion F)
    (hβ : β ^ 2 + algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b) * β
      + algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) = 0) :
    ∃ r : 𝓞 F, r ^ 2 + b * r + c ∈ v.asIdeal := by
  have hvF : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    fun x => valuedAdicCompletion_eq_valuation' v x
  have hint : ∀ x : 𝓞 F,
      Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) ≤ 1 := by
    intro x
    rw [hvF, valuation_of_algebraMap]
    exact v.intValuation_le_one x
  set B := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b) with hB
  set C := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) with hC
  have hB1 : Valued.v B ≤ 1 := hint b
  have hC1 : Valued.v C ≤ 1 := hint c
  have hβ1 : Valued.v β ≤ 1 := by
    by_contra h
    push_neg at h
    have h0 : 0 < Valued.v β := lt_trans zero_lt_one h
    have hsq : β ^ 2 = -(B * β + C) := by linear_combination hβ
    have hle : Valued.v (B * β + C) ≤ Valued.v β := by
      apply Valuation.map_add_le
      · rw [map_mul]
        calc Valued.v B * Valued.v β ≤ 1 * Valued.v β := mul_le_mul_of_nonneg_right hB1 zero_le'
          _ = Valued.v β := one_mul _
      · exact hC1.trans h.le
    have hlt : Valued.v β < Valued.v (β ^ 2) := by
      rw [map_pow, pow_two]
      calc Valued.v β = Valued.v β * 1 := (mul_one _).symm
        _ < Valued.v β * Valued.v β := mul_lt_mul_of_pos_left h h0
    rw [hsq, Valuation.map_neg] at hlt
    exact absurd hle (not_le.mpr hlt)
  have hU : {x : v.adicCompletion F | Valued.v (β - x) < 1} ∈ nhds β := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simp at hy ⊢
    rw [← Valuation.map_neg, neg_sub]
    exact hy
  obtain ⟨s, hs⟩ := (denseRange_algebraMap F v).mem_nhds hU
  have hs' : Valued.v (β - algebraMap F (v.adicCompletion F) s) < 1 := hs
  have hs1 : v.valuation F s ≤ 1 := by
    rw [← hvF]
    have heq : algebraMap F (v.adicCompletion F) s
        = β - (β - algebraMap F (v.adicCompletion F) s) := by ring
    rw [heq]
    exact Valuation.map_sub_le _ hβ1 hs'.le
  obtain ⟨r, hr⟩ := exists_integer_valuation_sub_lt_one v s hs1
  refine ⟨r, ?_⟩
  set R := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) with hR
  have hδ : Valued.v (R - β) < 1 := by
    have heq : R - β = -(β - algebraMap F (v.adicCompletion F) s)
        - algebraMap F (v.adicCompletion F) (s - algebraMap (𝓞 F) F r) := by
      rw [map_sub]; ring
    rw [heq]
    apply Valuation.map_sub_lt
    · rw [Valuation.map_neg]; exact hs'
    · rwa [hvF]
  have hR1 : Valued.v R ≤ 1 := hint r
  have hval : Valued.v (R ^ 2 + B * R + C) < 1 := by
    have heq : R ^ 2 + B * R + C = (R - β) * (R + β + B) := by linear_combination hβ
    rw [heq, map_mul]
    have h2 : Valued.v (R + β + B) ≤ 1 :=
      Valuation.map_add_le _ (Valuation.map_add_le _ hR1 hβ1) hB1
    calc Valued.v (R - β) * Valued.v (R + β + B) ≤ Valued.v (R - β) * 1 :=
          mul_le_mul_of_nonneg_left h2 zero_le'
      _ < 1 := by rw [mul_one]; exact hδ
  have heq : R ^ 2 + B * R + C
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r ^ 2 + b * r + c)) := by
    simp only [hR, hB, hC, map_add, map_mul, map_pow]
  rw [heq, hvF, valuation_of_algebraMap] at hval
  exact (intValuation_lt_one_iff_mem v _).mp hval
end GlobalTheory.InertField
end

set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open GlobalTheory GlobalTheory.InertField
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
namespace GlobalTheory.InertField
namespace _root_.GlobalTheory.InertField
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime → IsField (v.adicCompletion F ⊗[F] E) := by
  intro F E _ _ _ _ _ h2 v hP
  classical
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.InertField.exists_not_congr h2 v
  set P := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) with hPdef
  have hai : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  set g := minpoly (𝓞 F) a with hg
  have hgm : g.Monic := minpoly.monic hai
  have hgE : minpoly (𝓞 F) (a : E) = g :=
    minpoly.algebraMap_eq (IsFractionRing.injective (𝓞 E) E) a
  have haiE : IsIntegral (𝓞 F) (a : E) := hai.map (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E)
  have hgF : minpoly F (a : E) = g.map (algebraMap (𝓞 F) F) := by
    rw [← hgE]; exact minpoly.isIntegrallyClosed_eq_field_fractions' F haiE
  have hdegF : (minpoly F (a : E)).natDegree = g.natDegree := by
    rw [hgF]; exact hgm.natDegree_map _
  have hle2 : g.natDegree ≤ 2 := by
    rw [← hdegF, ← h2]; exact minpoly.natDegree_le (a : E)
  have hpos : 0 < g.natDegree := minpoly.natDegree_pos hai
  have hne1 : g.natDegree ≠ 1 := by
    intro h1
    have hX : g = Polynomial.X + Polynomial.C (g.coeff 0) := by
      rw [hgm.as_sum, h1]; simp
    have h0 : Polynomial.aeval a g = 0 := minpoly.aeval _ _
    rw [hX] at h0
    simp at h0
    apply ha (-(g.coeff 0))
    rw [map_neg, sub_neg_eq_add, h0]
    exact P.zero_mem
  have hdeg : g.natDegree = 2 := by omega
  set b := g.coeff 1 with hb
  set c := g.coeff 0 with hc
  have hrel : a ^ 2 + algebraMap (𝓞 F) (𝓞 E) b * a + algebraMap (𝓞 F) (𝓞 E) c = 0 := by
    have h0 : Polynomial.aeval a g = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one] at h0
    have hlc : g.coeff 2 = 1 := by rw [← hdeg]; exact hgm.coeff_natDegree
    rw [hlc, one_smul, Algebra.smul_def, Algebra.smul_def] at h0
    linear_combination h0
  have hnoroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal := by
    intro r hr
    have hmem := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hr
    have hfac : algebraMap (𝓞 F) (𝓞 E) (r ^ 2 + b * r + c)
        = (algebraMap (𝓞 F) (𝓞 E) r - a)
          * (algebraMap (𝓞 F) (𝓞 E) r + algebraMap (𝓞 F) (𝓞 E) b + a) := by
      simp only [map_add, map_mul, map_pow]
      linear_combination hrel
    rw [hfac] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · apply ha r
      rw [← neg_sub]
      exact P.neg_mem h
    · apply ha (-(r + b))
      rw [map_neg, map_add, sub_neg_eq_add]
      convert h using 1
      ring
  have hnotF : ∀ s : F, (a : E) ≠ algebraMap F E s := by
    intro s hs
    have h1 := minpoly.eq_X_sub_C E s
    rw [← hs] at h1
    rw [h1, Polynomial.natDegree_X_sub_C] at hdegF
    omega
  have hli : LinearIndependent F ![(1 : E), (a : E)] := by
    rw [LinearIndependent.pair_iff]
    intro x y hxy
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hxy
    by_cases hy : y = 0
    · subst hy
      simp at hxy
      exact ⟨hxy, rfl⟩
    · exfalso
      apply hnotF (-x / y)
      have hy' : algebraMap F E y ≠ 0 := (_root_.map_ne_zero _).mpr hy
      rw [map_div₀, map_neg]
      field_simp
      linear_combination hxy
  set Bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2]) with hBs
  set TB := Algebra.TensorProduct.basis (v.adicCompletion F) Bs with hTB
  set α : v.adicCompletion F ⊗[F] E := (1 : v.adicCompletion F) ⊗ₜ[F] (a : E) with hαdef
  set B := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b) with hB
  set C := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) with hC
  have hrelE : (a : E) ^ 2 + algebraMap F E (algebraMap (𝓞 F) F b) * (a : E)
      + algebraMap F E (algebraMap (𝓞 F) F c) = 0 := by
    have h := congrArg (algebraMap (𝓞 E) E) hrel
    rw [map_add, map_add, map_mul, map_pow, map_zero,
      ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E,
      ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E,
      IsScalarTower.algebraMap_apply (𝓞 F) F E,
      IsScalarTower.algebraMap_apply (𝓞 F) F E] at h
    exact h
  have hα : α ^ 2 + algebraMap (v.adicCompletion F) _ B * α
      + algebraMap (v.adicCompletion F) _ C = 0 := by
    have h := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := v.adicCompletion F)
      (B := E)) hrelE
    rw [map_add, map_add, map_mul, map_pow, map_zero, AlgHom.commutes, AlgHom.commutes,
      Algebra.TensorProduct.includeRight_apply] at h
    rw [hB, hC, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact h
  have hdecomp : ∀ z : v.adicCompletion F ⊗[F] E, z = algebraMap (v.adicCompletion F) _ (TB.repr z 0)
      + algebraMap (v.adicCompletion F) _ (TB.repr z 1) * α := by
    intro z
    conv_lhs => rw [← TB.sum_repr z]
    rw [Fin.sum_univ_two, hTB, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.basis_apply, hBs, coe_basisOfLinearIndependentOfCardEqFinrank]
    simp [Algebra.smul_def, hαdef, ← Algebra.TensorProduct.one_def]
  refine ⟨⟨0, 1, ?_⟩, fun x y => mul_comm x y, ?_⟩
  · intro h01
    have h1 : TB 0 = 1 := by
      rw [hTB, Algebra.TensorProduct.basis_apply, hBs,
        coe_basisOfLinearIndependentOfCardEqFinrank]
      simp [Algebra.TensorProduct.one_def]
    exact TB.ne_zero 0 (h1.trans h01.symm)
  · intro z hz
    have hz' := hdecomp z
    set x := TB.repr z 0 with hx
    set y := TB.repr z 1 with hy
    set N := x ^ 2 - B * x * y + C * y ^ 2 with hN
    have hN0 : N ≠ 0 := by
      intro hN0
      rw [hN] at hN0
      by_cases hy0 : y = 0
      · apply hz
        rw [hy0] at hN0
        have hx0 : x = 0 := by simpa using hN0
        rw [hz', hx0, hy0]
        simp
      · obtain ⟨r, hr⟩ := exists_quadratic_root_mod_of_adic_root v b c (-x / y) (by
          rw [← hB, ← hC]
          field_simp
          linear_combination hN0)
        exact hnoroot r hr
    refine ⟨(algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) x
      - algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) B
        * algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) y
      - algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) y * α)
      * algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) N⁻¹, ?_⟩
    have hzN : z * (algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) x
        - algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) B
          * algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) y
        - algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) y * α)
        = algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) N := by
      rw [hz', hN]
      simp only [map_add, map_sub, map_mul, map_pow]
      linear_combination
        (-(algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) y) ^ 2) * hα
    rw [← mul_assoc, hzN, ← map_mul, mul_inv_cancel₀ hN0, map_one]
end _root_.GlobalTheory.InertField
end GlobalTheory.InertField
