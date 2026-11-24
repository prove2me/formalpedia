-- Prove2me | solution 1 for GlobalTheory.KZ.ES.exists_conj_of_same_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:48.503472+00:00
-- url     : https://prove2.me/submissions/9d6fa601-403c-49cd-afc3-b57ff2943308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DiagMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
import Theorems.Thm_GlobalTheory_KZ_Betti_mem_potSub
import Theorems.Thm_GlobalTheory_KZ_Betti_mem_trivSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KZ.Betti.mem_potSub
attribute [local simp] GlobalTheory.KZ.Betti.mem_trivSub


section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
noncomputable section
namespace GlobalTheory.ValConj
open Finset
open scoped Pointwise
section tails
variable {L : Type} [Field L]
end tails
variable {F L : Type} [Field F] [Field L] [Algebra F L]
end GlobalTheory.ValConj
open scoped MatrixGroups TensorProduct in
open Matrix in
open Finset in
open scoped Pointwise in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
private lemma valuation_lt_one_iff_inv_not_mem' {L : Type} [Field L] (U : ValuationSubring L)
    (y : L) (h0 : y ≠ 0) : U.valuation y < 1 ↔ y⁻¹ ∉ U := by
  rw [← U.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))]
open scoped MatrixGroups TensorProduct in
open Matrix in
open Finset in
open scoped Pointwise in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
private lemma exists_normalized_integral_relation {F L : Type} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (U : ValuationSubring L) (x : L) :
    ∃ (n k : ℕ) (a : ℕ → F), k ≤ n ∧ (∀ j, algebraMap F L (a j) ∈ U) ∧
      (∀ j, k < j → U.valuation (algebraMap F L (a j)) < 1) ∧ a k = 1 ∧
      ∑ j ∈ Finset.range (n + 1), algebraMap F L (a j) * x ^ j = 0 := by
  classical
  set p := minpoly F x with hp
  have hp0 : p ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
  set n := p.natDegree
  let c : ℕ → F := fun j => p.coeff j
  let w : ℕ → _ := fun j => U.valuation (algebraMap F L (c j))
  let s := (Finset.range (n + 1)).filter fun j => c j ≠ 0
  have hs : s.Nonempty := ⟨n, by
    simp only [s, c, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Polynomial.leadingCoeff_ne_zero.2 hp0⟩⟩
  let M := s.sup' hs w
  let T := s.filter fun j => w j = M
  have hT : T.Nonempty := by
    obtain ⟨j, hj, hjM⟩ := Finset.exists_mem_eq_sup' hs w
    exact ⟨j, Finset.mem_filter.2 ⟨hj, hjM.symm⟩⟩
  let k := T.max' hT
  have hkT : k ∈ T := T.max'_mem hT
  have hks : k ∈ s := (Finset.mem_filter.1 hkT).1
  have hkM : w k = M := (Finset.mem_filter.1 hkT).2
  have hck : c k ≠ 0 := (Finset.mem_filter.1 hks).2
  have hkn : k ≤ n := by have := (Finset.mem_filter.1 hks).1; simp at this; omega
  have hwk : w k ≠ 0 := by simp [w, hck]
  have hle : ∀ j, w j ≤ w k := by
    intro j
    by_cases hcj : c j = 0
    · simp [w, hcj]
    · have hjn : j ≤ n := by
        by_contra h
        exact hcj (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
      rw [hkM]
      exact Finset.le_sup' w (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hcj⟩)
  have hlt : ∀ j, k < j → w j < w k := by
    intro j hj
    by_cases hcj : c j = 0
    · simp only [w, hcj, map_zero]; exact zero_lt_iff.2 hwk
    · refine lt_of_le_of_ne (hle j) fun h => ?_
      have hjn : j ≤ n := by
        by_contra h'
        exact hcj (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
      have hjT : j ∈ T := Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hcj⟩, h.trans hkM⟩
      exact absurd (T.le_max' j hjT) (by omega)
  refine ⟨n, k, fun j => c j / c k, hkn, fun j => ?_, fun j hj => ?_, div_self hck, ?_⟩
  · rw [← U.valuation_le_one_iff, map_div₀, map_div₀]
    exact div_le_one_of_le₀ (hle j) zero_le'
  · rw [map_div₀, map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.2 hwk)).2 (hlt j hj)
  · have h0 : Polynomial.aeval x p = 0 := minpoly.aeval F x
    rw [Polynomial.aeval_eq_sum_range] at h0
    have : ∑ j ∈ Finset.range (n + 1), algebraMap F L (c j / c k) * x ^ j =
        (∑ j ∈ Finset.range (n + 1), p.coeff j • x ^ j) * (algebraMap F L (c k))⁻¹ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_div₀, Algebra.smul_def]
      ring
    rw [this, h0, zero_mul]
open scoped MatrixGroups TensorProduct in
open Matrix in
open Finset in
open scoped Pointwise in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
private lemma sum_range_succ_eq_lower_add_mid_add_upper {L : Type} [Field L] (f : ℕ → L) (n k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ Finset.range (n + 1), f j =
      ∑ j ∈ Finset.range k, f j + f k + ∑ j ∈ Finset.Ico (k + 1) (n + 1), f j := by
  rw [← Finset.sum_range_add_sum_Ico f (by omega : k ≤ n + 1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : k < n + 1), add_assoc]
open scoped MatrixGroups TensorProduct in
open Matrix in
open Finset in
open scoped Pointwise in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
private lemma valuation_sum_lower_div_pow_eq_one_and_lt_one {L : Type} [Field L] (U U' : ValuationSubring L) (n k : ℕ)
    (a : ℕ → L) (x : L) (hk : k ≤ n) (hxU : x ∈ U) (hxU' : x ∉ U') (ha : ∀ j, a j ∈ U)
    (ha' : ∀ j, a j ∈ U') (hbig : ∀ j, k < j → U.valuation (a j) < 1) (hak : a k = 1)
    (hrel : ∑ j ∈ Finset.range (n + 1), a j * x ^ j = 0) :
    U.valuation (∑ j ∈ Finset.range k, a j * x ^ j / x ^ k) = 1 ∧
      U'.valuation (∑ j ∈ Finset.range k, a j * x ^ j / x ^ k) < 1 := by
  have hx : x ≠ 0 := fun h => hxU' (h ▸ zero_mem U')
  have hrel' : ∑ j ∈ Finset.range (n + 1), a j * x ^ j / x ^ k = 0 := by
    rw [← Finset.sum_div, hrel, zero_div]
  rw [sum_range_succ_eq_lower_add_mid_add_upper _ n k hk, hak, one_mul, div_self (pow_ne_zero _ hx)] at hrel'
  constructor
  · have ht : U.valuation (∑ j ∈ Finset.Ico (k + 1) (n + 1), a j * x ^ j / x ^ k) < 1 := by
      refine Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
      have hj' : k < j := by simp at hj; omega
      rw [mul_div_assoc, div_eq_mul_inv, ← pow_sub₀ x hx hj'.le, map_mul]
      have h1 : U.valuation (x ^ (j - k)) ≤ 1 :=
        (U.valuation_le_one_iff _).2 (pow_mem hxU _)
      calc U.valuation (a j) * U.valuation (x ^ (j - k)) ≤ U.valuation (a j) * 1 := by
            gcongr
        _ < 1 := by rw [mul_one]; exact hbig j hj'
    have : ∑ j ∈ Finset.range k, a j * x ^ j / x ^ k =
        -(1 + ∑ j ∈ Finset.Ico (k + 1) (n + 1), a j * x ^ j / x ^ k) := by
      linear_combination hrel'
    rw [this, Valuation.map_neg, Valuation.map_one_add_of_lt _ ht]
  · have hxinv : x⁻¹ ∈ U' := (U'.mem_or_inv_mem x).resolve_left hxU'
    have hxinv' : U'.valuation x⁻¹ < 1 := by
      rw [map_inv₀]
      have : 1 < U'.valuation x := by
        by_contra h
        exact hxU' ((U'.valuation_le_one_iff _).1 (not_lt.1 h))
      exact inv_lt_one_of_one_lt₀ this
    refine Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    have hj' : j < k := by simpa using hj
    have : a j * x ^ j / x ^ k = a j * x⁻¹ ^ (k - j) := by
      rw [inv_pow, pow_sub₀ x hx hj'.le, mul_div_assoc]
      field_simp
    rw [this, map_mul, map_pow]
    have h1 : U'.valuation (a j) ≤ 1 := (U'.valuation_le_one_iff _).2 (ha' j)
    calc U'.valuation (a j) * U'.valuation x⁻¹ ^ (k - j) ≤ 1 * U'.valuation x⁻¹ ^ (k - j) := by
          gcongr
      _ = U'.valuation x⁻¹ ^ (k - j) := one_mul _
      _ < 1 := pow_lt_one₀ zero_le' hxinv' (by omega)
open scoped MatrixGroups TensorProduct in
open Matrix in
open Finset in
open scoped Pointwise in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
private lemma sum_lower_div_pow_mem_of_normalized_relation {L : Type} [Field L] (U : ValuationSubring L) (n k : ℕ) (a : ℕ → L)
    (z : L) (hz : z ≠ 0) (hk : k ≤ n) (ha : ∀ j, a j ∈ U) (hak : a k = 1)
    (hrel : ∑ j ∈ Finset.range (n + 1), a j * z ^ j = 0) :
    ∑ j ∈ Finset.range k, a j * z ^ j / z ^ k ∈ U := by
  have hrel' : ∑ j ∈ Finset.range (n + 1), a j * z ^ j / z ^ k = 0 := by
    rw [← Finset.sum_div, hrel, zero_div]
  rw [sum_range_succ_eq_lower_add_mid_add_upper _ n k hk, hak, one_mul, div_self (pow_ne_zero _ hz)] at hrel'
  by_cases hzU : z ∈ U
  · have hbig : ∑ j ∈ Finset.Ico (k + 1) (n + 1), a j * z ^ j / z ^ k ∈ U := by
      refine U.toSubring.sum_mem fun j hj => ?_
      have hj' : k ≤ j := by simp at hj; omega
      rw [mul_div_assoc, div_eq_mul_inv, ← pow_sub₀ z hz hj']
      exact mul_mem (ha j) (pow_mem hzU _)
    have : ∑ j ∈ Finset.range k, a j * z ^ j / z ^ k =
        -(1 + ∑ j ∈ Finset.Ico (k + 1) (n + 1), a j * z ^ j / z ^ k) := by
      linear_combination hrel'
    rw [this]
    exact neg_mem (add_mem (one_mem _) hbig)
  · have hzinv : z⁻¹ ∈ U := (U.mem_or_inv_mem z).resolve_left hzU
    refine U.toSubring.sum_mem fun j hj => ?_
    have hj' : j ≤ k := by simp at hj; omega
    have : a j * z ^ j / z ^ k = a j * z⁻¹ ^ (k - j) := by
      rw [inv_pow, pow_sub₀ z hz hj', mul_div_assoc]
      field_simp
    rw [this]
    exact mul_mem (ha j) (pow_mem hzinv _)
open scoped MatrixGroups TensorProduct in
open Matrix in
open Finset in
open scoped Pointwise in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
private lemma mem_of_mem_of_inv_core_mem [FiniteDimensional F L] (W₁ W₂ U U' : ValuationSubring L)
    (hUW₁ : ∀ f : F, algebraMap F L f ∈ U → algebraMap F L f ∈ W₁)
    (hUW₂ : ∀ f : F, algebraMap F L f ∈ U → algebraMap F L f ∈ W₂)
    (hUU' : ∀ f : F, algebraMap F L f ∈ U → algebraMap F L f ∈ U')
    (hcen : ∀ s ∈ _root_.GlobalTheory.ValConj.core F W₁ W₂, s ≠ 0 → s⁻¹ ∈ U → s⁻¹ ∈ U')
    (x : L) (hx : x ∈ U) : x ∈ U' := by
  by_contra hx'
  obtain ⟨n, k, a, hk, ha, hbig, hak, hrel⟩ := exists_normalized_integral_relation (F := F) U x
  have hx0 : x ≠ 0 := fun h => hx' (h ▸ zero_mem U')
  obtain ⟨h1, h2⟩ := valuation_sum_lower_div_pow_eq_one_and_lt_one U U' n k (fun j => algebraMap F L (a j)) x hk hx hx' ha
    (fun j => hUU' _ (ha j)) hbig (by simp [hak]) hrel
  set s := ∑ j ∈ Finset.range k, algebraMap F L (a j) * x ^ j / x ^ k with hs
  have hsS : s ∈ _root_.GlobalTheory.ValConj.core F W₁ W₂ := by
    intro σ
    have hσs : σ s = ∑ j ∈ Finset.range k, algebraMap F L (a j) * σ x ^ j / σ x ^ k := by
      simp [hs, map_sum, map_div₀, map_mul, map_pow, AlgEquiv.commutes]
    have hσrel : ∑ j ∈ Finset.range (n + 1), algebraMap F L (a j) * σ x ^ j = 0 := by
      have := congrArg σ hrel
      simpa [map_sum, map_mul, map_pow, AlgEquiv.commutes] using this
    have hσx : σ x ≠ 0 := by simpa using hx0
    rw [hσs]
    exact ⟨sum_lower_div_pow_mem_of_normalized_relation W₁ n k _ (σ x) hσx hk (fun j => hUW₁ _ (ha j)) (by simp [hak]) hσrel,
      sum_lower_div_pow_mem_of_normalized_relation W₂ n k _ (σ x) hσx hk (fun j => hUW₂ _ (ha j)) (by simp [hak]) hσrel⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hsU : s⁻¹ ∈ U := by
    rw [← U.valuation_le_one_iff, map_inv₀, h1, inv_one]
  exact (valuation_lt_one_iff_inv_not_mem' U' s hs0).1 h2 (hcen s hsS hs0 hsU)
end
end

set_option autoImplicit false
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open Finset
open scoped Pointwise
variable {F L : Type} [Field F] [Field L] [Algebra F L]
open scoped Pointwise
namespace _root_.GlobalTheory.KZ.ES
theorem _root_.solution : ∀ (F L : Type) [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (W₁ W₂ : ValuationSubring L),
    (∀ a : F, algebraMap F L a ∈ W₁ ↔ algebraMap F L a ∈ W₂) →
      ∃ σ : L ≃ₐ[F] L, ∀ x : L, σ x ∈ W₂ ↔ x ∈ W₁ := by
  intro F L _ _ _ _ _ W₁ W₂ hW
  classical
  set S := _root_.GlobalTheory.ValConj.core F W₁ W₂ with hSdef
  have hS₁ : S ≤ W₁.toSubring := fun y hy => by simpa using (hy 1).1
  have hS₂ : S ≤ W₂.toSubring := fun y hy => by simpa using (hy 1).2
  let A := FixedPoints.subring S (L ≃ₐ[F] L)
  haveI : Algebra.IsInvariant A S (L ≃ₐ[F] L) :=
    (Algebra.isInvariant_iff _ _ _).2 fun b hb => ⟨⟨b, hb⟩, rfl⟩
  haveI : SMulCommClass (L ≃ₐ[F] L) A S := ⟨fun g a s => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    exact congrArg (· * g • s) (a.2 g)⟩
  have hcentre : ∀ (W : ValuationSubring L) (h : S ≤ W.toSubring) (s : S),
      s ∈ _root_.GlobalTheory.ValConj.centre S W h ↔ W.valuation (s : L) < 1 :=
    fun W h s => W.valuation_lt_one_iff _
  have hcoe : ∀ (g : L ≃ₐ[F] L) (s : S), ((g • s : S) : L) = g (s : L) := fun _ _ => rfl
  have hunder : Ideal.under A (_root_.GlobalTheory.ValConj.centre S W₁ hS₁) =
      Ideal.under A (_root_.GlobalTheory.ValConj.centre S W₂ hS₂) := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap]
    rw [hcentre, hcentre]
    have hfix : ∀ σ : L ≃ₐ[F] L, σ ((a : S) : L) = ((a : S) : L) := fun σ => by
      rw [← hcoe, a.2 σ]
    obtain ⟨f, hf⟩ := IntermediateField.mem_bot.1 (((IsGalois.mem_bot_iff_fixed _).2 hfix))
    change W₁.valuation ((a : S) : L) < 1 ↔ W₂.valuation ((a : S) : L) < 1
    rw [← hf]
    by_cases hf0 : f = 0
    · simp [hf0]
    have h0 : algebraMap F L f ≠ 0 := by simpa using hf0
    rw [valuation_lt_one_iff_inv_not_mem' _ _ h0, valuation_lt_one_iff_inv_not_mem' _ _ h0,
      ← map_inv₀, hW]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A S (L ≃ₐ[F] L) _ _ hunder
  have hcen : ∀ s ∈ S, s ≠ 0 → (s⁻¹ ∈ W₂ ↔ (g⁻¹ s)⁻¹ ∈ W₁) := by
    intro s hs hs0
    have h := congrArg (fun I => (⟨s, hs⟩ : S) ∈ I) hg
    simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem, eq_iff_iff] at h
    rw [hcentre, hcentre, hcoe] at h
    have hgs0 : g⁻¹ s ≠ 0 := by simpa using hs0
    rw [valuation_lt_one_iff_inv_not_mem' _ _ hs0, valuation_lt_one_iff_inv_not_mem' _ _ hgs0] at h
    exact not_iff_not.1 h
  have hgF : ∀ (τ : L ≃ₐ[F] L) (f : F), τ (algebraMap F L f) = algebraMap F L f :=
    fun τ f => τ.commutes f
  refine ⟨g, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have := mem_of_mem_of_inv_core_mem (F := F) W₁ W₂ W₂ (W₁.comap (g⁻¹ : L ≃ₐ[F] L).toRingEquiv.toRingHom)
      (fun f hf => (hW f).2 hf) (fun f hf => hf)
      (fun f hf => by
        rw [ValuationSubring.mem_comap]
        simpa [hgF] using (hW f).2 hf)
      (fun s hs hs0 h => by
        rw [ValuationSubring.mem_comap]
        simpa [map_inv₀] using (hcen s hs hs0).1 h) (g x) hx
    rw [ValuationSubring.mem_comap] at this
    simpa using this
  · have := mem_of_mem_of_inv_core_mem (F := F) W₁ W₂ (W₁.comap (g⁻¹ : L ≃ₐ[F] L).toRingEquiv.toRingHom) W₂
      (fun f hf => by
        rw [ValuationSubring.mem_comap] at hf
        change (g⁻¹ : L ≃ₐ[F] L) (algebraMap F L f) ∈ W₁ at hf
        rwa [AlgEquiv.commutes] at hf)
      (fun f hf => by
        rw [ValuationSubring.mem_comap] at hf
        change (g⁻¹ : L ≃ₐ[F] L) (algebraMap F L f) ∈ W₁ at hf
        rw [AlgEquiv.commutes] at hf
        exact (hW f).1 hf)
      (fun f hf => by
        rw [ValuationSubring.mem_comap] at hf
        change (g⁻¹ : L ≃ₐ[F] L) (algebraMap F L f) ∈ W₁ at hf
        rw [AlgEquiv.commutes] at hf
        exact (hW f).1 hf)
      (fun s hs hs0 h => by
        rw [ValuationSubring.mem_comap] at h
        exact (hcen s hs hs0).2 (by simpa [map_inv₀] using h)) (g x) (by
        rw [ValuationSubring.mem_comap]
        simpa using hx)
    exact this
end _root_.GlobalTheory.KZ.ES
