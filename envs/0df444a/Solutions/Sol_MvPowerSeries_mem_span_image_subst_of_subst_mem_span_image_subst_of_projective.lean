-- Prove2me | solution 1 for MvPowerSeries.mem_span_image_subst_of_subst_mem_span_image_subst_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c50e3b08-71d9-5552-a9d6-3b9733621d64

import Mathlib
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_mem_span_image_subst_of_subst_mem_span_image_subst_of_projective

set_option autoImplicit false

namespace K2Transfer

open MvPowerSeries
open scoped Classical

section Exponents

variable {α β : Type*}

theorem sumElim_ext {f f' : α →₀ ℕ} {g g' : β →₀ ℕ} :
    f.sumElim g = f'.sumElim g' ↔ f = f' ∧ g = g' := by
  constructor
  · intro h
    refine ⟨Finsupp.ext fun x => ?_, Finsupp.ext fun y => ?_⟩
    · have := congrArg (fun D => D (Sum.inl x)) h
      simpa only [Finsupp.sumElim_inl] using this
    · have := congrArg (fun D => D (Sum.inr y)) h
      simpa only [Finsupp.sumElim_inr] using this
  · rintro ⟨rfl, rfl⟩; rfl

noncomputable def fstE (D : α ⊕ β →₀ ℕ) : α →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp D).1
noncomputable def sndE (D : α ⊕ β →₀ ℕ) : β →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp D).2

theorem fstE_apply (D : α ⊕ β →₀ ℕ) (x : α) : fstE D x = D (Sum.inl x) :=
  Finsupp.fst_sumFinsuppEquivProdFinsupp D x
theorem sndE_apply (D : α ⊕ β →₀ ℕ) (y : β) : sndE D y = D (Sum.inr y) :=
  Finsupp.snd_sumFinsuppEquivProdFinsupp D y

theorem sumElim_fstE_sndE (D : α ⊕ β →₀ ℕ) : (fstE D).sumElim (sndE D) = D := by
  ext v
  rcases v with x | y
  · rw [Finsupp.sumElim_inl, fstE_apply]
  · rw [Finsupp.sumElim_inr, sndE_apply]

theorem fstE_sumElim (f : α →₀ ℕ) (g : β →₀ ℕ) : fstE (f.sumElim g) = f := by
  ext x; rw [fstE_apply, Finsupp.sumElim_inl]
theorem sndE_sumElim (f : α →₀ ℕ) (g : β →₀ ℕ) : sndE (f.sumElim g) = g := by
  ext y; rw [sndE_apply, Finsupp.sumElim_inr]

theorem sumElim_add (f f' : α →₀ ℕ) (g g' : β →₀ ℕ) :
    f.sumElim g + f'.sumElim g' = (f + f').sumElim (g + g') := by
  ext v
  rcases v with x | y
  · simp only [Finsupp.add_apply, Finsupp.sumElim_inl]
  · simp only [Finsupp.add_apply, Finsupp.sumElim_inr]

theorem sumElim_le_iff (f f' : α →₀ ℕ) (g g' : β →₀ ℕ) :
    f.sumElim g ≤ f'.sumElim g' ↔ f ≤ f' ∧ g ≤ g' := by
  simp only [Finsupp.le_iff, Finsupp.mem_support_iff, ne_eq]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have := h (Sum.inl x) (by rwa [Finsupp.sumElim_inl])
      simpa only [Finsupp.sumElim_inl] using this
    · have := h (Sum.inr y) (by rwa [Finsupp.sumElim_inr])
      simpa only [Finsupp.sumElim_inr] using this
  · rintro ⟨hf, hg⟩ v hv
    rcases v with x | y
    · simp only [Finsupp.sumElim_inl] at hv ⊢; exact hf x hv
    · simp only [Finsupp.sumElim_inr] at hv ⊢; exact hg y hv

theorem sumElim_tsub (f f' : α →₀ ℕ) (g g' : β →₀ ℕ) :
    f.sumElim g - f'.sumElim g' = (f - f').sumElim (g - g') := by
  ext v
  rcases v with x | y
  · simp only [Finsupp.tsub_apply, Finsupp.sumElim_inl]
  · simp only [Finsupp.tsub_apply, Finsupp.sumElim_inr]

theorem sumElim_zero_zero : (0 : α →₀ ℕ).sumElim (0 : β →₀ ℕ) = 0 := by
  ext v; rcases v with x | y <;> simp

theorem eq_embDomain_inr (g : β →₀ ℕ) :
    (0 : α →₀ ℕ).sumElim g = Finsupp.embDomain Function.Embedding.inr g := by
  ext v
  rcases v with x | y
  · rw [Finsupp.sumElim_inl, Finsupp.embDomain_notin_range]
    · rfl
    · rintro ⟨y, hy⟩; cases hy
  · rw [Finsupp.sumElim_inr]
    exact (Finsupp.embDomain_apply_self Function.Embedding.inr g y).symm

theorem eq_embDomain_inl (f : α →₀ ℕ) :
    f.sumElim (0 : β →₀ ℕ) = Finsupp.embDomain Function.Embedding.inl f := by
  ext v
  rcases v with x | y
  · rw [Finsupp.sumElim_inl]
    exact (Finsupp.embDomain_apply_self Function.Embedding.inl f x).symm
  · rw [Finsupp.sumElim_inr, Finsupp.embDomain_notin_range]
    · rfl
    · rintro ⟨x, hx⟩; cases hx

theorem not_mem_range_mapDomain_inr {f : α →₀ ℕ} (g : β →₀ ℕ) (hf : f ≠ 0) :
    f.sumElim g ∉ Set.range (Finsupp.mapDomain (Sum.inr : β → α ⊕ β)) := by
  rintro ⟨g', hg'⟩
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h; push Not at h; exact hf (Finsupp.ext h)
  have h1 : (Finsupp.mapDomain Sum.inr g') (Sum.inl x : α ⊕ β) = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by rintro ⟨y, hy⟩; cases hy)
  rw [hg', Finsupp.sumElim_inl] at h1
  exact hx h1

theorem not_mem_range_mapDomain_inl (f : α →₀ ℕ) {g : β →₀ ℕ} (hg : g ≠ 0) :
    f.sumElim g ∉ Set.range (Finsupp.mapDomain (Sum.inl : α → α ⊕ β)) := by
  rintro ⟨f', hf'⟩
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra h; push Not at h; exact hg (Finsupp.ext h)
  have h1 : (Finsupp.mapDomain Sum.inl f') (Sum.inr y : α ⊕ β) = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; cases hx)
  rw [hf', Finsupp.sumElim_inr] at h1
  exact hy h1

end Exponents

section Matrix

variable {B : Type*} [CommRing B] {n m : ℕ}

noncomputable def M (a : Fin n → MvPowerSeries (Fin m) B) (μ : Fin m →₀ ℕ) (ν : Fin n →₀ ℕ) : B :=
  coeff μ (ν.prod fun j k => a j ^ k)

theorem M_row_finite {a : Fin n → MvPowerSeries (Fin m) B} (ha : HasSubst a) (μ : Fin m →₀ ℕ) :
    {ν : Fin n →₀ ℕ | M a μ ν ≠ 0}.Finite := by
  have h := coeff_subst_finite ha (fun _ => (1 : B) : MvPowerSeries (Fin n) B) μ
  refine h.subset fun ν hν => ?_
  simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq, M] at hν ⊢
  rwa [show coeff ν (fun _ => (1 : B) : MvPowerSeries (Fin n) B) = 1 from rfl, one_smul]

noncomputable def S {a : Fin n → MvPowerSeries (Fin m) B} (ha : HasSubst a) (μ : Fin m →₀ ℕ) :
    Finset (Fin n →₀ ℕ) := (M_row_finite ha μ).toFinset

theorem mem_S {a : Fin n → MvPowerSeries (Fin m) B} (ha : HasSubst a) {μ : Fin m →₀ ℕ} {ν : Fin n →₀ ℕ} :
    ν ∈ S ha μ ↔ M a μ ν ≠ 0 := by
  rw [S, Set.Finite.mem_toFinset]; rfl

theorem prod_X_pow_eq_monomial {σ τ : Type*} (ι : σ → τ) (ε : σ →₀ ℕ) (E : τ →₀ ℕ)
    (hE : ∀ t, E t = ∑ s ∈ ε.support, if ι s = t then ε s else 0) :
    (ε.prod fun s k => (X (ι s) : MvPowerSeries τ B) ^ k) = monomial E 1 := by
  classical
  have hE' : E = ∑ s ∈ ε.support, Finsupp.single (ι s) (ε s) := by
    ext t
    rw [hE, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.single_apply]
  rw [hE', Finsupp.prod]
  induction ε.support using Finset.induction_on with
  | empty => simp
  | insert s T hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs, ih, X_pow_eq, monomial_mul_monomial, one_mul]

end Matrix

section LayoutLast

variable {B : Type*} [CommRing B] {ω : Type*} [Finite ω] {n m : ℕ}

noncomputable def θL (ω : Type*) (a : Fin n → MvPowerSeries (Fin m) B) :
    ω ⊕ Fin n → MvPowerSeries (ω ⊕ Fin m) B :=
  Sum.elim (fun w => X (Sum.inl w)) (fun k => subst (fun j => (X (Sum.inr j) : MvPowerSeries (ω ⊕ Fin m) B)) (a k))

omit [Finite ω] in
theorem θL_inr (a : Fin n → MvPowerSeries (Fin m) B) (k : Fin n) :
    θL ω a (Sum.inr k) = rename (⇑(Function.Embedding.inr : Fin m ↪ ω ⊕ Fin m)) (a k) := by
  rw [θL, Sum.elim_inr, rename_eq_subst]; rfl

theorem hasSubst_θL {a : Fin n → MvPowerSeries (Fin m) B} (ha0 : ∀ k, constantCoeff (a k) = 0) :
    HasSubst (θL ω a) := by
  refine hasSubst_of_constantCoeff_zero fun v => ?_
  rcases v with w | k
  · rw [θL, Sum.elim_inl, constantCoeff_X]
  · rw [θL_inr, constantCoeff_rename, ha0]

omit [Finite ω] in
theorem coeff_prod_θL (a : Fin n → MvPowerSeries (Fin m) B)
    (ε ε' : ω →₀ ℕ) (ν : Fin n →₀ ℕ) (μ : Fin m →₀ ℕ) :
    coeff (ε'.sumElim μ) ((ε.sumElim ν).prod fun v k => θL ω a v ^ k) = if ε = ε' then M a μ ν else 0 := by
  classical
  rw [Finsupp.prod_sumElim]
  have h1 : (ε.prod ((fun v k => θL ω a v ^ k) ∘ Sum.inl)) = monomial (ε.sumElim (0 : Fin m →₀ ℕ)) 1 := by
    have : ((fun v k => θL ω a v ^ k) ∘ Sum.inl) = fun w k => (X (Sum.inl w) : MvPowerSeries (ω ⊕ Fin m) B) ^ k := by
      funext w k; simp [θL]
    rw [this]
    refine prod_X_pow_eq_monomial Sum.inl ε _ fun t => ?_
    rcases t with w | j
    · rw [Finsupp.sumElim_inl]
      simp only [Sum.inl.injEq, Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not]
      by_cases h : ε w = 0 <;> simp [h]
    · rw [Finsupp.sumElim_inr]
      simp
  have h2 : (ν.prod ((fun v k => θL ω a v ^ k) ∘ Sum.inr)) =
      rename (⇑(Function.Embedding.inr : Fin m ↪ ω ⊕ Fin m)) (ν.prod fun j k => a j ^ k) := by
    rw [Finsupp.prod, Finsupp.prod, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, map_pow, θL_inr]
  rw [h1, h2, coeff_monomial_mul, one_mul]
  by_cases h : ε = ε'
  · subst h
    have hle : ε.sumElim (0 : Fin m →₀ ℕ) ≤ ε.sumElim μ := (sumElim_le_iff _ _ _ _).mpr ⟨le_rfl, bot_le (a := μ)⟩
    rw [if_pos hle, if_pos rfl, sumElim_tsub, tsub_self, tsub_zero, eq_embDomain_inr, coeff_embDomain_rename]
    rfl
  · rw [if_neg h]
    by_cases hle : ε.sumElim (0 : Fin m →₀ ℕ) ≤ ε'.sumElim μ
    · rw [if_pos hle, sumElim_tsub, tsub_zero]
      apply coeff_rename_eq_zero
      have hle' : ε ≤ ε' := ((sumElim_le_iff _ _ _ _).mp hle).1
      have hne : ε' - ε ≠ 0 := fun h0 => h (le_antisymm hle' (tsub_eq_zero_iff_le.mp h0))
      exact not_mem_range_mapDomain_inr μ hne
    · rw [if_neg hle]

theorem coeff_subst_θL {a : Fin n → MvPowerSeries (Fin m) B} (ha0 : ∀ k, constantCoeff (a k) = 0)
    (V : MvPowerSeries (ω ⊕ Fin n) B) (ε : ω →₀ ℕ) (μ : Fin m →₀ ℕ) :
    coeff (ε.sumElim μ) (subst (θL ω a) V) =
      ∑ ν ∈ S (hasSubst_of_constantCoeff_zero ha0) μ, M a μ ν * coeff (ε.sumElim ν) V := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  rw [coeff_subst (hasSubst_θL ha0) V]
  have hsupp : (Function.support fun D : ω ⊕ Fin n →₀ ℕ =>
      coeff D V • coeff (ε.sumElim μ) (D.prod fun v k => θL ω a v ^ k)) ⊆
      ((S ha μ).image fun ν => ε.sumElim ν : Finset (ω ⊕ Fin n →₀ ℕ)) := by
    intro D hD
    rw [Function.mem_support, ← sumElim_fstE_sndE D, coeff_prod_θL] at hD
    rw [Finset.coe_image, Set.mem_image]
    by_cases h : fstE D = ε
    · refine ⟨sndE D, ?_, by rw [← h, sumElim_fstE_sndE]⟩
      rw [Finset.mem_coe, mem_S]
      rw [if_pos h] at hD
      exact fun h0 => hD (by rw [h0, smul_zero])
    · rw [if_neg h, smul_zero] at hD
      exact (hD rfl).elim
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image fun ν _ ν' _ h => (sumElim_ext.mp h).2]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_prod_θL, if_pos rfl, smul_eq_mul, mul_comm]

end LayoutLast

section LayoutFirst

variable {B : Type*} [CommRing B] {ω : Type*} [Finite ω] {n m : ℕ}

noncomputable def θF (ω : Type*) (a : Fin n → MvPowerSeries (Fin m) B) :
    Fin n ⊕ ω → MvPowerSeries (Fin m ⊕ ω) B :=
  Sum.elim (fun k => subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin m ⊕ ω) B)) (a k)) (fun t => X (Sum.inr t))

omit [Finite ω] in
theorem θF_inl (a : Fin n → MvPowerSeries (Fin m) B) (k : Fin n) :
    θF ω a (Sum.inl k) = rename (⇑(Function.Embedding.inl : Fin m ↪ Fin m ⊕ ω)) (a k) := by
  rw [θF, Sum.elim_inl, rename_eq_subst]; rfl

theorem hasSubst_θF {a : Fin n → MvPowerSeries (Fin m) B} (ha0 : ∀ k, constantCoeff (a k) = 0) :
    HasSubst (θF ω a) := by
  refine hasSubst_of_constantCoeff_zero fun v => ?_
  rcases v with k | t
  · rw [θF_inl, constantCoeff_rename, ha0]
  · rw [θF, Sum.elim_inr, constantCoeff_X]

omit [Finite ω] in
theorem coeff_prod_θF (a : Fin n → MvPowerSeries (Fin m) B)
    (δ δ' : ω →₀ ℕ) (ν : Fin n →₀ ℕ) (μ : Fin m →₀ ℕ) :
    coeff (μ.sumElim δ') ((ν.sumElim δ).prod fun v k => θF ω a v ^ k) = if δ = δ' then M a μ ν else 0 := by
  classical
  rw [Finsupp.prod_sumElim, mul_comm]
  have h1 : (δ.prod ((fun v k => θF ω a v ^ k) ∘ Sum.inr)) = monomial ((0 : Fin m →₀ ℕ).sumElim δ) 1 := by
    have : ((fun v k => θF ω a v ^ k) ∘ Sum.inr) = fun t k => (X (Sum.inr t) : MvPowerSeries (Fin m ⊕ ω) B) ^ k := by
      funext t k; simp [θF]
    rw [this]
    refine prod_X_pow_eq_monomial Sum.inr δ _ fun t => ?_
    rcases t with j | w
    · rw [Finsupp.sumElim_inl]
      simp
    · rw [Finsupp.sumElim_inr]
      simp only [Sum.inr.injEq, Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not]
      by_cases h : δ w = 0 <;> simp [h]
  have h2 : (ν.prod ((fun v k => θF ω a v ^ k) ∘ Sum.inl)) =
      rename (⇑(Function.Embedding.inl : Fin m ↪ Fin m ⊕ ω)) (ν.prod fun j k => a j ^ k) := by
    rw [Finsupp.prod, Finsupp.prod, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, map_pow, θF_inl]
  rw [h1, h2, coeff_monomial_mul, one_mul]
  by_cases h : δ = δ'
  · subst h
    have hle : (0 : Fin m →₀ ℕ).sumElim δ ≤ μ.sumElim δ := (sumElim_le_iff _ _ _ _).mpr ⟨bot_le (a := μ), le_rfl⟩
    rw [if_pos hle, if_pos rfl, sumElim_tsub, tsub_self, tsub_zero, eq_embDomain_inl, coeff_embDomain_rename]
    rfl
  · rw [if_neg h]
    by_cases hle : (0 : Fin m →₀ ℕ).sumElim δ ≤ μ.sumElim δ'
    · rw [if_pos hle, sumElim_tsub, tsub_zero]
      apply coeff_rename_eq_zero
      have hle' : δ ≤ δ' := ((sumElim_le_iff _ _ _ _).mp hle).2
      have hne : δ' - δ ≠ 0 := fun h0 => h (le_antisymm hle' (tsub_eq_zero_iff_le.mp h0))
      exact not_mem_range_mapDomain_inl μ hne
    · rw [if_neg hle]

theorem coeff_subst_θF {a : Fin n → MvPowerSeries (Fin m) B} (ha0 : ∀ k, constantCoeff (a k) = 0)
    (H : MvPowerSeries (Fin n ⊕ ω) B) (μ : Fin m →₀ ℕ) (δ : ω →₀ ℕ) :
    coeff (μ.sumElim δ) (subst (θF ω a) H) =
      ∑ ν ∈ S (hasSubst_of_constantCoeff_zero ha0) μ, M a μ ν * coeff (ν.sumElim δ) H := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  rw [coeff_subst (hasSubst_θF ha0) H]
  have hsupp : (Function.support fun D : Fin n ⊕ ω →₀ ℕ =>
      coeff D H • coeff (μ.sumElim δ) (D.prod fun v k => θF ω a v ^ k)) ⊆
      ((S ha μ).image fun ν => ν.sumElim δ : Finset (Fin n ⊕ ω →₀ ℕ)) := by
    intro D hD
    rw [Function.mem_support, ← sumElim_fstE_sndE D, coeff_prod_θF] at hD
    rw [Finset.coe_image, Set.mem_image]
    by_cases h : sndE D = δ
    · refine ⟨fstE D, ?_, by rw [← h, sumElim_fstE_sndE]⟩
      rw [Finset.mem_coe, mem_S]
      rw [if_pos h] at hD
      exact fun h0 => hD (by rw [h0, smul_zero])
    · rw [if_neg h, smul_zero] at hD
      exact (hD rfl).elim
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image fun ν _ ν' _ h => (sumElim_ext.mp h).1]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_prod_θF, if_pos rfl, smul_eq_mul, mul_comm]

end LayoutFirst

section Slices

variable {B : Type*} [CommRing B] {d q n : ℕ}

def sl (V : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B) (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ) :
    MvPowerSeries (Fin q) B :=
  fun γ => coeff ((δ.sumElim γ).sumElim ν) V

theorem coeff_sl (V : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B) (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ)
    (γ : Fin q →₀ ℕ) : coeff γ (sl V δ ν) = coeff ((δ.sumElim γ).sumElim ν) V := rfl

theorem sl_add (V W : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B) (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ) :
    sl (V + W) δ ν = sl V δ ν + sl W δ ν := by
  ext γ; simp only [coeff_sl, map_add]

theorem sl_sum {κ : Type*} (s : Finset κ) (V : κ → MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B)
    (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ) : sl (∑ k ∈ s, V k) δ ν = ∑ k ∈ s, sl (V k) δ ν := by
  ext γ; simp only [coeff_sl, map_sum]

theorem eq_of_sl_eq {V W : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B} (h : ∀ δ ν, sl V δ ν = sl W δ ν) :
    V = W := by
  ext E
  have := congrArg (coeff (sndE (fstE E))) (h (fstE (fstE E)) (sndE E))
  rwa [coeff_sl, coeff_sl, sumElim_fstE_sndE, sumElim_fstE_sndE] at this

noncomputable def ofSl (φ : (Fin d →₀ ℕ) → (Fin n →₀ ℕ) → MvPowerSeries (Fin q) B) :
    MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B :=
  fun E => coeff (sndE (fstE E)) (φ (fstE (fstE E)) (sndE E))

theorem sl_ofSl (φ : (Fin d →₀ ℕ) → (Fin n →₀ ℕ) → MvPowerSeries (Fin q) B) (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ) :
    sl (ofSl φ) δ ν = φ δ ν := by
  ext γ
  rw [coeff_sl]
  show coeff (sndE (fstE ((δ.sumElim γ).sumElim ν))) (φ (fstE (fstE ((δ.sumElim γ).sumElim ν))) (sndE _)) = _
  rw [fstE_sumElim, sndE_sumElim, fstE_sumElim, sndE_sumElim]

def ιE (d q n : ℕ) : Fin q ↪ (Fin d ⊕ Fin q) ⊕ Fin n :=
  ⟨fun l => Sum.inl (Sum.inr l), fun _ _ h => by simpa using h⟩

theorem subst_eq_rename_ιE (i : MvPowerSeries (Fin q) B) :
    subst (fun l => (X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B)) i = rename (⇑(ιE d q n)) i := by
  rw [rename_eq_subst]; rfl

theorem embDomain_ιE (γ : Fin q →₀ ℕ) :
    Finsupp.embDomain (ιE d q n) γ = (((0 : Fin d →₀ ℕ).sumElim γ).sumElim (0 : Fin n →₀ ℕ)) := by
  ext v
  rcases v with (x | l) | k
  · rw [Finsupp.sumElim_inl, Finsupp.sumElim_inl, Finsupp.embDomain_notin_range]
    · rfl
    · rintro ⟨l, hl⟩; cases hl
  · rw [Finsupp.sumElim_inl, Finsupp.sumElim_inr]
    exact Finsupp.embDomain_apply_self (ιE d q n) γ l
  · rw [Finsupp.sumElim_inr, Finsupp.embDomain_notin_range]
    · rfl
    · rintro ⟨l, hl⟩; cases hl

theorem coeff_rename_ιE (i : MvPowerSeries (Fin q) B) (δ : Fin d →₀ ℕ) (γ : Fin q →₀ ℕ) (ν : Fin n →₀ ℕ) :
    coeff ((δ.sumElim γ).sumElim ν) (rename (⇑(ιE d q n)) i) = if δ = 0 ∧ ν = 0 then coeff γ i else 0 := by
  split_ifs with h
  · rw [h.1, h.2, ← embDomain_ιE, coeff_embDomain_rename]
  · apply coeff_rename_eq_zero
    rintro ⟨γ', hγ'⟩
    rw [← Finsupp.embDomain_eq_mapDomain, embDomain_ιE, sumElim_ext, sumElim_ext] at hγ'
    exact h ⟨hγ'.1.1.symm, hγ'.2.symm⟩

theorem sl_mul_rename (h : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B) (i : MvPowerSeries (Fin q) B)
    (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ) :
    sl (h * rename (⇑(ιE d q n)) i) δ ν = sl h δ ν * i := by
  ext γ
  rw [coeff_sl, coeff_mul, coeff_mul]

  let Φ : (Fin q →₀ ℕ) × (Fin q →₀ ℕ) → (((Fin d ⊕ Fin q) ⊕ Fin n →₀ ℕ) × ((Fin d ⊕ Fin q) ⊕ Fin n →₀ ℕ)) :=
    fun c => ((δ.sumElim c.1).sumElim ν, ((0 : Fin d →₀ ℕ).sumElim c.2).sumElim (0 : Fin n →₀ ℕ))
  have hΦinj : Function.Injective Φ := by
    intro c c' hcc
    simp only [Φ, Prod.mk.injEq, sumElim_ext] at hcc
    exact Prod.ext hcc.1.1.2 hcc.2.1.2
  have himage : (Finset.HasAntidiagonal.antidiagonal γ).image Φ ⊆ Finset.HasAntidiagonal.antidiagonal ((δ.sumElim γ).sumElim ν) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc ⊢
    simp only [Φ, sumElim_add, add_zero, hc]
  rw [← Finset.sum_subset himage, Finset.sum_image fun c _ c' _ hcc => hΦinj hcc]
  · refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Φ, coeff_sl, coeff_rename_ιE, and_self, if_true]
  ·
    intro p hp hnot
    by_cases hz : fstE (fstE p.2) = 0 ∧ sndE p.2 = 0
    · exfalso
      apply hnot
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [Finset.mem_image]
      refine ⟨(sndE (fstE p.1), sndE (fstE p.2)), ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        have := congrArg (fun E => sndE (fstE E)) hp
        rw [← sumElim_fstE_sndE p.1, ← sumElim_fstE_sndE p.2, ← sumElim_fstE_sndE (fstE p.1),
          ← sumElim_fstE_sndE (fstE p.2), sumElim_add, sumElim_add] at hp
        rw [sumElim_ext, sumElim_ext] at hp
        exact hp.1.2
      · rw [← sumElim_fstE_sndE p.1, ← sumElim_fstE_sndE p.2, ← sumElim_fstE_sndE (fstE p.1),
          ← sumElim_fstE_sndE (fstE p.2), sumElim_add, sumElim_add, sumElim_ext, sumElim_ext] at hp
        apply Prod.ext
        · show (δ.sumElim (sndE (fstE p.1))).sumElim ν = p.1
          conv_rhs => rw [← sumElim_fstE_sndE p.1, ← sumElim_fstE_sndE (fstE p.1)]
          rw [hz.1, add_zero] at hp; rw [hz.2, add_zero] at hp
          rw [hp.1.1, hp.2]
        · show ((0 : Fin d →₀ ℕ).sumElim (sndE (fstE p.2))).sumElim 0 = p.2
          conv_rhs => rw [← sumElim_fstE_sndE p.2, ← sumElim_fstE_sndE (fstE p.2)]
          rw [hz.1, hz.2]
    · rw [← sumElim_fstE_sndE p.2, ← sumElim_fstE_sndE (fstE p.2), coeff_rename_ιE, if_neg hz, mul_zero]

end Slices

section SpanChar

variable {B : Type*} [CommRing B] {d q n : ℕ}

theorem sl_mem_of_mem_span (I : Ideal (MvPowerSeries (Fin q) B))
    {V : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B}
    (hV : V ∈ Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B))) ''
          (I : Set (MvPowerSeries (Fin q) B))))
    (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ) : sl V δ ν ∈ I := by
  obtain ⟨N, r, g, hsum⟩ := Submodule.mem_span_set'.mp hV
  rw [← hsum, sl_sum]
  refine I.sum_mem fun k _ => ?_
  obtain ⟨i, hi, hgi⟩ := (g k).2
  rw [smul_eq_mul, show ((g k : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B)) = _ from hgi.symm,
    subst_eq_rename_ιE, sl_mul_rename]
  exact I.mul_mem_left _ hi

theorem mem_span_of_sl_mem [IsNoetherianRing B] (I : Ideal (MvPowerSeries (Fin q) B))
    {V : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B} (hV : ∀ δ ν, sl V δ ν ∈ I) :
    V ∈ Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B))) ''
          (I : Set (MvPowerSeries (Fin q) B))) := by
  classical
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) B) :=
    MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing B q
  obtain ⟨r, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have htI : ∀ s, t s ∈ I := fun s => by rw [← ht]; exact Submodule.subset_span ⟨s, rfl⟩
  have hdec : ∀ δ ν, ∃ g : Fin r → MvPowerSeries (Fin q) B, ∑ s, g s • t s = sl V δ ν := fun δ ν =>
    (Submodule.mem_span_range_iff_exists_fun _).mp (by rw [ht]; exact hV δ ν)
  choose g hg using hdec
  let W : Fin r → MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B := fun s => ofSl fun δ ν => g δ ν s
  have hVW : V = ∑ s, W s * rename (⇑(ιE d q n)) (t s) := by
    refine eq_of_sl_eq fun δ ν => ?_
    rw [sl_sum, ← hg δ ν]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sl_mul_rename, sl_ofSl, smul_eq_mul]
  rw [hVW]
  refine Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨t s, htI s, ?_⟩)
  exact subst_eq_rename_ιE (t s)

end SpanChar

end K2Transfer

open MvPowerSeries K2Transfer in
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] {q : ℕ} (I : Ideal (MvPowerSeries (Fin q) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin q) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin q) B ⧸ I))
    {d n m : ℕ} (a : Fin n → MvPowerSeries (Fin m) B) (ha0 : ∀ k, MvPowerSeries.constantCoeff (a k) = 0)
    (hinj : ∀ H : MvPowerSeries (Fin n ⊕ Fin d) B,
      MvPowerSeries.subst
          (Sum.elim (fun k => MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin m ⊕ Fin d) B)) (a k))
            (fun t => MvPowerSeries.X (Sum.inr t))) H = 0 → H = 0)
    (V : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B)
    (hV : MvPowerSeries.subst
        (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin m) B))
          (fun k => MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin m) B)) (a k))) V ∈
      Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin m) B))) ''
          (I : Set (MvPowerSeries (Fin q) B)))) :
    V ∈ Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B))) ''
          (I : Set (MvPowerSeries (Fin q) B))) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0

  have hV' : subst (θL (Fin d ⊕ Fin q) a) V ∈ Ideal.span ((MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin m) B))) ''
        (I : Set (MvPowerSeries (Fin q) B))) := hV

  have hslI : ∀ (δ : Fin d →₀ ℕ) (μ : Fin m →₀ ℕ),
      ∑ ν ∈ S ha μ, M a μ ν • sl V δ ν ∈ I := by
    intro δ μ
    have h1 := sl_mem_of_mem_span I hV' δ μ
    have h2 : sl (subst (θL (Fin d ⊕ Fin q) a) V) δ μ = ∑ ν ∈ S ha μ, M a μ ν • sl V δ ν := by
      ext γ
      rw [coeff_sl, coeff_subst_θL ha0 V (δ.sumElim γ) μ, map_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [map_smul, smul_eq_mul, coeff_sl]
    rwa [h2] at h1

  let C := MvPowerSeries (Fin q) B ⧸ I
  let π : MvPowerSeries (Fin q) B →ₐ[B] C := Ideal.Quotient.mkₐ B I
  let cbar : (Fin d →₀ ℕ) → (Fin n →₀ ℕ) → C := fun δ ν => π (sl V δ ν)
  have hC : ∀ (δ : Fin d →₀ ℕ) (μ : Fin m →₀ ℕ), ∑ ν ∈ S ha μ, M a μ ν • cbar δ ν = 0 := by
    intro δ μ
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr (hslI δ μ)
    rw [← Ideal.Quotient.mkₐ_eq_mk B, map_sum] at this
    simpa only [map_smul] using this

  obtain ⟨F, _, _, _, ι, s, hsι⟩ := Module.Projective.iff_split.mp hproj
  let bF := Module.Free.chooseBasis B F
  have hjoint : ∀ x : C, (∀ j, bF.coord j (ι x) = 0) → x = 0 := by
    intro x hx
    have h1 : bF.repr (ι x) = 0 := Finsupp.ext fun j => hx j
    have h2 : ι x = 0 := bF.repr.map_eq_zero_iff.mp h1
    have h3 : s (ι x) = x := by
      have := congrArg (fun f => f x) hsι
      simpa using this
    rw [← h3, h2, map_zero]

  have hcoord : ∀ j (δ : Fin d →₀ ℕ) (ν : Fin n →₀ ℕ), bF.coord j (ι (cbar δ ν)) = 0 := by
    intro j
    let lam : C →ₗ[B] B := (bF.coord j).comp ι
    let H : MvPowerSeries (Fin n ⊕ Fin d) B := fun D => lam (cbar (sndE D) (fstE D))
    have hH : ∀ ν δ, coeff (ν.sumElim δ) H = lam (cbar δ ν) := fun ν δ => by
      show lam (cbar (sndE (ν.sumElim δ)) (fstE (ν.sumElim δ))) = _
      rw [fstE_sumElim, sndE_sumElim]
    have hsub : subst (θF (Fin d) a) H = 0 := by
      ext e
      rw [coeff_zero, ← sumElim_fstE_sndE e, coeff_subst_θF ha0 H]
      have := congrArg lam (hC (sndE e) (fstE e))
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [map_smul, smul_eq_mul, hH]
    have hH0 : H = 0 := hinj H hsub
    intro δ ν
    have := hH ν δ
    rw [hH0, coeff_zero] at this
    exact this.symm

  have hcbar : ∀ δ ν, cbar δ ν = 0 := fun δ ν => hjoint _ fun j => hcoord j δ ν
  refine mem_span_of_sl_mem I fun δ ν => ?_
  have := hcbar δ ν
  rwa [show cbar δ ν = π (sl V δ ν) from rfl, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at this

end S_MvPowerSeries_mem_span_image_subst_of_subst_mem_span_image_subst_of_projective
end P2MW
export P2MW.S_MvPowerSeries_mem_span_image_subst_of_subst_mem_span_image_subst_of_projective (solution)
