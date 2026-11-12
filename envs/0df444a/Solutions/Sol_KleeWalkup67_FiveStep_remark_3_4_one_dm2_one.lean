-- Prove2me | solution 1 for KleeWalkup67.FiveStep.remark_3_4_one_dm2_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:29:40.218357+00:00
-- url     : https://prove2.me/submissions/e99aa9ce-8727-48de-9406-ad13af1d1397

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra
import Theorems.Thm_Hirsch_vertex_tight_rows_span
import Theorems.Thm_Hirsch_dimension_three_bound
import Theorems.Thm_KleeWalkup67_FiveStep_proposition_3_4_a
import Theorems.Thm_KleeWalkup67_FiveStep_proposition_3_4_b
import Theorems.Thm_KleeWalkup67_FiveStep_remark_3_4_merge

namespace Aux_KW67_remark_3_4_one_dm2_one

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep

noncomputable def tightFinset {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ⟪a i, z⟫ = b i)

lemma mem_tightFinset {d n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    {b : Fin n → ℝ} {z : EuclideanSpace ℝ (Fin d)} {i : Fin n} :
    i ∈ tightFinset a b z ↔ ⟪a i, z⟫ = b i := by
  unfold tightFinset
  simp

lemma coe_tightFinset {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (tightFinset a b z : Set (Fin n)) = TightSet a b z := by
  ext i
  simp [mem_tightFinset, TightSet]

lemma card_tightFinset_eq_ncard {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (tightFinset a b z).card = (TightSet a b z).ncard := by
  rw [← coe_tightFinset, Set.ncard_coe_finset]

lemma hpoly_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hirsch.Hpoly a b) := by
  intro x hx y hy u v hu hv huv i
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 : u * ⟪a i, x⟫ ≤ u * b i := mul_le_mul_of_nonneg_left (hx i) hu
  have h2 : v * ⟪a i, y⟫ ≤ v * b i := mul_le_mul_of_nonneg_left (hy i) hv
  linarith [show u * b i + v * b i = b i by rw [← add_mul, huv, one_mul]]

lemma adj_right_mem_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E}
    {a b : E} (h : Hirsch.Adj P a b) : b ∈ Set.extremePoints ℝ P := by
  have hb : b ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    refine ⟨right_mem_segment ℝ a b, ?_⟩
    rintro x hx y hy ⟨p, q, hp, hq, hpq, hxy⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h.1)
    rw [segment_eq_image'] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hb' : b = a + (1 : ℝ) • (b - a) := by module
    have hcomb : p • (a + s • (b - a)) + q • (a + t • (b - a))
        = a + (p * s + q * t) • (b - a) := by
      calc p • (a + s • (b - a)) + q • (a + t • (b - a))
          = (p + q) • a + (p * s + q * t) • (b - a) := by module
        _ = a + (p * s + q * t) • (b - a) := by rw [hpq]; module
    have hb2 : a + (p * s + q * t) • (b - a) = b := by rw [← hcomb]; exact hxy
    have hco : p * s + q * t = 1 := by
      have h3 : ((p * s + q * t) - 1) • (b - a) = 0 := by
        have e1 : ((p * s + q * t) - 1) • (b - a)
            = (a + (p * s + q * t) • (b - a)) - (a + (1 : ℝ) • (b - a)) := by module
        rw [e1, hb2, ← hb', sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith [sub_eq_zero.mp h4]
      · exact absurd h4 hba
    have hs1 : s = 1 := by
      nlinarith [hs.1, hs.2, ht.1, ht.2]
    rw [hs1]
    module
  have hex := h.2.extremePoints_eq (𝕜 := ℝ)
  rw [hex] at hb
  exact hb.2

lemma step_into_hpoly {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {v u : EuclideanSpace ℝ (Fin d)} (hv : v ∈ Hirsch.Hpoly a b)
    (hu : ∀ i ∈ tightFinset a b v, ⟪a i, u⟫ ≤ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → v + ε • u ∈ Hirsch.Hpoly a b := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < ⟪a i, u⟫)
  have hS_pos : ∀ i ∈ S, 0 < (b i - ⟪a i, v⟫) / ⟪a i, u⟫ := by
    intro i hi
    have hiu : 0 < ⟪a i, u⟫ := (Finset.mem_filter.mp hi).2
    have hnot : i ∉ tightFinset a b v := fun hm => by linarith [hu i hm]
    have hne : ⟪a i, v⟫ ≠ b i := by rwa [mem_tightFinset] at hnot
    have hlt : ⟪a i, v⟫ < b i := lt_of_le_of_ne (hv i) hne
    exact div_pos (sub_pos.mpr hlt) hiu
  by_cases hSne : S.Nonempty
  · let ε₀ : ℝ := S.inf' hSne (fun i => (b i - ⟪a i, v⟫) / ⟪a i, u⟫)
    have hε₀ : 0 < ε₀ := (Finset.lt_inf'_iff hSne).mpr hS_pos
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε hε_pos hε_le i
    rw [inner_add_right, real_inner_smul_right]
    rcases lt_or_ge 0 ⟪a i, u⟫ with hpos | hnonpos
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩
      have h1 : ε ≤ (b i - ⟪a i, v⟫) / ⟪a i, u⟫ := hε_le.trans (Finset.inf'_le _ hiS)
      have h2 : ε * ⟪a i, u⟫ ≤ b i - ⟪a i, v⟫ := (le_div_iff₀ hpos).mp h1
      linarith
    · have hmul : ε * ⟪a i, u⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_pos.le hnonpos
      linarith [hv i]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε_pos _ i
    rw [inner_add_right, real_inner_smul_right]
    have hnonpos : ⟪a i, u⟫ ≤ 0 := by
      by_contra hlt
      push Not at hlt
      exact hSne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩⟩
    have hmul : ε * ⟪a i, u⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_pos.le hnonpos
    linarith [hv i]

noncomputable def tightLinearMap {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (tightFinset a b v → ℝ) where
  toFun w i := ⟪a i.1, w⟫
  map_add' x y := by ext i; simp [inner_add_right]
  map_smul' r x := by ext i; simp [real_inner_smul_right]

noncomputable def tightEquiv {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard : (TightSet a b v).ncard = d) :
    EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (tightFinset a b v → ℝ) := by
  let f := tightLinearMap a b v
  have hinj : Function.Injective f := by
    intro x y hxy
    have h0 : x - y = 0 := by
      refine Hirsch.vertex_tight_rows_span d n a b v hv (x - y) ?_
      intro j hj
      have hfj := congr_fun hxy ⟨j, mem_tightFinset.mpr hj⟩
      dsimp [f, tightLinearMap] at hfj
      rw [inner_sub_right, hfj, sub_self]
    exact sub_eq_zero.mp h0
  have hcard_fin : (tightFinset a b v).card = d := by
    rw [card_tightFinset_eq_ncard, hcard]
  have hfr_dom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have hfr_cod : Module.finrank ℝ (tightFinset a b v → ℝ) = d := by
    simp [hcard_fin]
  have hker : Module.finrank ℝ (LinearMap.ker f) = 0 :=
    Submodule.finrank_eq_zero.mpr (LinearMap.ker_eq_bot.mpr hinj)
  have hrng : Module.finrank ℝ (LinearMap.range f) =
      Module.finrank ℝ (tightFinset a b v → ℝ) := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    omega
  have hsurj : Function.Surjective f :=
    LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hrng)
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

def zeroOnSubmodule {α : Type*} [DecidableEq α] (T J : Finset α) : Submodule ℝ (T → ℝ) where
  carrier := {f | ∀ i : T, i.1 ∈ J → f i = 0}
  add_mem' hf hg i hi := by simp [hf i hi, hg i hi]
  zero_mem' _ _ := rfl
  smul_mem' r f hf i hi := by simp [hf i hi]

def zeroOnEquivSdiff {α : Type*} [DecidableEq α] (T J : Finset α) :
    zeroOnSubmodule T J ≃ₗ[ℝ] ((T \ J : Finset α) → ℝ) := by
  refine
    { toFun := fun f k => f.1 ⟨k.1, (Finset.mem_sdiff.mp k.2).1⟩
      invFun := fun g =>
        ⟨fun i => if hi : i.1 ∈ J then 0 else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, hi⟩⟩,
          fun i hi => dif_pos hi⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    ext i
    by_cases hi : i.1 ∈ J
    · simp [hi, f.2 i hi]
    · simp [hi]
  · intro g
    ext k
    have hk : k.1 ∉ J := (Finset.mem_sdiff.mp k.2).2
    simp [hk]

lemma finrank_zeroOn_comap {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard : (TightSet a b v).ncard = d)
    (J : Finset (Fin n)) (hJT : J ⊆ tightFinset a b v) :
    Module.finrank ℝ
      ((zeroOnSubmodule (tightFinset a b v) J).comap (tightEquiv a b hv hcard).toLinearMap) =
      d - J.card := by
  classical
  let E := tightEquiv a b hv hcard
  let M := zeroOnSubmodule (tightFinset a b v) J
  let e1 : M.comap E.toLinearMap ≃ₗ[ℝ] M :=
    { toFun := fun x => ⟨E x.1, x.2⟩
      invFun := fun y => ⟨E.symm y.1, by simp [M, y.2]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  rw [e1.finrank_eq, (zeroOnEquivSdiff (tightFinset a b v) J).finrank_eq,
    Module.finrank_pi, Fintype.card_coe]
  have hcard_T : (tightFinset a b v).card = d := by
    rw [card_tightFinset_eq_ncard, hcard]
  have h := Finset.card_sdiff_add_card_eq_card hJT
  omega

lemma dim_faceOf_at_simple_vertex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard : (TightSet a b v).ncard = d)
    (J : Finset (Fin n)) (hvJ : v ∈ faceOf a b J) :
    J ⊆ tightFinset a b v ∧ dim (faceOf a b J) = d - J.card := by
  classical
  have hJT : J ⊆ tightFinset a b v := fun i hi => mem_tightFinset.mpr (hvJ.2 i hi)
  refine ⟨hJT, ?_⟩
  let E := tightEquiv a b hv hcard
  let M := zeroOnSubmodule (tightFinset a b v) J
  have hdir : (affineSpan ℝ (faceOf a b J)).direction = M.comap E.toLinearMap := by
    apply le_antisymm
    · rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro w ⟨z₁, hz₁, z₂, hz₂, rfl⟩
      intro i hi
      change ⟪a i.1, z₁ - z₂⟫ = 0
      rw [inner_sub_right, hz₁.2 i.1 hi, hz₂.2 i.1 hi, sub_self]
    · intro w hw
      rw [direction_affineSpan]
      let g₀ : tightFinset a b v → ℝ := fun k => if k.1 ∈ J then 0 else -1 - |E w k|
      let g₁ : tightFinset a b v → ℝ := g₀ + E w
      let u₀ := E.symm g₀
      let u₁ := E.symm g₁
      have hu₀_le : ∀ i ∈ tightFinset a b v, ⟪a i, u₀⟫ ≤ 0 := by
        intro i hi
        have heq : ⟪a i, u₀⟫ = g₀ ⟨i, hi⟩ := by
          change E u₀ ⟨i, hi⟩ = g₀ ⟨i, hi⟩
          simp [u₀]
        rw [heq]
        dsimp [g₀]
        split_ifs
        · exact le_rfl
        · linarith [abs_nonneg (E w ⟨i, hi⟩)]
      have hu₁_le : ∀ i ∈ tightFinset a b v, ⟪a i, u₁⟫ ≤ 0 := by
        intro i hi
        have heq : ⟪a i, u₁⟫ = g₁ ⟨i, hi⟩ := by
          change E u₁ ⟨i, hi⟩ = g₁ ⟨i, hi⟩
          simp [u₁]
        rw [heq]
        dsimp [g₁, g₀]
        split_ifs with hJ
        · have hw0 : E w ⟨i, hi⟩ = 0 := hw ⟨i, hi⟩ hJ
          linarith
        · linarith [le_abs_self (E w ⟨i, hi⟩)]
      obtain ⟨ε₀, hε₀_pos, hε₀⟩ := step_into_hpoly a b hv.1 hu₀_le
      obtain ⟨ε₁, hε₁_pos, hε₁⟩ := step_into_hpoly a b hv.1 hu₁_le
      let ε := min ε₀ ε₁
      have hε_pos : 0 < ε := lt_min hε₀_pos hε₁_pos
      have hz₀ : v + ε • u₀ ∈ faceOf a b J := by
        refine ⟨hε₀ ε hε_pos (min_le_left _ _), ?_⟩
        intro i hi
        have hiT : i ∈ tightFinset a b v := hJT hi
        have heq : ⟪a i, u₀⟫ = g₀ ⟨i, hiT⟩ := by
          change E u₀ ⟨i, hiT⟩ = g₀ ⟨i, hiT⟩
          simp [u₀]
        rw [inner_add_right, real_inner_smul_right, hvJ.2 i hi, heq]
        simp [g₀, hi]
      have hz₁ : v + ε • u₁ ∈ faceOf a b J := by
        refine ⟨hε₁ ε hε_pos (min_le_right _ _), ?_⟩
        intro i hi
        have hiT : i ∈ tightFinset a b v := hJT hi
        have heq : ⟪a i, u₁⟫ = g₁ ⟨i, hiT⟩ := by
          change E u₁ ⟨i, hiT⟩ = g₁ ⟨i, hiT⟩
          simp [u₁]
        have hw0 : E w ⟨i, hiT⟩ = 0 := hw ⟨i, hiT⟩ hi
        rw [inner_add_right, real_inner_smul_right, hvJ.2 i hi, heq]
        simp [g₁, g₀, hi, hw0]
      have hmem : (v + ε • u₁) -ᵥ (v + ε • u₀) ∈ vectorSpan ℝ (faceOf a b J) :=
        vsub_mem_vectorSpan ℝ hz₁ hz₀
      have hdiff : (v + ε • u₁) -ᵥ (v + ε • u₀) = ε • w := by
        have hu10 : u₁ - u₀ = w := by
          dsimp [u₁, u₀, g₁]
          rw [map_add, add_sub_cancel_left, E.symm_apply_apply]
        calc (v + ε • u₁) - (v + ε • u₀)
            = ε • (u₁ - u₀) := by module
          _ = ε • w := by rw [hu10]
      rw [hdiff] at hmem
      have hsmul := Submodule.smul_mem (vectorSpan ℝ (faceOf a b J)) ε⁻¹ hmem
      rwa [inv_smul_smul₀ (ne_of_gt hε_pos)] at hsmul
  unfold dim
  rw [hdir]
  exact finrank_zeroOn_comap a b hv hcard J hJT

lemma finrank_span_singleton_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (v : E) :
    Module.finrank ℝ (ℝ ∙ v) ≤ 1 := by
  let f : ℝ →ₗ[ℝ] E :=
    { toFun := fun t => t • v
      map_add' := fun s t => add_smul s t v
      map_smul' := fun r t => by simp [mul_smul] }
  have hle : (ℝ ∙ v) ≤ LinearMap.range f := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨1, one_smul ℝ v⟩
  calc Module.finrank ℝ (ℝ ∙ v)
      ≤ Module.finrank ℝ (LinearMap.range f) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ ℝ := LinearMap.finrank_range_le f
    _ = 1 := Module.finrank_self ℝ

lemma adj_inter_tightFinset_card {d n : ℕ} (hd : 1 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard_u : (TightSet a b u).ncard = d)
    (hadj : Hirsch.Adj (Hirsch.Hpoly a b) u v) :
    (tightFinset a b u ∩ tightFinset a b v).card = d - 1 := by
  classical
  have hTu : (tightFinset a b u).card = d := by
    rw [card_tightFinset_eq_ncard, hcard_u]
  have hle : (tightFinset a b u ∩ tightFinset a b v).card ≤ d - 1 := by
    by_contra hgt
    push Not at hgt
    have hge : (tightFinset a b u).card ≤ (tightFinset a b u ∩ tightFinset a b v).card := by omega
    have heq := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hge
    have hsub : tightFinset a b u ⊆ tightFinset a b v := by
      rw [← heq]
      exact Finset.inter_subset_right
    have hv_eq_u : v - u = 0 := by
      refine Hirsch.vertex_tight_rows_span d n a b u hu (v - u) ?_
      intro j hj
      have hjv : ⟪a j, v⟫ = b j := mem_tightFinset.mp (hsub (mem_tightFinset.mpr hj))
      rw [inner_sub_right, hjv, hj, sub_self]
    exact hadj.1 (sub_eq_zero.mp hv_eq_u).symm
  have hge : d - 1 ≤ (tightFinset a b u ∩ tightFinset a b v).card := by
    by_contra hlt
    push Not at hlt
    let J := tightFinset a b u ∩ tightFinset a b v
    have hJU : J ⊆ tightFinset a b u := Finset.inter_subset_left
    let E := tightEquiv a b hu hcard_u
    let N := (zeroOnSubmodule (tightFinset a b u) J).comap E.toLinearMap
    have hfrN : Module.finrank ℝ N = d - J.card :=
      finrank_zeroOn_comap a b hu hcard_u J hJU
    have hfrN_ge2 : 2 ≤ Module.finrank ℝ N := by
      rw [hfrN]
      dsimp [J]
      omega
    have hfrL : Module.finrank ℝ (ℝ ∙ (v - u)) ≤ 1 := finrank_span_singleton_le_one (v - u)
    have hnot_le : ¬ (N ≤ (ℝ ∙ (v - u))) := by
      intro hle'
      have := Submodule.finrank_mono hle'
      omega
    obtain ⟨e, heN, he_not⟩ : ∃ e ∈ N, e ∉ (ℝ ∙ (v - u)) := by
      by_contra hall
      push Not at hall
      exact hnot_le hall
    let m : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v
    have hm_seg : m ∈ segment ℝ u v :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hm_P : m ∈ Hirsch.Hpoly a b :=
      hpoly_convex a b hu.1 hv.1 (by norm_num) (by norm_num) (by norm_num)
    have hTm : tightFinset a b m = J := by
      ext i
      simp only [mem_tightFinset, J, Finset.mem_inter]
      have h1 : ⟪a i, u⟫ ≤ b i := hu.1 i
      have h2 : ⟪a i, v⟫ ≤ b i := hv.1 i
      have hexp : ⟪a i, m⟫ = (1 / 2 : ℝ) * ⟪a i, u⟫ + (1 / 2 : ℝ) * ⟪a i, v⟫ := by
        dsimp [m]
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [hexp]
      constructor
      · intro hm_eq
        constructor <;> linarith
      · rintro ⟨hu_eq, hv_eq⟩
        linarith
    have he_zero : ∀ i ∈ tightFinset a b m, ⟪a i, e⟫ = 0 := by
      rw [hTm]
      intro i hi
      exact heN ⟨i, hJU hi⟩ hi
    have hne_zero : ∀ i ∈ tightFinset a b m, ⟪a i, -e⟫ ≤ 0 := by
      intro i hi
      rw [inner_neg_right, he_zero i hi, neg_zero]
    obtain ⟨ε₁, hε₁_pos, hε₁⟩ := step_into_hpoly a b hm_P (fun i hi => (he_zero i hi).le)
    obtain ⟨ε₂, hε₂_pos, hε₂⟩ := step_into_hpoly a b hm_P hne_zero
    let ε := min ε₁ ε₂
    have hε_pos : 0 < ε := lt_min hε₁_pos hε₂_pos
    have hz_pos : m + ε • e ∈ Hirsch.Hpoly a b := hε₁ ε hε_pos (min_le_left _ _)
    have hz_neg : m + ε • (-e) ∈ Hirsch.Hpoly a b := hε₂ ε hε_pos (min_le_right _ _)
    have hm_open : m ∈ openSegment ℝ (m + ε • e) (m + ε • (-e)) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    have hz_seg : m + ε • e ∈ segment ℝ u v :=
      hadj.2.2 hz_pos hz_neg hm_seg hm_open
    rw [segment_eq_image'] at hz_seg
    obtain ⟨t, _, htz⟩ := hz_seg
    dsimp only at htz
    have hrel : ε • e = (t - 1 / 2) • (v - u) := by
      calc ε • e
          = (m + ε • e) - m := by module
        _ = (u + t • (v - u)) - ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) := by rw [← htz]
        _ = (t - 1 / 2) • (v - u) := by module
    have he_mem : e ∈ (ℝ ∙ (v - u)) := by
      have h1 : (t - 1 / 2) • (v - u) ∈ (ℝ ∙ (v - u)) :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      rw [← hrel] at h1
      have h2 := Submodule.smul_mem (ℝ ∙ (v - u)) ε⁻¹ h1
      rwa [inv_smul_smul₀ (ne_of_gt hε_pos)] at h2
    exact he_not he_mem
  omega

end Aux_KW67_remark_3_4_one_dm2_one

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep Aux_KW67_remark_3_4_one_dm2_one

theorem solution {d : ℕ} (hd : 2 ≤ d)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (hB : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    IsFacialPath a b [1, d - 2, 1] x y := by
  classical
  by_cases hd2 : d = 2
  · subst hd2
    obtain ⟨_, hx_ext, hy_ext, hx_ncard, _, hdisj_set⟩ := hD
    have hTx_card : (tightFinset a b x).card = 2 := by rw [card_tightFinset_eq_ncard, hx_ncard]
    have hdisj : Disjoint (tightFinset a b x) (tightFinset a b y) := by
      rw [Finset.disjoint_left]
      intro i hix hiy
      exact Set.disjoint_left.mp hdisj_set (mem_tightFinset.mp hix) (mem_tightFinset.mp hiy)
    have hxy_ne : x ≠ y := by
      intro h_eq
      subst h_eq
      have h0 : (tightFinset a b x ∩ tightFinset a b x).card = 0 := by
        rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
        simp
      rw [Finset.inter_self, hTx_card] at h0
      omega
    have hnot_adj_xy : ¬ Hirsch.Adj (Hirsch.Hpoly a b) x y := by
      intro hadj
      have hc := adj_inter_tightFinset_card (by omega) a b hx_ext hy_ext hx_ncard hadj
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj] at hc
      simp at hc
    obtain ⟨w, hw0, hw2, hwstep⟩ :=
      Hirsch.dimension_three_bound 2 (2 * 2) (by omega) a b ⟨x, hx_ext.1⟩ hB x hx_ext y hy_ext
    have hstep0 := hwstep 0 (by omega)
    have hstep1 := hwstep 1 (by omega)
    rw [hw0] at hstep0
    rw [hw2] at hstep1
    let v₁ := w 1
    have hadj01 : Hirsch.Adj (Hirsch.Hpoly a b) x v₁ := by
      rcases hstep0 with heq0 | hadj0
      · exfalso
        rcases hstep1 with heq1 | hadj1
        · exact hxy_ne (heq0.trans heq1)
        · rw [← heq0] at hadj1
          exact hnot_adj_xy hadj1
      · exact hadj0
    have hadj12 : Hirsch.Adj (Hirsch.Hpoly a b) v₁ y := by
      rcases hstep1 with heq1 | hadj1
      · exfalso
        change v₁ = y at heq1
        rw [heq1] at hadj01
        exact hnot_adj_xy hadj01
      · exact hadj1
    have hv₁_ext : v₁ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) :=
      adj_right_mem_extremePoints hadj01
    have hv₁_ncard : (TightSet a b v₁).ncard = 2 := hS.2 v₁ hv₁_ext
    have hv₁_card : (tightFinset a b v₁).card = 2 := by rw [card_tightFinset_eq_ncard, hv₁_ncard]
    let I₀ := tightFinset a b x ∩ tightFinset a b v₁
    let I₁ := tightFinset a b v₁
    let I₂ := tightFinset a b v₁ ∩ tightFinset a b y
    have hI₀_card : I₀.card = 1 :=
      adj_inter_tightFinset_card (by omega) a b hx_ext hv₁_ext hx_ncard hadj01
    have hI₂_card : I₂.card = 1 :=
      adj_inter_tightFinset_card (by omega) a b hv₁_ext hy_ext hv₁_ncard hadj12
    have hx_I₀ : x ∈ faceOf a b I₀ :=
      ⟨hx_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_left hi)⟩
    have hv₁_I₀ : v₁ ∈ faceOf a b I₀ :=
      ⟨hv₁_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_right hi)⟩
    have hv₁_I₁ : v₁ ∈ faceOf a b I₁ :=
      ⟨hv₁_ext.1, fun i hi => mem_tightFinset.mp hi⟩
    have hv₁_I₂ : v₁ ∈ faceOf a b I₂ :=
      ⟨hv₁_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_left hi)⟩
    have hy_I₂ : y ∈ faceOf a b I₂ :=
      ⟨hy_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_right hi)⟩
    have hdim₀ : dim (faceOf a b I₀) = 1 := by
      have hd0 := (dim_faceOf_at_simple_vertex a b hx_ext hx_ncard I₀ hx_I₀).2
      omega
    have hdim₁ : dim (faceOf a b I₁) = 0 := by
      have hd1 := (dim_faceOf_at_simple_vertex a b hv₁_ext hv₁_ncard I₁ hv₁_I₁).2
      dsimp [I₁] at hd1 ⊢
      omega
    have hdim₂ : dim (faceOf a b I₂) = 1 := by
      have hd2' := (dim_faceOf_at_simple_vertex a b hv₁_ext hv₁_ncard I₂ hv₁_I₂).2
      omega
    let K : Fin [1, 2 - 2, 1].length → Set (EuclideanSpace ℝ (Fin 2)) :=
      ![faceOf a b I₀, faceOf a b I₁, faceOf a b I₂]
    refine ⟨K, ?_, ?_, ?_⟩
    · intro idx
      fin_cases idx
      · exact ⟨⟨⟨x, hx_I₀⟩, I₀, rfl⟩, hdim₀⟩
      · exact ⟨⟨⟨v₁, hv₁_I₁⟩, I₁, rfl⟩, hdim₁⟩
      · exact ⟨⟨⟨v₁, hv₁_I₂⟩, I₂, rfl⟩, hdim₂⟩
    · intro idx₁ idx₂ hnext
      fin_cases idx₁ <;> fin_cases idx₂ <;> simp at hnext ⊢
      · exact ⟨v₁, hv₁_I₀, hv₁_I₁⟩
      · exact ⟨v₁, hv₁_I₁, hv₁_I₂⟩
    · have hlen3 : 0 < [1, 2 - 2, 1].length := by simp
      exact ⟨hlen3, by simpa [K] using hx_I₀, by simpa [K] using hy_I₂⟩
  by_cases hd3 : d = 3
  · subst hd3
    exact KleeWalkup67.FiveStep.proposition_3_4_a a b x y hD hS 1 1 zero_lt_one zero_lt_one rfl
  have hd4 : 4 ≤ d := by omega
  have hpath4 : IsFacialPath a b ([1] ++ (d - 3) :: 1 :: [1]) x y := by
    simpa using KleeWalkup67.FiveStep.proposition_3_4_b a b x y hD hS hB
      (d - 3) 1 (by omega) zero_lt_one (by omega)
  have hmerged := KleeWalkup67.FiveStep.remark_3_4_merge a b x y hD hS
    [1] [1] (d - 3) 1 (by omega) hpath4
  have hsub_eq : d - 3 + 1 = d - 2 := by omega
  rwa [List.singleton_append, hsub_eq] at hmerged
