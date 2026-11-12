-- Prove2me | solution 1 for KleeWalkup67.FiveStep.proposition_3_4_b
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:26:22.498724+00:00
-- url     : https://prove2.me/submissions/4e0226d3-8fcf-4428-aa31-8f8996996e71

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra
import Theorems.Thm_Hirsch_vertex_tight_rows_span
import Theorems.Thm_KleeWalkup67_FiveStep_proposition_3_4_a

namespace Aux_KW67_proposition_3_4_b

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

lemma faceOf_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (I : Finset (Fin n)) : Convex ℝ (faceOf a b I) := by
  intro x hx y hy u v hu hv huv
  refine ⟨hpoly_convex a b hx.1 hy.1 hu hv huv, ?_⟩
  intro i hi
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hx.2 i hi, hy.2 i hi]
  rw [← add_mul, huv, one_mul]

lemma isExtreme_faceOf {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (I : Finset (Fin n)) : IsExtreme ℝ (Hirsch.Hpoly a b) (faceOf a b I) := by
  refine ⟨fun z hz => hz.1, ?_⟩
  rintro x₁ hx₁ x₂ hx₂ z hzI ⟨p, q, hp, hq, hpq, hcomb⟩
  refine ⟨hx₁, ?_⟩
  intro i hi
  have hz_eq : ⟪a i, z⟫ = b i := hzI.2 i hi
  have h1 : ⟪a i, x₁⟫ ≤ b i := hx₁ i
  have h2 : ⟪a i, x₂⟫ ≤ b i := hx₂ i
  have hlin : p * ⟪a i, x₁⟫ + q * ⟪a i, x₂⟫ = b i := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb, hz_eq]
  by_contra hne
  have hlt : ⟪a i, x₁⟫ < b i := lt_of_le_of_ne h1 hne
  have hm1 : p * ⟪a i, x₁⟫ < p * b i := mul_lt_mul_of_pos_left hlt hp
  have hm2 : q * ⟪a i, x₂⟫ ≤ q * b i := mul_le_mul_of_nonneg_left h2 hq.le
  have hm3 : p * b i + q * b i = b i := by rw [← add_mul, hpq, one_mul]
  linarith

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

lemma nonempty_faceOf_has_vertex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v₀ : EuclideanSpace ℝ (Fin d)}
    (hv₀ : v₀ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (I : Finset (Fin n)) (hne : (faceOf a b I).Nonempty) :
    ∃ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b), v ∈ faceOf a b I := by
  classical
  have hinj_all : ∀ e : EuclideanSpace ℝ (Fin d), (∀ j : Fin n, ⟪a j, e⟫ = 0) → e = 0 := by
    intro e he
    exact Hirsch.vertex_tight_rows_span d n a b v₀ hv₀ e (fun j _ => he j)
  suffices hind : ∀ (m : ℕ) (z : EuclideanSpace ℝ (Fin d)),
      z ∈ faceOf a b I → n - (tightFinset a b z).card ≤ m →
      ∃ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b), v ∈ faceOf a b I by
    obtain ⟨z, hz⟩ := hne
    exact hind (n - (tightFinset a b z).card) z hz le_rfl
  intro m
  induction m with
  | zero =>
      intro z hz hm
      by_cases hspan : ∀ e : EuclideanSpace ℝ (Fin d),
          (∀ j ∈ tightFinset a b z, ⟪a j, e⟫ = 0) → e = 0
      · refine ⟨z, ⟨hz.1, ?_⟩, hz⟩
        rintro x₁ hx₁ x₂ hx₂ ⟨p, q, hp, hq, hpq, hcomb⟩
        have hxz : x₁ - z = 0 := by
          refine hspan (x₁ - z) ?_
          intro j hj
          have hjz : ⟪a j, z⟫ = b j := mem_tightFinset.mp hj
          have hj1 : ⟪a j, x₁⟫ ≤ b j := hx₁ j
          have hj2 : ⟪a j, x₂⟫ ≤ b j := hx₂ j
          have hlin : p * ⟪a j, x₁⟫ + q * ⟪a j, x₂⟫ = b j := by
            rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb, hjz]
          have heq1 : ⟪a j, x₁⟫ = b j := by
            by_contra hne1
            have hlt1 : ⟪a j, x₁⟫ < b j := lt_of_le_of_ne hj1 hne1
            have hm1 : p * ⟪a j, x₁⟫ < p * b j := mul_lt_mul_of_pos_left hlt1 hp
            have hm2 : q * ⟪a j, x₂⟫ ≤ q * b j := mul_le_mul_of_nonneg_left hj2 hq.le
            have hm3 : p * b j + q * b j = b j := by rw [← add_mul, hpq, one_mul]
            linarith
          rw [inner_sub_right, heq1, hjz, sub_self]
        exact sub_eq_zero.mp hxz
      · push Not at hspan
        obtain ⟨e, heT, he_ne⟩ := hspan
        have hex : ∃ j : Fin n, ⟪a j, e⟫ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact he_ne (hinj_all e hall)
        obtain ⟨j₀, hj₀⟩ := hex
        have hcard_le : (tightFinset a b z).card ≤ n := by
          simpa using Finset.card_le_univ (tightFinset a b z)
        have hcard_eq : (tightFinset a b z).card = n := by omega
        have huniv : tightFinset a b z = Finset.univ :=
          Finset.eq_univ_of_card _ (by simpa using hcard_eq)
        exact absurd (heT j₀ (by simp [huniv])) hj₀
  | succ m ih =>
      intro z hz hm
      by_cases hspan : ∀ e : EuclideanSpace ℝ (Fin d),
          (∀ j ∈ tightFinset a b z, ⟪a j, e⟫ = 0) → e = 0
      · refine ⟨z, ⟨hz.1, ?_⟩, hz⟩
        rintro x₁ hx₁ x₂ hx₂ ⟨p, q, hp, hq, hpq, hcomb⟩
        have hxz : x₁ - z = 0 := by
          refine hspan (x₁ - z) ?_
          intro j hj
          have hjz : ⟪a j, z⟫ = b j := mem_tightFinset.mp hj
          have hj1 : ⟪a j, x₁⟫ ≤ b j := hx₁ j
          have hj2 : ⟪a j, x₂⟫ ≤ b j := hx₂ j
          have hlin : p * ⟪a j, x₁⟫ + q * ⟪a j, x₂⟫ = b j := by
            rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb, hjz]
          have heq1 : ⟪a j, x₁⟫ = b j := by
            by_contra hne1
            have hlt1 : ⟪a j, x₁⟫ < b j := lt_of_le_of_ne hj1 hne1
            have hm1 : p * ⟪a j, x₁⟫ < p * b j := mul_lt_mul_of_pos_left hlt1 hp
            have hm2 : q * ⟪a j, x₂⟫ ≤ q * b j := mul_le_mul_of_nonneg_left hj2 hq.le
            have hm3 : p * b j + q * b j = b j := by rw [← add_mul, hpq, one_mul]
            linarith
          rw [inner_sub_right, heq1, hjz, sub_self]
        exact sub_eq_zero.mp hxz
      · push Not at hspan
        obtain ⟨e₀, he₀T, he₀_ne⟩ := hspan
        have hex : ∃ j : Fin n, ⟪a j, e₀⟫ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact he₀_ne (hinj_all e₀ hall)
        obtain ⟨j₀, hj₀⟩ := hex
        let e : EuclideanSpace ℝ (Fin d) := if 0 < ⟪a j₀, e₀⟫ then e₀ else -e₀
        have heT : ∀ j ∈ tightFinset a b z, ⟪a j, e⟫ = 0 := by
          intro j hj
          dsimp [e]
          split_ifs
          · exact he₀T j hj
          · rw [inner_neg_right, he₀T j hj, neg_zero]
        have hj₀_pos : 0 < ⟪a j₀, e⟫ := by
          dsimp [e]
          split_ifs with hpos
          · exact hpos
          · rw [inner_neg_right]
            have hlt : ⟪a j₀, e₀⟫ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hj₀
            linarith
        let S : Finset (Fin n) := Finset.univ.filter (fun j => 0 < ⟪a j, e⟫)
        have hSne : S.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀_pos⟩⟩
        obtain ⟨jstar, hjstar_S, hjstar_min⟩ :=
          S.exists_min_image (fun j => (b j - ⟪a j, z⟫) / ⟪a j, e⟫) hSne
        let t : ℝ := (b jstar - ⟪a jstar, z⟫) / ⟪a jstar, e⟫
        have hjstar_e : 0 < ⟪a jstar, e⟫ := (Finset.mem_filter.mp hjstar_S).2
        have hjstar_notT : jstar ∉ tightFinset a b z := by
          intro hm_in
          linarith [heT jstar hm_in]
        have hjstar_lt : ⟪a jstar, z⟫ < b jstar :=
          lt_of_le_of_ne (hz.1 jstar) (by rwa [mem_tightFinset] at hjstar_notT)
        have ht_pos : 0 < t := div_pos (sub_pos.mpr hjstar_lt) hjstar_e
        let z' := z + t • e
        have hz'_P : z' ∈ Hirsch.Hpoly a b := by
          intro j
          dsimp [z']
          rw [inner_add_right, real_inner_smul_right]
          rcases lt_or_ge 0 ⟪a j, e⟫ with hje_pos | hje_nonpos
          · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hje_pos⟩
            have hle : t ≤ (b j - ⟪a j, z⟫) / ⟪a j, e⟫ := hjstar_min j hjS
            have hmul : t * ⟪a j, e⟫ ≤ b j - ⟪a j, z⟫ := (le_div_iff₀ hje_pos).mp hle
            linarith
          · have hmul : t * ⟪a j, e⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_pos.le hje_nonpos
            linarith [hz.1 j]
        have hsub : tightFinset a b z ⊆ tightFinset a b z' := by
          intro j hj
          rw [mem_tightFinset] at hj ⊢
          dsimp [z']
          rw [inner_add_right, real_inner_smul_right, hj, heT j (mem_tightFinset.mpr hj)]
          ring
        have hz' : z' ∈ faceOf a b I := by
          refine ⟨hz'_P, ?_⟩
          intro i hi
          exact mem_tightFinset.mp (hsub (mem_tightFinset.mpr (hz.2 i hi)))
        have hjstar_in : jstar ∈ tightFinset a b z' := by
          rw [mem_tightFinset]
          dsimp [z', t]
          rw [inner_add_right, real_inner_smul_right, div_mul_cancel₀ _ (ne_of_gt hjstar_e)]
          ring
        have hssub : tightFinset a b z ⊂ tightFinset a b z' :=
          Finset.ssubset_iff_of_subset hsub |>.mpr ⟨jstar, hjstar_in, hjstar_notT⟩
        have hlt_card : (tightFinset a b z).card < (tightFinset a b z').card :=
          Finset.card_lt_card hssub
        have hcard_le : (tightFinset a b z').card ≤ n := by
          simpa using Finset.card_le_univ (tightFinset a b z')
        exact ih z' hz' (by omega)

lemma finrank_span_singleton_eq_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {v : E} (hv : v ≠ 0) :
    Module.finrank ℝ (ℝ ∙ v) = 1 := by
  let f0 : ℝ →ₗ[ℝ] (ℝ ∙ v) :=
    { toFun := fun t => ⟨t • v, Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v)⟩
      map_add' := fun s t => by ext; exact add_smul s t v
      map_smul' := fun r t => by ext; simp [mul_smul] }
  let f : ℝ ≃ₗ[ℝ] (ℝ ∙ v) :=
    LinearEquiv.ofBijective f0
      ⟨fun s t hst => by
          have h1 : (s - t) • v = 0 := by
            rw [sub_smul, sub_eq_zero]
            exact congr_arg Subtype.val hst
          rcases smul_eq_zero.mp h1 with h2 | h2
          · exact sub_eq_zero.mp h2
          · exact absurd h2 hv,
        fun ⟨w, hw⟩ => by
          obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
          exact ⟨t, rfl⟩⟩
  rw [← f.finrank_eq, Module.finrank_self]

lemma exists_bounded_edge_from_simple_vertex {d n : ℕ} (hd : 2 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hB : Bornology.IsBounded (Hirsch.Hpoly a b))
    {x : EuclideanSpace ℝ (Fin d)} (hx_ext : x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hx_ncard : (TightSet a b x).ncard = d) {i₀ : Fin n} (hi₀ : i₀ ∈ tightFinset a b x) :
    ∃ x' ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      x' ≠ x ∧ IsFace a b (segment ℝ x x') ∧ dim (segment ℝ x x') = 1 ∧
      tightFinset a b x \ {i₀} ⊆ tightFinset a b x' ∧ i₀ ∉ tightFinset a b x' := by
  classical
  have hTx_card : (tightFinset a b x).card = d := by rw [card_tightFinset_eq_ncard, hx_ncard]
  let J₀ : Finset (Fin n) := (tightFinset a b x).erase i₀
  have hJ₀_card : J₀.card = d - 1 := by
    rw [Finset.card_erase_of_mem hi₀, hTx_card]
  have hx_J₀ : x ∈ faceOf a b J₀ :=
    ⟨hx_ext.1, fun j hj => mem_tightFinset.mp (Finset.erase_subset i₀ _ hj)⟩
  have hdim_J₀ : dim (faceOf a b J₀) = 1 := by
    have hdJ := (dim_faceOf_at_simple_vertex a b hx_ext hx_ncard J₀ hx_J₀).2
    rw [hdJ, hJ₀_card]
    omega
  let E_x := tightEquiv a b hx_ext hx_ncard
  let e : EuclideanSpace ℝ (Fin d) := E_x.symm (fun k => if k.1 = i₀ then -1 else 0)
  have he_eval : ∀ j : Fin n, ∀ hj : j ∈ tightFinset a b x,
      ⟪a j, e⟫ = if j = i₀ then -1 else 0 := by
    intro j hj
    change E_x e ⟨j, hj⟩ = if j = i₀ then -1 else 0
    simp [e]
  have he_J₀ : ∀ j ∈ J₀, ⟪a j, e⟫ = 0 := by
    intro j hj
    obtain ⟨hjne, hjTx⟩ := Finset.mem_erase.mp hj
    rw [he_eval j hjTx, if_neg hjne]
  have he_i₀ : ⟪a i₀, e⟫ = -1 := by
    rw [he_eval i₀ hi₀, if_pos rfl]
  have he_ne : e ≠ 0 := by
    intro he0
    rw [he0, inner_zero_right] at he_i₀
    norm_num at he_i₀
  have he_le : ∀ j ∈ tightFinset a b x, ⟪a j, e⟫ ≤ 0 := by
    intro j hj
    rw [he_eval j hj]
    split_ifs <;> linarith
  obtain ⟨ε₀, hε₀_pos, hε₀⟩ := step_into_hpoly a b hx_ext.1 he_le
  let S_ray : Set ℝ := {t : ℝ | 0 ≤ t ∧ x + t • e ∈ Hirsch.Hpoly a b}
  have h0_S : (0 : ℝ) ∈ S_ray := ⟨le_rfl, by simpa using hx_ext.1⟩
  have hε₀_S : ε₀ ∈ S_ray := ⟨hε₀_pos.le, hε₀ ε₀ hε₀_pos le_rfl⟩
  have hbdd : BddAbove S_ray := by
    obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    have he_norm : 0 < ‖e‖ := norm_pos_iff.mpr he_ne
    refine ⟨(R + ‖x‖) / ‖e‖, ?_⟩
    rintro t ⟨ht0, hxt⟩
    have hnorm_xt : ‖x + t • e‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hxt
    have hte : t * ‖e‖ ≤ R + ‖x‖ := by
      calc t * ‖e‖
          = ‖t • e‖ := by rw [norm_smul, Real.norm_of_nonneg ht0]
        _ = ‖(x + t • e) - x‖ := by congr 1; module
        _ ≤ ‖x + t • e‖ + ‖x‖ := norm_sub_le _ _
        _ ≤ R + ‖x‖ := by linarith
    exact (le_div_iff₀ he_norm).mpr hte
  let tstar : ℝ := sSup S_ray
  have htstar_pos : 0 < tstar := lt_of_lt_of_le hε₀_pos (le_csSup hbdd hε₀_S)
  let x' : EuclideanSpace ℝ (Fin d) := x + tstar • e
  have hx'_P : x' ∈ Hirsch.Hpoly a b := by
    intro i
    dsimp [x']
    rw [inner_add_right, real_inner_smul_right]
    rcases lt_or_ge 0 ⟪a i, e⟫ with hpos | hnonpos
    · have hub : tstar ≤ (b i - ⟪a i, x⟫) / ⟪a i, e⟫ := by
        refine csSup_le ⟨0, h0_S⟩ ?_
        rintro t ⟨_, hxt⟩
        have hti : ⟪a i, x + t • e⟫ ≤ b i := hxt i
        rw [inner_add_right, real_inner_smul_right] at hti
        exact (le_div_iff₀ hpos).mpr (by linarith)
      have hmul : tstar * ⟪a i, e⟫ ≤ b i - ⟪a i, x⟫ := (le_div_iff₀ hpos).mp hub
      linarith
    · have hmul : tstar * ⟪a i, e⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos htstar_pos.le hnonpos
      linarith [hx_ext.1 i]
  have hx'_J₀ : x' ∈ faceOf a b J₀ := by
    refine ⟨hx'_P, ?_⟩
    intro j hj
    dsimp [x']
    rw [inner_add_right, real_inner_smul_right, hx_J₀.2 j hj, he_J₀ j hj]
    ring
  have hx'_ne : x' ≠ x := by
    intro h_eq
    have h0 : tstar • e = 0 := by
      have : (x + tstar • e) - x = 0 := by change x' - x = 0; rw [h_eq, sub_self]
      simpa using this
    rcases smul_eq_zero.mp h0 with h1 | h2
    · linarith
    · exact he_ne h2
  have hseg_eq : faceOf a b J₀ = segment ℝ x x' := by
    apply Set.Subset.antisymm
    · have he_dir : e ∈ (affineSpan ℝ (faceOf a b J₀)).direction := by
        rw [direction_affineSpan]
        have hmem := vsub_mem_vectorSpan ℝ hx'_J₀ hx_J₀
        have hdiff : x' -ᵥ x = tstar • e := by dsimp [x']; module
        rw [hdiff] at hmem
        have hsm := Submodule.smul_mem (vectorSpan ℝ (faceOf a b J₀)) tstar⁻¹ hmem
        rwa [inv_smul_smul₀ (ne_of_gt htstar_pos)] at hsm
      have hsub_span : (ℝ ∙ e) ≤ (affineSpan ℝ (faceOf a b J₀)).direction := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact he_dir
      have hdir_eq : (ℝ ∙ e) = (affineSpan ℝ (faceOf a b J₀)).direction :=
        Submodule.eq_of_le_of_finrank_eq hsub_span
          ((finrank_span_singleton_eq_one he_ne).trans hdim_J₀.symm)
      intro z hz
      have hz_dir : z - x ∈ (ℝ ∙ e) := by
        rw [hdir_eq, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hz hx_J₀
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hz_dir
      have hz_eq : z = x + s • e := by
        calc z = x + (z - x) := by module
          _ = x + s • e := by rw [hs]
      have hs0 : 0 ≤ s := by
        have hzi₀ : ⟪a i₀, z⟫ ≤ b i₀ := hz.1 i₀
        rw [hz_eq, inner_add_right, real_inner_smul_right,
          mem_tightFinset.mp hi₀, he_i₀] at hzi₀
        linarith
      have hst : s ≤ tstar := le_csSup hbdd ⟨hs0, hz_eq ▸ hz.1⟩
      refine ⟨1 - s / tstar, s / tstar,
        sub_nonneg.mpr ((div_le_one htstar_pos).mpr hst),
        div_nonneg hs0 htstar_pos.le, by ring, ?_⟩
      dsimp [x']
      rw [hz_eq, smul_add, smul_smul, ← add_assoc, ← add_smul]
      have hc1 : (1 - s / tstar) + s / tstar = (1 : ℝ) := by ring
      have hc2 : (s / tstar) * tstar = s := div_mul_cancel₀ s (ne_of_gt htstar_pos)
      rw [hc1, hc2, one_smul]
    · exact (faceOf_convex a b J₀).segment_subset hx_J₀ hx'_J₀
  have hadj : Hirsch.Adj (Hirsch.Hpoly a b) x x' :=
    ⟨hx'_ne.symm, hseg_eq ▸ isExtreme_faceOf a b J₀⟩
  have hx'_ext : x' ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) :=
    adj_right_mem_extremePoints hadj
  have hi₀_nx' : i₀ ∉ tightFinset a b x' := by
    rw [mem_tightFinset]
    dsimp [x']
    rw [inner_add_right, real_inner_smul_right, mem_tightFinset.mp hi₀, he_i₀]
    linarith
  have hsdiff_sub : tightFinset a b x \ {i₀} ⊆ tightFinset a b x' := by
    rw [Finset.sdiff_singleton_eq_erase]
    intro j hj
    exact mem_tightFinset.mpr (hx'_J₀.2 j hj)
  exact ⟨x', hx'_ext, hx'_ne,
    ⟨⟨x, left_mem_segment ℝ x x'⟩, J₀, hseg_eq.symm⟩,
    hseg_eq ▸ hdim_J₀, hsdiff_sub, hi₀_nx'⟩

noncomputable def rieszVec {m : ℕ} (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm ℓ.toContinuousLinearMap

lemma inner_rieszVec {m : ℕ} (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ)
    (u : EuclideanSpace ℝ (Fin m)) :
    ⟪rieszVec ℓ, u⟫ = ℓ u := by
  unfold rieszVec
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

lemma interior_nonempty_of_pos_rhs {m n : ℕ} (hn : 0 < n)
    (a' : Fin n → EuclideanSpace ℝ (Fin m)) (b' : Fin n → ℝ)
    (hb' : ∀ r, 0 < b' r) :
    (interior (Hirsch.Hpoly a' b')).Nonempty := by
  classical
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let δ : ℝ := Finset.univ.inf' huniv_ne (fun r => b' r / (‖a' r‖ + 1))
  have hδ_pos : 0 < δ := by
    rw [Finset.lt_inf'_iff]
    intro r _
    exact div_pos (hb' r) (by positivity)
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨δ, hδ_pos, ?_⟩
  intro w hw r
  have hw_norm : ‖w‖ < δ := by simpa using hw
  have hδ_le : δ ≤ b' r / (‖a' r‖ + 1) := Finset.inf'_le _ (Finset.mem_univ r)
  have h1 : ⟪a' r, w⟫ ≤ ‖a' r‖ * ‖w‖ := real_inner_le_norm _ _
  have h2 : ‖a' r‖ * ‖w‖ ≤ (‖a' r‖ + 1) * δ := by
    calc ‖a' r‖ * ‖w‖
        ≤ (‖a' r‖ + 1) * ‖w‖ := by
            exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg w)
      _ ≤ (‖a' r‖ + 1) * δ := by
            exact mul_le_mul_of_nonneg_left hw_norm.le (by positivity)
  have h3 : (‖a' r‖ + 1) * δ ≤ b' r := by
    have hpos : 0 < ‖a' r‖ + 1 := by positivity
    have := (le_div_iff₀ hpos).mp hδ_le
    linarith
  linarith

lemma irredundant_of_tight_at_simple_vertex {m n : ℕ}
    (a' : Fin n → EuclideanSpace ℝ (Fin m)) (b' : Fin n → ℝ)
    {w : EuclideanSpace ℝ (Fin m)} (hw : w ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b'))
    (hcard_w : (TightSet a' b' w).ncard = m)
    {r : Fin n} (hr : r ∈ tightFinset a' b' w) :
    ∃ z : EuclideanSpace ℝ (Fin m), (∀ s, s ≠ r → ⟪a' s, z⟫ ≤ b' s) ∧ b' r < ⟪a' r, z⟫ := by
  classical
  let E_w := tightEquiv a' b' hw hcard_w
  let e : EuclideanSpace ℝ (Fin m) := E_w.symm (fun k => if k.1 = r then 1 else 0)
  have he_eval : ∀ s : Fin n, ∀ hs : s ∈ tightFinset a' b' w,
      ⟪a' s, e⟫ = if s = r then 1 else 0 := by
    intro s hs
    change E_w e ⟨s, hs⟩ = if s = r then 1 else 0
    simp [e]
  have he_r : ⟪a' r, e⟫ = 1 := by rw [he_eval r hr, if_pos rfl]
  let S_pos : Finset (Fin n) := (Finset.univ.erase r).filter (fun s => 0 < ⟪a' s, e⟫)
  have hS_pos : ∀ s ∈ S_pos, 0 < (b' s - ⟪a' s, w⟫) / ⟪a' s, e⟫ := by
    intro s hs
    obtain ⟨hs_er, hse_pos⟩ := Finset.mem_filter.mp hs
    have hs_ne : s ≠ r := (Finset.mem_erase.mp hs_er).1
    have hs_nT : s ∉ tightFinset a' b' w := by
      intro hsT
      have h0 := he_eval s hsT
      rw [if_neg hs_ne] at h0
      linarith
    have hlt : ⟪a' s, w⟫ < b' s :=
      lt_of_le_of_ne (hw.1 s) (by rwa [mem_tightFinset] at hs_nT)
    exact div_pos (sub_pos.mpr hlt) hse_pos
  let ε : ℝ :=
    if hSne : S_pos.Nonempty then S_pos.inf' hSne (fun s => (b' s - ⟪a' s, w⟫) / ⟪a' s, e⟫)
    else 1
  have hε_pos : 0 < ε := by
    dsimp [ε]
    split_ifs with hSne
    · exact (Finset.lt_inf'_iff hSne).mpr hS_pos
    · exact zero_lt_one
  refine ⟨w + ε • e, ?_, ?_⟩
  · intro s hs_ne
    rw [inner_add_right, real_inner_smul_right]
    rcases lt_or_ge 0 ⟪a' s, e⟫ with hpos | hnonpos
    · have hs_in : s ∈ S_pos :=
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hs_ne, Finset.mem_univ s⟩, hpos⟩
      have hSne : S_pos.Nonempty := ⟨s, hs_in⟩
      have hle : ε ≤ (b' s - ⟪a' s, w⟫) / ⟪a' s, e⟫ := by
        dsimp [ε]
        rw [dif_pos hSne]
        exact Finset.inf'_le _ hs_in
      have hmul : ε * ⟪a' s, e⟫ ≤ b' s - ⟪a' s, w⟫ := (le_div_iff₀ hpos).mp hle
      linarith
    · have hmul : ε * ⟪a' s, e⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_pos.le hnonpos
      linarith [hw.1 s]
  · rw [inner_add_right, real_inner_smul_right, mem_tightFinset.mp hr, he_r]
    linarith

lemma lift_facet_path {d d' k₂ k₄ : ℕ}
    (hk₂ : 0 < k₂) (hk₄ : 0 < k₄) (hd'_def : k₂ + 1 + k₄ = d') (hd_eq : d = d' + 1)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (hS : IsSimple a b)
    (x x' y : EuclideanSpace ℝ (Fin d))
    (hx'_face : IsFace a b (segment ℝ x x')) (hx'_dim : dim (segment ℝ x x') = 1)
    (hdisj : Disjoint (tightFinset a b x) (tightFinset a b y))
    (i₀ j₀ : Fin (2 * d))
    (hTx'_eq : tightFinset a b x' = insert j₀ (tightFinset a b x \ {i₀}))
    (S_idx : Finset (Fin (2 * d)))
    (hmem_S_idx : ∀ i : Fin (2 * d), i ∈ S_idx ↔ i ≠ j₀ ∧ i ≠ i₀)
    (eS : Fin (2 * d') ≃ S_idx)
    (a' : Fin (2 * d') → EuclideanSpace ℝ (Fin d'))
    (b' : Fin (2 * d') → ℝ) (hb'_pos : ∀ r : Fin (2 * d'), 0 < b' r)
    (liftZ : EuclideanSpace ℝ (Fin d') → EuclideanSpace ℝ (Fin d))
    (hliftZ_props : ∀ w ∈ Hirsch.Hpoly a' b',
      liftZ w ∈ Hirsch.Hpoly a b ∧
      ⟪a j₀, liftZ w⟫ = b j₀ ∧
      ⟪a i₀, liftZ w⟫ < b i₀ ∧
      ∀ r : Fin (2 * d'), ⟪a' r, w⟫ = b' r ↔ ⟪a (eS r).1, liftZ w⟫ = b (eS r).1)
    (hliftZ_ext : ∀ w ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b'),
      liftZ w ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (wx wy : EuclideanSpace ℝ (Fin d'))
    (hwx_ext : wx ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b'))
    (hwy_ext : wy ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b'))
    (hlift_wx : liftZ wx = x') (hlift_wy : liftZ wy = y) :
    IsFacialPath a b [1, k₂, 1, k₄] x y := by
  classical
  have htight_map : ∀ w ∈ Hirsch.Hpoly a' b',
      (tightFinset a' b' w).card = (tightFinset a b (liftZ w) \ {j₀}).card := by
    intro w hw
    obtain ⟨_, hzj₀, hzi₀, hiff⟩ := hliftZ_props w hw
    have himg_eq : (tightFinset a' b' w).image (fun r => (eS r).1) =
        tightFinset a b (liftZ w) \ {j₀} := by
      ext i
      simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton, mem_tightFinset]
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨(hiff r).mp hr, ((hmem_S_idx (eS r).1).mp (eS r).2).1⟩
      · rintro ⟨hi_Tz, hne_j₀⟩
        have hne_i₀ : i ≠ i₀ := by
          intro hii₀
          subst hii₀
          linarith
        have hiS : i ∈ S_idx := (hmem_S_idx i).mpr ⟨hne_j₀, hne_i₀⟩
        let r : Fin (2 * d') := eS.symm ⟨i, hiS⟩
        have hr : (eS r).1 = i := by simp [r]
        refine ⟨r, ?_, hr⟩
        rw [hiff r, hr]
        exact hi_Tz
    rw [← himg_eq]
    exact (Finset.card_image_of_injective (tightFinset a' b' w)
      (fun r₁ r₂ heq => eS.injective (Subtype.ext heq))).symm
  have hS' : IsSimple a' b' := by
    refine ⟨⟨wx, hwx_ext⟩, ?_⟩
    intro w hw_ext
    rw [← card_tightFinset_eq_ncard, htight_map w hw_ext.1]
    have hz_ext := hliftZ_ext w hw_ext
    have hz_card : (tightFinset a b (liftZ w)).card = d := by
      rw [card_tightFinset_eq_ncard, hS.2 (liftZ w) hz_ext]
    have hj₀_in : j₀ ∈ tightFinset a b (liftZ w) :=
      mem_tightFinset.mpr (hliftZ_props w hw_ext.1).2.1
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hj₀_in, hz_card, hd_eq]
    exact Nat.add_sub_cancel d' 1
  have hTwx_ncard : (TightSet a' b' wx).ncard = d' := hS'.2 wx hwx_ext
  have hTwy_ncard : (TightSet a' b' wy).ncard = d' := hS'.2 wy hwy_ext
  have hdisj_w : Disjoint (TightSet a' b' wx) (TightSet a' b' wy) := by
    rw [Set.disjoint_left]
    intro r hr_x hr_y
    have hzx : ⟪a (eS r).1, x'⟫ = b (eS r).1 := by
      rw [← hlift_wx]
      exact ((hliftZ_props wx hwx_ext.1).2.2.2 r).mp hr_x
    have hzy : ⟪a (eS r).1, y⟫ = b (eS r).1 := by
      rw [← hlift_wy]
      exact ((hliftZ_props wy hwy_ext.1).2.2.2 r).mp hr_y
    have hr_Tx' : (eS r).1 ∈ tightFinset a b x' := mem_tightFinset.mpr hzx
    have hr_Ty : (eS r).1 ∈ tightFinset a b y := mem_tightFinset.mpr hzy
    rw [hTx'_eq] at hr_Tx'
    rcases Finset.mem_insert.mp hr_Tx' with heq_j₀ | hsx
    · exact ((hmem_S_idx (eS r).1).mp (eS r).2).1 heq_j₀
    · exact Finset.disjoint_left.mp hdisj (Finset.mem_sdiff.mp hsx).1 hr_Ty
  have hdisj_w_fin : Disjoint (tightFinset a' b' wx) (tightFinset a' b' wy) := by
    rw [Finset.disjoint_left]
    intro r hrx hry
    exact Set.disjoint_left.mp hdisj_w (mem_tightFinset.mp hrx) (mem_tightFinset.mp hry)
  have huniv_w : tightFinset a' b' wx ∪ tightFinset a' b' wy = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj_w_fin,
      card_tightFinset_eq_ncard, hTwx_ncard,
      card_tightFinset_eq_ncard, hTwy_ncard, Fintype.card_fin]
    exact (two_mul d').symm
  have hn_pos : 0 < 2 * d' := by
    rw [← hd'_def]
    positivity
  have hF' : IsFacetPresentation a' b' := by
    refine ⟨interior_nonempty_of_pos_rhs hn_pos a' b' hb'_pos, ?_⟩
    intro r
    have hru : r ∈ tightFinset a' b' wx ∪ tightFinset a' b' wy := by
      rw [huniv_w]; exact Finset.mem_univ r
    rcases Finset.mem_union.mp hru with hrx | hry
    · exact irredundant_of_tight_at_simple_vertex a' b' hwx_ext hTwx_ncard hrx
    · exact irredundant_of_tight_at_simple_vertex a' b' hwy_ext hTwy_ncard hry
  have hD' : IsDantzigFigure a' b' wx wy :=
    ⟨hF', hwx_ext, hwy_ext, hTwx_ncard, hTwy_ncard, hdisj_w⟩
  obtain ⟨K', hK'_face, hK'_adj, _, hwx0, hwy2⟩ :=
    KleeWalkup67.FiveStep.proposition_3_4_a a' b' wx wy hD' hS' k₂ k₄ hk₂ hk₄ hd'_def
  let liftSet : Finset (Fin (2 * d')) → Finset (Fin (2 * d)) := fun I' =>
    insert j₀ (I'.image (fun r => (eS r).1))
  have hmem_lift_face : ∀ (I' : Finset (Fin (2 * d'))) (w : EuclideanSpace ℝ (Fin d')),
      w ∈ faceOf a' b' I' → liftZ w ∈ faceOf a b (liftSet I') := by
    intro I' w hwI'
    obtain ⟨hzP, hzj₀, _, hiff⟩ := hliftZ_props w hwI'.1
    refine ⟨hzP, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | himg
    · exact hzj₀
    · obtain ⟨r, hrI', rfl⟩ := Finset.mem_image.mp himg
      exact (hiff r).mp (hwI'.2 r hrI')
  have hlift_face_dim : ∀ (I' : Finset (Fin (2 * d'))) (k : ℕ),
      (faceOf a' b' I').Nonempty → dim (faceOf a' b' I') = k →
      IsFace a b (faceOf a b (liftSet I')) ∧ dim (faceOf a b (liftSet I')) = k := by
    intro I' k hne' hdim'
    obtain ⟨w, hw_ext, hwI'⟩ := nonempty_faceOf_has_vertex a' b' hwx_ext I' hne'
    have hw_ncard : (TightSet a' b' w).ncard = d' := hS'.2 w hw_ext
    obtain ⟨_, hd_calc'⟩ := dim_faceOf_at_simple_vertex a' b' hw_ext hw_ncard I' hwI'
    have hzj₀_not_img : j₀ ∉ I'.image (fun r => (eS r).1) := by
      intro himg
      obtain ⟨r, _, hreq⟩ := Finset.mem_image.mp himg
      exact ((hmem_S_idx (eS r).1).mp (eS r).2).1 hreq
    have himg_card : (I'.image (fun r => (eS r).1)).card = I'.card := by
      refine Finset.card_image_of_injective I' ?_
      intro r₁ r₂ h12
      exact eS.injective (Subtype.ext h12)
    have hlift_card : (liftSet I').card = I'.card + 1 := by
      dsimp [liftSet]
      rw [Finset.card_insert_of_notMem hzj₀_not_img, himg_card]
    have hz_ext : liftZ w ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) := hliftZ_ext w hw_ext
    have hz_mem : liftZ w ∈ faceOf a b (liftSet I') := hmem_lift_face I' w hwI'
    have hz_ncard : (TightSet a b (liftZ w)).ncard = d := hS.2 (liftZ w) hz_ext
    have hd_calc := (dim_faceOf_at_simple_vertex a b hz_ext hz_ncard (liftSet I') hz_mem).2
    refine ⟨⟨⟨liftZ w, hz_mem⟩, liftSet I', rfl⟩, ?_⟩
    rw [hd_calc, hlift_card, hd_eq, Nat.add_sub_add_right, ← hd_calc', hdim']
  obtain ⟨⟨hne0, I'₀, hK'0⟩, hdim'0⟩ := hK'_face ⟨0, by simp⟩
  obtain ⟨⟨hne1, I'₁, hK'1⟩, hdim'1⟩ := hK'_face ⟨1, by simp⟩
  obtain ⟨⟨hne2, I'₂, hK'2⟩, hdim'2⟩ := hK'_face ⟨2, by simp⟩
  rw [hK'0] at hdim'0
  rw [hK'1] at hdim'1
  rw [hK'2] at hdim'2
  have hf0 := hlift_face_dim I'₀ k₂ (hK'0 ▸ hne0) (by simpa using hdim'0)
  have hf1 := hlift_face_dim I'₁ 1 (hK'1 ▸ hne1) (by simpa using hdim'1)
  have hf2 := hlift_face_dim I'₂ k₄ (hK'2 ▸ hne2) (by simpa using hdim'2)
  let K : Fin [1, k₂, 1, k₄].length → Set (EuclideanSpace ℝ (Fin d)) :=
    ![segment ℝ x x', faceOf a b (liftSet I'₀), faceOf a b (liftSet I'₁), faceOf a b (liftSet I'₂)]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro idx
    fin_cases idx
    · exact ⟨hx'_face, hx'_dim⟩
    · exact hf0
    · exact hf1
    · exact hf2
  · intro idx₁ idx₂ hnext
    fin_cases idx₁ <;> fin_cases idx₂ <;> simp at hnext ⊢
    · have hwx_I'₀ : wx ∈ faceOf a' b' I'₀ := by
        have h0 : wx ∈ K' ⟨0, by simp⟩ := hwx0
        rwa [hK'0] at h0
      have hx'_in0 : x' ∈ faceOf a b (liftSet I'₀) := by
        rw [← hlift_wx]
        exact hmem_lift_face I'₀ wx hwx_I'₀
      exact ⟨x', right_mem_segment ℝ x x', hx'_in0⟩
    · obtain ⟨w01, hw0, hw1⟩ := hK'_adj ⟨0, by simp⟩ ⟨1, by simp⟩ rfl
      rw [hK'0] at hw0
      rw [hK'1] at hw1
      exact ⟨liftZ w01, hmem_lift_face I'₀ w01 hw0, hmem_lift_face I'₁ w01 hw1⟩
    · obtain ⟨w12, hw1, hw2⟩ := hK'_adj ⟨1, by simp⟩ ⟨2, by simp⟩ rfl
      rw [hK'1] at hw1
      rw [hK'2] at hw2
      exact ⟨liftZ w12, hmem_lift_face I'₁ w12 hw1, hmem_lift_face I'₂ w12 hw2⟩
  · have hlen4 : 0 < [1, k₂, 1, k₄].length := by simp
    have hwy_I'₂ : wy ∈ faceOf a' b' I'₂ := by
      have h2 : wy ∈ K' ⟨2, by simp⟩ := hwy2
      rwa [hK'2] at h2
    have hy_in2 : y ∈ faceOf a b (liftSet I'₂) := by
      rw [← hlift_wy]
      exact hmem_lift_face I'₂ wy hwy_I'₂
    exact ⟨hlen4, by simpa [K] using left_mem_segment ℝ x x', by simpa [K] using hy_in2⟩

end Aux_KW67_proposition_3_4_b

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep Aux_KW67_proposition_3_4_b

theorem solution {d : ℕ}
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (hB : Bornology.IsBounded (Hirsch.Hpoly a b))
    (k₂ k₄ : ℕ) (hk₂ : 0 < k₂) (hk₄ : 0 < k₄) (hsum : 1 + k₂ + 1 + k₄ = d) :
    IsFacialPath a b [1, k₂, 1, k₄] x y := by
  classical
  have hd4 : 4 ≤ d := by omega
  let d' : ℕ := k₂ + 1 + k₄
  have hd_eq : d = d' + 1 := by dsimp [d']; omega
  have hd'3 : 3 ≤ d' := by dsimp [d']; omega
  obtain ⟨_, hx_ext, hy_ext, hx_ncard, hy_ncard, hdisj_set⟩ := hD
  have hTx_card : (tightFinset a b x).card = d := by rw [card_tightFinset_eq_ncard, hx_ncard]
  have hTy_card : (tightFinset a b y).card = d := by rw [card_tightFinset_eq_ncard, hy_ncard]
  have hdisj : Disjoint (tightFinset a b x) (tightFinset a b y) := by
    rw [Finset.disjoint_left]
    intro i hix hiy
    exact Set.disjoint_left.mp hdisj_set (mem_tightFinset.mp hix) (mem_tightFinset.mp hiy)
  have huniv : tightFinset a b x ∪ tightFinset a b y = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hTx_card, hTy_card]
    simp
    omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < (tightFinset a b x).card)
  obtain ⟨x', hx'_ext, _, hx'_face, hx'_dim, hTx_sdiff_x', hi₀_nx'⟩ :=
    exists_bounded_edge_from_simple_vertex (by omega) a b hB hx_ext hx_ncard hi₀
  have hcard_x' : (TightSet a b x').ncard = d := hS.2 x' hx'_ext
  have hTx'_card : (tightFinset a b x').card = d := by rw [card_tightFinset_eq_ncard, hcard_x']
  have hsdiff_x'_one : (tightFinset a b x' \ (tightFinset a b x \ {i₀})).card = 1 := by
    have hs := Finset.card_sdiff_add_card_eq_card hTx_sdiff_x'
    have hc : (tightFinset a b x \ {i₀}).card = d - 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hi₀, hTx_card]
    omega
  obtain ⟨j₀, hj₀_eq⟩ := Finset.card_eq_one.mp hsdiff_x'_one
  have hj₀_mem : j₀ ∈ tightFinset a b x' \ (tightFinset a b x \ {i₀}) :=
    hj₀_eq ▸ Finset.mem_singleton_self j₀
  obtain ⟨hj₀_Tx', hj₀_not_sdiff⟩ := Finset.mem_sdiff.mp hj₀_mem
  have hj₀_ne_i₀ : j₀ ≠ i₀ := fun h => hi₀_nx' (h ▸ hj₀_Tx')
  have hj₀_nTx : j₀ ∉ tightFinset a b x := fun hjx =>
    hj₀_not_sdiff (Finset.mem_sdiff.mpr ⟨hjx, Finset.notMem_singleton.mpr hj₀_ne_i₀⟩)
  have hj₀_Ty : j₀ ∈ tightFinset a b y := by
    have hu : j₀ ∈ tightFinset a b x ∪ tightFinset a b y := by rw [huniv]; exact Finset.mem_univ j₀
    rcases Finset.mem_union.mp hu with h1 | h2
    · exact absurd h1 hj₀_nTx
    · exact h2
  have hTx'_eq : tightFinset a b x' = insert j₀ (tightFinset a b x \ {i₀}) := by
    ext i
    simp only [Finset.mem_insert]
    constructor
    · intro hix'
      by_cases his : i ∈ tightFinset a b x \ {i₀}
      · exact Or.inr his
      · have hsd : i ∈ tightFinset a b x' \ (tightFinset a b x \ {i₀}) :=
          Finset.mem_sdiff.mpr ⟨hix', his⟩
        rw [hj₀_eq, Finset.mem_singleton] at hsd
        exact Or.inl hsd
    · rintro (rfl | his)
      · exact hj₀_Tx'
      · exact hTx_sdiff_x' his
  -- Midpoint c of x' and y has exact tight set {j₀}
  let c : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • x' + (1 / 2 : ℝ) • y
  have hc_P : c ∈ Hirsch.Hpoly a b :=
    hpoly_convex a b hx'_ext.1 hy_ext.1 (by norm_num) (by norm_num) (by norm_num)
  have hc_j₀ : ⟪a j₀, c⟫ = b j₀ := by
    dsimp [c]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      mem_tightFinset.mp hj₀_Tx', mem_tightFinset.mp hj₀_Ty]
    ring
  have hc_strict : ∀ i : Fin (2 * d), i ≠ j₀ → ⟪a i, c⟫ < b i := by
    intro i hi_ne
    dsimp [c]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 : ⟪a i, x'⟫ ≤ b i := hx'_ext.1 i
    have h2 : ⟪a i, y⟫ ≤ b i := hy_ext.1 i
    by_contra hge
    have heq1 : ⟪a i, x'⟫ = b i := by linarith
    have heq2 : ⟪a i, y⟫ = b i := by linarith
    have hi_Tx' : i ∈ tightFinset a b x' := mem_tightFinset.mpr heq1
    have hi_Ty : i ∈ tightFinset a b y := mem_tightFinset.mpr heq2
    rw [hTx'_eq] at hi_Tx'
    rcases Finset.mem_insert.mp hi_Tx' with rfl | his
    · exact hi_ne rfl
    · exact Finset.disjoint_left.mp hdisj (Finset.mem_sdiff.mp his).1 hi_Ty
  -- Subspace H₀ = {v | ⟪a j₀, v⟫ = 0} of dimension d'
  let H₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    (zeroOnSubmodule (tightFinset a b y) {j₀}).comap (tightEquiv a b hy_ext hy_ncard).toLinearMap
  have hmem_H₀ : ∀ v : EuclideanSpace ℝ (Fin d), v ∈ H₀ ↔ ⟪a j₀, v⟫ = 0 := by
    intro v
    change (∀ k : tightFinset a b y, k.1 ∈ ({j₀} : Finset (Fin (2 * d))) → ⟪a k.1, v⟫ = 0) ↔
      ⟪a j₀, v⟫ = 0
    constructor
    · intro hv
      exact hv ⟨j₀, hj₀_Ty⟩ (Finset.mem_singleton_self j₀)
    · intro hv0 k hk
      rw [Finset.mem_singleton.mp hk]
      exact hv0
  have hfr_H₀ : Module.finrank ℝ H₀ = d' := by
    have hf := finrank_zeroOn_comap a b hy_ext hy_ncard {j₀}
      (Finset.singleton_subset_iff.mpr hj₀_Ty)
    change Module.finrank ℝ H₀ = d - ({j₀} : Finset (Fin (2 * d))).card at hf
    rw [Finset.card_singleton] at hf
    omega
  obtain ⟨L⟩ : Nonempty (EuclideanSpace ℝ (Fin d') ≃ₗ[ℝ] H₀) :=
    ⟨LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin d')) H₀ (by simp [hfr_H₀])⟩
  obtain ⟨atilde, hatilde⟩ : ∃ atilde : Fin (2 * d) → EuclideanSpace ℝ (Fin d'),
      ∀ (i : Fin (2 * d)) (u : EuclideanSpace ℝ (Fin d')), ⟪atilde i, u⟫ = ⟪a i, (L u).1⟫ :=
    ⟨fun i => rieszVec
        { toFun := fun u => ⟪a i, (L u).1⟫
          map_add' := fun u₁ u₂ => by simp [inner_add_right]
          map_smul' := fun r u => by simp [real_inner_smul_right] },
      fun i u => inner_rieszVec _ u⟩
  let btilde : Fin (2 * d) → ℝ := fun i => b i - ⟪a i, c⟫
  have hbtilde_pos : ∀ i : Fin (2 * d), i ≠ j₀ → 0 < btilde i := fun i hne =>
    sub_pos.mpr (hc_strict i hne)
  have hbtilde_i₀_pos : 0 < btilde i₀ := hbtilde_pos i₀ hj₀_ne_i₀.symm
  -- Remaining 2 * d' indices S = Finset.univ \ {i₀, j₀}
  let S_idx : Finset (Fin (2 * d)) := (Finset.univ.erase i₀).erase j₀
  have hmem_S_idx : ∀ i : Fin (2 * d), i ∈ S_idx ↔ i ≠ j₀ ∧ i ≠ i₀ := by
    intro i
    simp [S_idx]
  have hS_idx_card : S_idx.card = 2 * d' := by
    have h1 : i₀ ∈ (Finset.univ : Finset (Fin (2 * d))) := Finset.mem_univ i₀
    have h2 : j₀ ∈ (Finset.univ : Finset (Fin (2 * d))).erase i₀ :=
      Finset.mem_erase.mpr ⟨hj₀_ne_i₀, Finset.mem_univ j₀⟩
    dsimp [S_idx]
    rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1, Finset.card_fin]
    omega
  obtain ⟨eS⟩ : Nonempty (Fin (2 * d') ≃ S_idx) :=
    ⟨(S_idx.equivFinOfCardEq hS_idx_card).symm⟩
  let b' : Fin (2 * d') → ℝ := fun r => btilde (eS r).1 / btilde i₀
  let a' : Fin (2 * d') → EuclideanSpace ℝ (Fin d') := fun r =>
    atilde (eS r).1 - b' r • atilde i₀
  have hb'_pos : ∀ r : Fin (2 * d'), 0 < b' r := by
    intro r
    exact div_pos (hbtilde_pos (eS r).1 ((hmem_S_idx (eS r).1).mp (eS r).2).1) hbtilde_i₀_pos
  -- Positivity of projective denominator 1 + ⟪atilde i₀, w⟫ > 0 on Hpoly a' b'
  have hdenom_pos : ∀ w ∈ Hirsch.Hpoly a' b', 0 < 1 + ⟪atilde i₀, w⟫ := by
    intro w hw
    by_contra hle
    push Not at hle
    have hneg_ge1 : 1 ≤ -⟪atilde i₀, w⟫ := by linarith
    have hneg_pos : 0 < -⟪atilde i₀, w⟫ := by linarith
    let s : ℝ := 1 / (-⟪atilde i₀, w⟫)
    have hs_pos : 0 < s := div_pos one_pos hneg_pos
    have hs_le1 : s ≤ 1 := (div_le_one hneg_pos).mpr hneg_ge1
    have h0_P' : (0 : EuclideanSpace ℝ (Fin d')) ∈ Hirsch.Hpoly a' b' := by
      intro r
      rw [inner_zero_right]
      exact (hb'_pos r).le
    let ws : EuclideanSpace ℝ (Fin d') := (1 - s) • (0 : EuclideanSpace ℝ (Fin d')) + s • w
    have hws_P' : ws ∈ Hirsch.Hpoly a' b' :=
      hpoly_convex a' b' h0_P' hw (sub_nonneg.mpr hs_le1) hs_pos.le (by ring)
    have hws_eq : ws = s • w := by dsimp [ws]; module
    have hws_i₀ : ⟪atilde i₀, ws⟫ = -1 := by
      have hne_neg : -⟪atilde i₀, w⟫ ≠ 0 := ne_of_gt hneg_pos
      rw [hws_eq, real_inner_smul_right]
      dsimp [s]
      calc (1 / -⟪atilde i₀, w⟫) * ⟪atilde i₀, w⟫
          = -((-⟪atilde i₀, w⟫) / (-⟪atilde i₀, w⟫)) := by ring
        _ = -1 := by rw [div_self hne_neg]
    have hws_S : ∀ i ∈ S_idx, ⟪atilde i, ws⟫ ≤ 0 := by
      intro i hiS
      let r : Fin (2 * d') := eS.symm ⟨i, hiS⟩
      have hr_eq : (eS r).1 = i := by simp [r]
      have hwr : ⟪a' r, ws⟫ ≤ b' r := hws_P' r
      dsimp [a'] at hwr
      rw [inner_sub_left, real_inner_smul_left, hr_eq, hws_i₀] at hwr
      linarith
    have hLws_ne : (L ws).1 ≠ 0 := by
      intro h0
      have hws0 : ws = 0 := L.injective (Subtype.ext (by simpa using h0))
      rw [hws0, inner_zero_right] at hws_i₀
      norm_num at hws_i₀
    have hLws_norm : 0 < ‖(L ws).1‖ := norm_pos_iff.mpr hLws_ne
    obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    have hc_norm : ‖c‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hc_P
    let M : ℝ := (R + ‖c‖ + 1) / ‖(L ws).1‖
    have hM_pos : 0 < M := div_pos (by linarith [norm_nonneg c]) hLws_norm
    have hray_in : c + M • (L ws).1 ∈ Hirsch.Hpoly a b := by
      intro i
      rw [inner_add_right, real_inner_smul_right]
      by_cases hij₀ : i = j₀
      · subst hij₀
        rw [hc_j₀, (hmem_H₀ (L ws).1).mp (L ws).2]
        linarith
      · by_cases hii₀ : i = i₀
        · subst hii₀
          have h1 : ⟪a i, (L ws).1⟫ = -1 := by rw [← hatilde, hws_i₀]
          rw [h1]
          linarith [hc_strict i hij₀]
        · have hiS : i ∈ S_idx := (hmem_S_idx i).mpr ⟨hij₀, hii₀⟩
          have h1 : ⟪a i, (L ws).1⟫ ≤ 0 := by rw [← hatilde]; exact hws_S i hiS
          have hmul : M * ⟪a i, (L ws).1⟫ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hM_pos.le h1
          linarith [hc_strict i hij₀]
    have hnorm_le : ‖c + M • (L ws).1‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hray_in
    have hM_mul : M * ‖(L ws).1‖ = R + ‖c‖ + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hLws_norm)
    have htri : M * ‖(L ws).1‖ ≤ R + ‖c‖ := by
      calc M * ‖(L ws).1‖
          = ‖M • (L ws).1‖ := by rw [norm_smul, Real.norm_of_nonneg hM_pos.le]
        _ = ‖(c + M • (L ws).1) - c‖ := by congr 1; module
        _ ≤ ‖c + M • (L ws).1‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ R + ‖c‖ := by linarith
    linarith
  -- Forward and inverse projective maps between F \ faceOf {i₀} and Hpoly a' b'
  obtain ⟨toU, htoU_sub⟩ :
      ∃ toU : ∀ z : EuclideanSpace ℝ (Fin d), ⟪a j₀, z⟫ = b j₀ → EuclideanSpace ℝ (Fin d'),
        ∀ (z : EuclideanSpace ℝ (Fin d)) (hz : ⟪a j₀, z⟫ = b j₀), (L (toU z hz)).1 = z - c := by
    refine ⟨fun z hz => L.symm ⟨z - c, (hmem_H₀ (z - c)).mpr
      (by rw [inner_sub_right, hz, hc_j₀, sub_self])⟩, ?_⟩
    intro z hz
    rw [L.apply_symm_apply]
  have htoU_spec : ∀ (z : EuclideanSpace ℝ (Fin d)) (hz : ⟪a j₀, z⟫ = b j₀),
      c + (L (toU z hz)).1 = z := by
    intro z hz
    rw [htoU_sub z hz]
    module
  have htoU_inner : ∀ (z : EuclideanSpace ℝ (Fin d)) (hz : ⟪a j₀, z⟫ = b j₀) (i : Fin (2 * d)),
      ⟪atilde i, toU z hz⟫ = ⟪a i, z⟫ - ⟪a i, c⟫ := by
    intro z hz i
    rw [hatilde, htoU_sub z hz, inner_sub_right]
  let Phi : EuclideanSpace ℝ (Fin d') → EuclideanSpace ℝ (Fin d') := fun u =>
    (1 / (btilde i₀ - ⟪atilde i₀, u⟫)) • u
  let Psi : EuclideanSpace ℝ (Fin d') → EuclideanSpace ℝ (Fin d') := fun w =>
    (btilde i₀ / (1 + ⟪atilde i₀, w⟫)) • w
  let liftZ : EuclideanSpace ℝ (Fin d') → EuclideanSpace ℝ (Fin d) := fun w =>
    c + (L (Psi w)).1
  have hPhi_Psi : ∀ w : EuclideanSpace ℝ (Fin d'), 0 < 1 + ⟪atilde i₀, w⟫ →
      btilde i₀ - ⟪atilde i₀, Psi w⟫ = btilde i₀ / (1 + ⟪atilde i₀, w⟫) ∧ Phi (Psi w) = w := by
    intro w hw_pos
    have hden_ne : 1 + ⟪atilde i₀, w⟫ ≠ 0 := ne_of_gt hw_pos
    have hbi₀_ne : btilde i₀ ≠ 0 := ne_of_gt hbtilde_i₀_pos
    have hsub : btilde i₀ - ⟪atilde i₀, Psi w⟫ = btilde i₀ / (1 + ⟪atilde i₀, w⟫) := by
      dsimp [Psi]
      rw [real_inner_smul_right]
      field_simp [hden_ne]
      ring
    refine ⟨hsub, ?_⟩
    dsimp [Phi]
    rw [hsub]
    dsimp [Psi]
    rw [smul_smul]
    have hc1 : (1 / (btilde i₀ / (1 + ⟪atilde i₀, w⟫))) *
        (btilde i₀ / (1 + ⟪atilde i₀, w⟫)) = (1 : ℝ) := by
      field_simp [hden_ne, hbi₀_ne]
    rw [hc1, one_smul]
  have hPsi_Phi : ∀ u : EuclideanSpace ℝ (Fin d'), 0 < btilde i₀ - ⟪atilde i₀, u⟫ →
      1 + ⟪atilde i₀, Phi u⟫ = btilde i₀ / (btilde i₀ - ⟪atilde i₀, u⟫) ∧ Psi (Phi u) = u := by
    intro u hu_pos
    have hden_ne : btilde i₀ - ⟪atilde i₀, u⟫ ≠ 0 := ne_of_gt hu_pos
    have hbi₀_ne : btilde i₀ ≠ 0 := ne_of_gt hbtilde_i₀_pos
    have hadd : 1 + ⟪atilde i₀, Phi u⟫ = btilde i₀ / (btilde i₀ - ⟪atilde i₀, u⟫) := by
      dsimp [Phi]
      rw [real_inner_smul_right]
      field_simp [hden_ne]
      ring
    refine ⟨hadd, ?_⟩
    dsimp [Psi]
    rw [hadd]
    dsimp [Phi]
    rw [smul_smul]
    have hc1 : (btilde i₀ / (btilde i₀ / (btilde i₀ - ⟪atilde i₀, u⟫))) *
        (1 / (btilde i₀ - ⟪atilde i₀, u⟫)) = (1 : ℝ) := by
      field_simp [hden_ne, hbi₀_ne]
    rw [hc1, one_smul]
  -- Algebraic identity relating row r in P' to row eS r in P
  have hrow_rel : ∀ (w : EuclideanSpace ℝ (Fin d')) (hw_pos : 0 < 1 + ⟪atilde i₀, w⟫)
      (r : Fin (2 * d')),
      ⟪a (eS r).1, liftZ w⟫ - b (eS r).1 =
        (btilde i₀ / (1 + ⟪atilde i₀, w⟫)) * (⟪a' r, w⟫ - b' r) := by
    intro w hw_pos r
    have hden_ne : 1 + ⟪atilde i₀, w⟫ ≠ 0 := ne_of_gt hw_pos
    have hbi₀_ne : btilde i₀ ≠ 0 := ne_of_gt hbtilde_i₀_pos
    have hbt_r : b (eS r).1 = ⟪a (eS r).1, c⟫ + btilde (eS r).1 := by dsimp [btilde]; ring
    dsimp [liftZ, Psi, a', b']
    rw [inner_add_right, ← hatilde, real_inner_smul_right,
      inner_sub_left, real_inner_smul_left, hbt_r]
    field_simp [hden_ne, hbi₀_ne]
    ring
  have hliftZ_props : ∀ w ∈ Hirsch.Hpoly a' b',
      liftZ w ∈ Hirsch.Hpoly a b ∧
      ⟪a j₀, liftZ w⟫ = b j₀ ∧
      ⟪a i₀, liftZ w⟫ < b i₀ ∧
      ∀ r : Fin (2 * d'), ⟪a' r, w⟫ = b' r ↔ ⟪a (eS r).1, liftZ w⟫ = b (eS r).1 := by
    intro w hw
    have hw_pos : 0 < 1 + ⟪atilde i₀, w⟫ := hdenom_pos w hw
    have hfac_pos : 0 < btilde i₀ / (1 + ⟪atilde i₀, w⟫) := div_pos hbtilde_i₀_pos hw_pos
    have hj₀_eq' : ⟪a j₀, liftZ w⟫ = b j₀ := by
      dsimp [liftZ]
      rw [inner_add_right, hc_j₀, (hmem_H₀ (L (Psi w)).1).mp (L (Psi w)).2, add_zero]
    have hi₀_lt : ⟪a i₀, liftZ w⟫ < b i₀ := by
      have hsub := (hPhi_Psi w hw_pos).1
      have h1 : ⟪a i₀, liftZ w⟫ - ⟪a i₀, c⟫ = ⟪atilde i₀, Psi w⟫ := by
        dsimp [liftZ]
        rw [inner_add_right, hatilde]
        ring
      dsimp [btilde] at hsub
      linarith
    refine ⟨?_, hj₀_eq', hi₀_lt, ?_⟩
    · intro i
      by_cases hij₀ : i = j₀
      · subst hij₀; exact hj₀_eq'.le
      · by_cases hii₀ : i = i₀
        · subst hii₀; exact hi₀_lt.le
        · have hiS : i ∈ S_idx := (hmem_S_idx i).mpr ⟨hij₀, hii₀⟩
          let r : Fin (2 * d') := eS.symm ⟨i, hiS⟩
          have hr : (eS r).1 = i := by simp [r]
          have hrel := hrow_rel w hw_pos r
          rw [hr] at hrel
          have hwr : ⟪a' r, w⟫ - b' r ≤ 0 := sub_nonpos.mpr (hw r)
          have hmul : (btilde i₀ / (1 + ⟪atilde i₀, w⟫)) * (⟪a' r, w⟫ - b' r) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hfac_pos.le hwr
          linarith
    · intro r
      have hrel := hrow_rel w hw_pos r
      have hfac_ne : btilde i₀ / (1 + ⟪atilde i₀, w⟫) ≠ 0 := ne_of_gt hfac_pos
      constructor
      · intro h_eq
        have : ⟪a (eS r).1, liftZ w⟫ - b (eS r).1 = 0 := by rw [hrel, h_eq, sub_self, mul_zero]
        linarith
      · intro h_eq
        have h0 : (btilde i₀ / (1 + ⟪atilde i₀, w⟫)) * (⟪a' r, w⟫ - b' r) = 0 := by
          rw [← hrel, h_eq, sub_self]
        rcases mul_eq_zero.mp h0 with h1 | h2
        · exact absurd h1 hfac_ne
        · linarith
  have hPhi_in_P' : ∀ (z : EuclideanSpace ℝ (Fin d)) (hzP : z ∈ Hirsch.Hpoly a b)
      (hzj₀ : ⟪a j₀, z⟫ = b j₀) (hzi₀ : ⟪a i₀, z⟫ < b i₀),
      0 < btilde i₀ - ⟪atilde i₀, toU z hzj₀⟫ ∧
      Phi (toU z hzj₀) ∈ Hirsch.Hpoly a' b' ∧
      liftZ (Phi (toU z hzj₀)) = z := by
    intro z hzP hzj₀ hzi₀
    have hden : btilde i₀ - ⟪atilde i₀, toU z hzj₀⟫ = b i₀ - ⟪a i₀, z⟫ := by
      rw [htoU_inner z hzj₀ i₀]
      dsimp [btilde]
      ring
    have hden_pos : 0 < btilde i₀ - ⟪atilde i₀, toU z hzj₀⟫ := by linarith
    obtain ⟨h1pos_eq, hPsiPhi⟩ := hPsi_Phi (toU z hzj₀) hden_pos
    have h1pos : 0 < 1 + ⟪atilde i₀, Phi (toU z hzj₀)⟫ := by
      rw [h1pos_eq]
      exact div_pos hbtilde_i₀_pos hden_pos
    have hlift_eq : liftZ (Phi (toU z hzj₀)) = z := by
      dsimp [liftZ]
      rw [hPsiPhi]
      exact htoU_spec z hzj₀
    refine ⟨hden_pos, ?_, hlift_eq⟩
    intro r
    have hrel := hrow_rel (Phi (toU z hzj₀)) h1pos r
    rw [hlift_eq] at hrel
    have hfac_pos : 0 < btilde i₀ / (1 + ⟪atilde i₀, Phi (toU z hzj₀)⟫) :=
      div_pos hbtilde_i₀_pos h1pos
    have hzr : ⟪a (eS r).1, z⟫ - b (eS r).1 ≤ 0 := sub_nonpos.mpr (hzP (eS r).1)
    rw [hrel] at hzr
    have hsub_le : ⟪a' r, Phi (toU z hzj₀)⟫ - b' r ≤ 0 :=
      nonpos_of_mul_nonpos_right hzr hfac_pos
    linarith
  -- Extreme point preservation in both directions
  have hliftZ_ext : ∀ w ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b'),
      liftZ w ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) := by
    intro w hw_ext
    obtain ⟨hzP, hzj₀, hzi₀, _⟩ := hliftZ_props w hw_ext.1
    refine ⟨hzP, ?_⟩
    rintro z₁ hz₁ z₂ hz₂ ⟨p, q, hp, hq, hpq, hcomb⟩
    let z₁' : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • liftZ w + (1 / 2 : ℝ) • z₁
    let z₂' : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • liftZ w + (1 / 2 : ℝ) • z₂
    have hz₁'_P : z₁' ∈ Hirsch.Hpoly a b :=
      hpoly_convex a b hzP hz₁ (by norm_num) (by norm_num) (by norm_num)
    have hz₂'_P : z₂' ∈ Hirsch.Hpoly a b :=
      hpoly_convex a b hzP hz₂ (by norm_num) (by norm_num) (by norm_num)
    have hlin_j₀ : p * ⟪a j₀, z₁⟫ + q * ⟪a j₀, z₂⟫ = b j₀ := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb, hzj₀]
    have h1_j₀ : ⟪a j₀, z₁⟫ = b j₀ := by
      by_contra hne
      have hlt : ⟪a j₀, z₁⟫ < b j₀ := lt_of_le_of_ne (hz₁ j₀) hne
      have hm1 : p * ⟪a j₀, z₁⟫ < p * b j₀ := mul_lt_mul_of_pos_left hlt hp
      have hm2 : q * ⟪a j₀, z₂⟫ ≤ q * b j₀ := mul_le_mul_of_nonneg_left (hz₂ j₀) hq.le
      have hm3 : p * b j₀ + q * b j₀ = b j₀ := by rw [← add_mul, hpq, one_mul]
      linarith
    have h2_j₀ : ⟪a j₀, z₂⟫ = b j₀ := by
      by_contra hne
      have hlt : ⟪a j₀, z₂⟫ < b j₀ := lt_of_le_of_ne (hz₂ j₀) hne
      have hm1 : p * ⟪a j₀, z₁⟫ ≤ p * b j₀ := mul_le_mul_of_nonneg_left (hz₁ j₀) hp.le
      have hm2 : q * ⟪a j₀, z₂⟫ < q * b j₀ := mul_lt_mul_of_pos_left hlt hq
      have hm3 : p * b j₀ + q * b j₀ = b j₀ := by rw [← add_mul, hpq, one_mul]
      linarith
    have hz₁'_j₀ : ⟪a j₀, z₁'⟫ = b j₀ := by
      dsimp [z₁']
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hzj₀, h1_j₀]
      ring
    have hz₂'_j₀ : ⟪a j₀, z₂'⟫ = b j₀ := by
      dsimp [z₂']
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hzj₀, h2_j₀]
      ring
    have hz₁'_i₀ : ⟪a i₀, z₁'⟫ < b i₀ := by
      dsimp [z₁']
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      linarith [hz₁ i₀]
    have hz₂'_i₀ : ⟪a i₀, z₂'⟫ < b i₀ := by
      dsimp [z₂']
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      linarith [hz₂ i₀]
    obtain ⟨hden1, hw1_P', hlift1⟩ := hPhi_in_P' z₁' hz₁'_P hz₁'_j₀ hz₁'_i₀
    obtain ⟨hden2, hw2_P', hlift2⟩ := hPhi_in_P' z₂' hz₂'_P hz₂'_j₀ hz₂'_i₀
    have hcomb' : p • z₁' + q • z₂' = liftZ w := by
      dsimp [z₁', z₂']
      calc p • ((1 / 2 : ℝ) • liftZ w + (1 / 2 : ℝ) • z₁) +
              q • ((1 / 2 : ℝ) • liftZ w + (1 / 2 : ℝ) • z₂)
          = ((p + q) / 2) • liftZ w + (1 / 2 : ℝ) • (p • z₁ + q • z₂) := by module
        _ = ((1 : ℝ) / 2) • liftZ w + (1 / 2 : ℝ) • liftZ w := by rw [hpq, hcomb]
        _ = liftZ w := by module
    let u₁ := toU z₁' hz₁'_j₀
    let u₂ := toU z₂' hz₂'_j₀
    have hu_comb : p • u₁ + q • u₂ = Psi w := by
      apply L.injective
      ext1
      have h1 : (L (p • u₁ + q • u₂)).1 = p • (z₁' - c) + q • (z₂' - c) := by
        rw [map_add, map_smul, map_smul]
        change p • (L u₁).1 + q • (L u₂).1 = p • (z₁' - c) + q • (z₂' - c)
        dsimp [u₁, u₂]
        rw [htoU_sub z₁' hz₁'_j₀, htoU_sub z₂' hz₂'_j₀]
      have h2 : p • (z₁' - c) + q • (z₂' - c) = liftZ w - c := by
        calc p • (z₁' - c) + q • (z₂' - c)
            = (p • z₁' + q • z₂') - (p + q) • c := by module
          _ = liftZ w - c := by rw [hcomb', hpq, one_smul]
      have h3 : liftZ w - c = (L (Psi w)).1 := by dsimp [liftZ]; module
      rw [h1, h2, h3]
    let τ₁ : ℝ := btilde i₀ - ⟪atilde i₀, u₁⟫
    let τ₂ : ℝ := btilde i₀ - ⟪atilde i₀, u₂⟫
    have hτ₁_pos : 0 < τ₁ := hden1
    have hτ₂_pos : 0 < τ₂ := hden2
    have hτ_sum : p * τ₁ + q * τ₂ = btilde i₀ - ⟪atilde i₀, Psi w⟫ := by
      dsimp [τ₁, τ₂]
      have hinner : ⟪atilde i₀, Psi w⟫ = p * ⟪atilde i₀, u₁⟫ + q * ⟪atilde i₀, u₂⟫ := by
        rw [← hu_comb, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [hinner]
      calc p * (btilde i₀ - ⟪atilde i₀, u₁⟫) + q * (btilde i₀ - ⟪atilde i₀, u₂⟫)
          = (p + q) * btilde i₀ - (p * ⟪atilde i₀, u₁⟫ + q * ⟪atilde i₀, u₂⟫) := by ring
        _ = btilde i₀ - (p * ⟪atilde i₀, u₁⟫ + q * ⟪atilde i₀, u₂⟫) := by rw [hpq, one_mul]
    have hτ_pos : 0 < p * τ₁ + q * τ₂ := add_pos (mul_pos hp hτ₁_pos) (mul_pos hq hτ₂_pos)
    have hw_open : w ∈ openSegment ℝ (Phi u₁) (Phi u₂) := by
      refine ⟨(p * τ₁) / (p * τ₁ + q * τ₂), (q * τ₂) / (p * τ₁ + q * τ₂),
        div_pos (mul_pos hp hτ₁_pos) hτ_pos,
        div_pos (mul_pos hq hτ₂_pos) hτ_pos, by rw [← add_div, div_self (ne_of_gt hτ_pos)], ?_⟩
      dsimp [Phi]
      change ((p * τ₁) / (p * τ₁ + q * τ₂)) • ((1 / τ₁) • u₁) +
          ((q * τ₂) / (p * τ₁ + q * τ₂)) • ((1 / τ₂) • u₂) = w
      rw [smul_smul, smul_smul]
      have hc1 : ((p * τ₁) / (p * τ₁ + q * τ₂)) * (1 / τ₁) =
          p / (p * τ₁ + q * τ₂) := by field_simp [ne_of_gt hτ₁_pos, ne_of_gt hτ_pos]
      have hc2 : ((q * τ₂) / (p * τ₁ + q * τ₂)) * (1 / τ₂) =
          q / (p * τ₁ + q * τ₂) := by field_simp [ne_of_gt hτ₂_pos, ne_of_gt hτ_pos]
      rw [hc1, hc2, div_eq_inv_mul p _, div_eq_inv_mul q _, ← smul_smul, ← smul_smul,
        ← smul_add, hu_comb, hτ_sum]
      have hpw := (hPhi_Psi w (hdenom_pos w hw_ext.1)).2
      dsimp [Phi] at hpw
      simpa [one_div] using hpw
    have hw1_eq : Phi u₁ = w := hw_ext.2 hw1_P' hw2_P' hw_open
    have hz₁'_eq : z₁' = liftZ w := by
      rw [← hlift1, hw1_eq]
    have hhalf : (1 / 2 : ℝ) • (z₁ - liftZ w) = 0 := by
      calc (1 / 2 : ℝ) • (z₁ - liftZ w)
          = z₁' - liftZ w := by dsimp [z₁']; module
        _ = 0 := by rw [hz₁'_eq, sub_self]
    rcases smul_eq_zero.mp hhalf with hnum | hsub0
    · norm_num at hnum
    · exact sub_eq_zero.mp hsub0
  have hPhi_ext : ∀ (z : EuclideanSpace ℝ (Fin d))
      (hz_ext : z ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
      (hzj₀ : ⟪a j₀, z⟫ = b j₀) (hzi₀ : ⟪a i₀, z⟫ < b i₀),
      Phi (toU z hzj₀) ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b') := by
    intro z hz_ext hzj₀ hzi₀
    obtain ⟨_, hw_P', hlift_z⟩ := hPhi_in_P' z hz_ext.1 hzj₀ hzi₀
    refine ⟨hw_P', ?_⟩
    rintro w₁ hw₁ w₂ hw₂ ⟨p, q, hp, hq, hpq, hcomb⟩
    let lam₁ : ℝ := 1 + ⟪atilde i₀, w₁⟫
    let lam₂ : ℝ := 1 + ⟪atilde i₀, w₂⟫
    have hlam₁_pos : 0 < lam₁ := hdenom_pos w₁ hw₁
    have hlam₂_pos : 0 < lam₂ := hdenom_pos w₂ hw₂
    have hlam_sum : p * lam₁ + q * lam₂ = 1 + ⟪atilde i₀, Phi (toU z hzj₀)⟫ := by
      dsimp [lam₁, lam₂]
      rw [← hcomb, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      calc p * (1 + ⟪atilde i₀, w₁⟫) + q * (1 + ⟪atilde i₀, w₂⟫)
          = (p + q) + (p * ⟪atilde i₀, w₁⟫ + q * ⟪atilde i₀, w₂⟫) := by ring
        _ = 1 + (p * ⟪atilde i₀, w₁⟫ + q * ⟪atilde i₀, w₂⟫) := by rw [hpq]
    have hlam_pos : 0 < p * lam₁ + q * lam₂ := add_pos (mul_pos hp hlam₁_pos) (mul_pos hq hlam₂_pos)
    have hPsi_comb :
        ((p * lam₁) / (p * lam₁ + q * lam₂)) • Psi w₁ +
          ((q * lam₂) / (p * lam₁ + q * lam₂)) • Psi w₂ = Psi (Phi (toU z hzj₀)) := by
      dsimp [Psi]
      change ((p * lam₁) / (p * lam₁ + q * lam₂)) • ((btilde i₀ / lam₁) • w₁) +
          ((q * lam₂) / (p * lam₁ + q * lam₂)) • ((btilde i₀ / lam₂) • w₂) =
          (btilde i₀ / (1 + ⟪atilde i₀, Phi (toU z hzj₀)⟫)) • Phi (toU z hzj₀)
      rw [smul_smul, smul_smul]
      have hc1 : ((p * lam₁) / (p * lam₁ + q * lam₂)) * (btilde i₀ / lam₁) =
          (btilde i₀ / (p * lam₁ + q * lam₂)) * p := by
        field_simp [ne_of_gt hlam₁_pos, ne_of_gt hlam_pos]
      have hc2 : ((q * lam₂) / (p * lam₁ + q * lam₂)) * (btilde i₀ / lam₂) =
          (btilde i₀ / (p * lam₁ + q * lam₂)) * q := by
        field_simp [ne_of_gt hlam₂_pos, ne_of_gt hlam_pos]
      rw [hc1, hc2, ← smul_smul, ← smul_smul, ← smul_add, hcomb, hlam_sum]
    have hz_open : z ∈ openSegment ℝ (liftZ w₁) (liftZ w₂) := by
      refine ⟨(p * lam₁) / (p * lam₁ + q * lam₂), (q * lam₂) / (p * lam₁ + q * lam₂),
        div_pos (mul_pos hp hlam₁_pos) hlam_pos,
        div_pos (mul_pos hq hlam₂_pos) hlam_pos, by rw [← add_div, div_self (ne_of_gt hlam_pos)], ?_⟩
      let α : ℝ := (p * lam₁) / (p * lam₁ + q * lam₂)
      let β : ℝ := (q * lam₂) / (p * lam₁ + q * lam₂)
      have hab : α + β = 1 := by dsimp [α, β]; rw [← add_div, div_self (ne_of_gt hlam_pos)]
      change α • (c + (L (Psi w₁)).1) + β • (c + (L (Psi w₂)).1) = z
      have hL_add : α • (L (Psi w₁)).1 + β • (L (Psi w₂)).1 =
          (L (Psi (Phi (toU z hzj₀)))).1 := by
        have hm : (L (α • Psi w₁ + β • Psi w₂)).1 =
            α • (L (Psi w₁)).1 + β • (L (Psi w₂)).1 := by simp
        rw [← hm, hPsi_comb]
      calc α • (c + (L (Psi w₁)).1) + β • (c + (L (Psi w₂)).1)
          = (α + β) • c + (α • (L (Psi w₁)).1 + β • (L (Psi w₂)).1) := by module
        _ = c + (L (Psi (Phi (toU z hzj₀)))).1 := by rw [hab, one_smul, hL_add]
        _ = z := hlift_z
    have hz1_eq : liftZ w₁ = z :=
      hz_ext.2 (hliftZ_props w₁ hw₁).1 (hliftZ_props w₂ hw₂).1 hz_open
    have hPsi_eq : Psi w₁ = Psi (Phi (toU z hzj₀)) := by
      apply L.injective
      ext1
      have : c + (L (Psi w₁)).1 = c + (L (Psi (Phi (toU z hzj₀)))).1 := by
        change liftZ w₁ = liftZ (Phi (toU z hzj₀))
        rw [hz1_eq, hlift_z]
      exact add_left_cancel this
    have hw1_phi := (hPhi_Psi w₁ hlam₁_pos).2
    have hw_phi := (hPhi_Psi (Phi (toU z hzj₀)) (hdenom_pos _ hw_P')).2
    rw [← hw1_phi, hPsi_eq, hw_phi]
  have hx'_j₀ : ⟪a j₀, x'⟫ = b j₀ := mem_tightFinset.mp hj₀_Tx'
  have hx'_i₀ : ⟪a i₀, x'⟫ < b i₀ :=
    lt_of_le_of_ne (hx'_ext.1 i₀) (by rwa [mem_tightFinset] at hi₀_nx')
  have hy_j₀ : ⟪a j₀, y⟫ = b j₀ := mem_tightFinset.mp hj₀_Ty
  have hi₀_ny : i₀ ∉ tightFinset a b y := Finset.disjoint_left.mp hdisj hi₀
  have hy_i₀ : ⟪a i₀, y⟫ < b i₀ :=
    lt_of_le_of_ne (hy_ext.1 i₀) (by rwa [mem_tightFinset] at hi₀_ny)
  let wx : EuclideanSpace ℝ (Fin d') := Phi (toU x' hx'_j₀)
  let wy : EuclideanSpace ℝ (Fin d') := Phi (toU y hy_j₀)
  have hwx_ext : wx ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b') :=
    hPhi_ext x' hx'_ext hx'_j₀ hx'_i₀
  have hwy_ext : wy ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b') :=
    hPhi_ext y hy_ext hy_j₀ hy_i₀
  have hlift_wx : liftZ wx = x' := (hPhi_in_P' x' hx'_ext.1 hx'_j₀ hx'_i₀).2.2
  have hlift_wy : liftZ wy = y := (hPhi_in_P' y hy_ext.1 hy_j₀ hy_i₀).2.2
  exact lift_facet_path hk₂ hk₄ rfl hd_eq a b hS x x' y hx'_face hx'_dim hdisj i₀ j₀ hTx'_eq
    S_idx hmem_S_idx eS a' b' hb'_pos liftZ hliftZ_props hliftZ_ext wx wy hwx_ext hwy_ext
    hlift_wx hlift_wy
