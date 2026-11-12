-- Prove2me | solution 1 for KleeWalkup67.FiveStep.proposition_3_4_a
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:57:31.980698+00:00
-- url     : https://prove2.me/submissions/3dafb399-6ed8-4c5d-ba70-e467fe44c760

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra
import Theorems.Thm_Hirsch_vertex_tight_rows_span
import Theorems.Thm_Hirsch_graph_connected_general

namespace Aux_KW67_proposition_3_4_a

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep

noncomputable def tightFinset {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ⟪a i, z⟫ = b i)

lemma mem_tightFinset {d n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    {b : Fin n → ℝ} {z : EuclideanSpace ℝ (Fin d)} {i : Fin n} :
    i ∈ tightFinset a b z ↔ ⟪a i, z⟫ = b i := by
  classical
  simp [tightFinset]

lemma coe_tightFinset {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (tightFinset a b z : Set (Fin n)) = TightSet a b z := by
  ext i
  simp [mem_tightFinset, TightSet]

lemma card_tightFinset_eq_ncard {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (tightFinset a b z).card = (TightSet a b z).ncard := by
  rw [← coe_tightFinset, Set.ncard_coe_finset]

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

lemma hpoly_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hirsch.Hpoly a b) := by
  intro x hx y hy s t hs ht hst i
  have h1 := hx i
  have h2 := hy i
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have e1 : s * ⟪a i, x⟫ ≤ s * b i := mul_le_mul_of_nonneg_left h1 hs
  have e2 : t * ⟪a i, y⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht
  have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

lemma step_into_hpoly {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v u : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Hirsch.Hpoly a b)
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

def zeroOnSubmodule {n : ℕ} (T J : Finset (Fin n)) : Submodule ℝ (T → ℝ) where
  carrier := {f | ∀ i : T, i.1 ∈ J → f i = 0}
  add_mem' ha hb i hi := by simp [ha i hi, hb i hi]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf i hi := by simp [hf i hi]

noncomputable def zeroOnEquivSdiff {n : ℕ} (T J : Finset (Fin n)) :
    zeroOnSubmodule T J ≃ₗ[ℝ] ((T \ J : Finset (Fin n)) → ℝ) := by
  classical
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
    Module.finrank ℝ ((zeroOnSubmodule (tightFinset a b v) J).comap
      (tightEquiv a b hv hcard).toLinearMap) = d - J.card := by
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
  change Module.finrank ℝ (M.comap E.toLinearMap) = d - J.card
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

lemma exists_crossing_step (f : ℕ → ℕ) (t : ℕ) :
    ∀ L : ℕ, t + 1 ≤ f 0 → f L ≤ t → (∀ j < L, f j ≤ f (j + 1) + 1) →
      ∃ j < L, f j = t + 1 ∧ f (j + 1) = t := by
  intro L
  induction L with
  | zero =>
      intro h0 hL _
      omega
  | succ m ih =>
      intro h0 hm1 hstep
      rcases le_or_gt (f m) t with hle | hgt
      · obtain ⟨j, hj, h1, h2⟩ := ih h0 hle (fun j hj' => hstep j (by omega))
        exact ⟨j, by omega, h1, h2⟩
      · have hsm := hstep m (Nat.lt_succ_self m)
        exact ⟨m, Nat.lt_succ_self m, by omega, by omega⟩

end Aux_KW67_proposition_3_4_a

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep Aux_KW67_proposition_3_4_a

theorem solution {d : ℕ}
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (k₁ k₃ : ℕ) (hk₁ : 0 < k₁) (hk₃ : 0 < k₃) (hsum : k₁ + 1 + k₃ = d) :
    IsFacialPath a b [k₁, 1, k₃] x y := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨_, hx_ext, hy_ext, hx_ncard, hy_ncard, hdisj_set⟩ := hD
  let Tx := tightFinset a b x
  let Ty := tightFinset a b y
  have hTx_card : Tx.card = d := by rw [card_tightFinset_eq_ncard, hx_ncard]
  have hTy_card : Ty.card = d := by rw [card_tightFinset_eq_ncard, hy_ncard]
  have hdisj : Disjoint Tx Ty := by
    rw [Finset.disjoint_left]
    intro i hix hiy
    exact Set.disjoint_left.mp hdisj_set (mem_tightFinset.mp hix) (mem_tightFinset.mp hiy)
  have huniv : Tx ∪ Ty = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hTx_card, hTy_card]
    simp
    omega
  obtain ⟨L, w, hw0, hwL, hwstep⟩ :=
    Hirsch.graph_connected_general d (2 * d) a b x y hx_ext hy_ext
  have hw_ext : ∀ j ≤ L, w j ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) := by
    intro j
    induction j with
    | zero => intro _; rwa [hw0]
    | succ j ih =>
        intro hjL
        have hprev := ih (by omega)
        rcases hwstep j (by omega) with heq | hadj
        · rwa [← heq]
        · exact adj_right_mem_extremePoints hadj
  let f : ℕ → ℕ := fun j => (tightFinset a b (w j) ∩ Tx).card
  have hf0 : k₃ + 1 ≤ f 0 := by
    dsimp [f]
    rw [hw0]
    change k₃ + 1 ≤ (Tx ∩ Tx).card
    rw [Finset.inter_self, hTx_card]
    omega
  have hfL : f L ≤ k₃ := by
    dsimp [f]
    rw [hwL]
    change (Ty ∩ Tx).card ≤ k₃
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm]
    simp
  have hf_step : ∀ j < L, f j ≤ f (j + 1) + 1 := by
    intro j hj
    rcases hwstep j hj with heq | hadj
    · dsimp [f]
      rw [← heq]
      omega
    · have hu := hw_ext j (by omega)
      have hv := hw_ext (j + 1) (by omega)
      have hcard_u : (TightSet a b (w j)).ncard = d := hS.2 (w j) hu
      have hinter := adj_inter_tightFinset_card hd1 a b hu hv hcard_u hadj
      let Tu := tightFinset a b (w j)
      let Tv := tightFinset a b (w (j + 1))
      change (Tu ∩ Tv).card = d - 1 at hinter
      have hTu_card : Tu.card = d := by rw [card_tightFinset_eq_ncard, hcard_u]
      have hsdiff_card : (Tu \ Tv).card = 1 := by
        have h := Finset.card_sdiff_add_card_inter Tu Tv
        change (Tu \ Tv).card + (Tu ∩ Tv).card = Tu.card at h
        omega
      have hsplit : Tu ∩ Tx ⊆ (Tv ∩ Tx) ∪ (Tu \ Tv) := by
        intro i hi
        rcases Finset.mem_inter.mp hi with ⟨hiu, hix⟩
        by_cases hiv : i ∈ Tv
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hiv, hix⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hiu, hiv⟩)
      have hcard_le := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
      dsimp [f]
      change (Tu ∩ Tx).card ≤ (Tv ∩ Tx).card + 1
      omega
  obtain ⟨j, hjL, hfj, hfj1⟩ := exists_crossing_step f k₃ L hf0 hfL hf_step
  let u := w j
  let v := w (j + 1)
  have hu_ext : u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) := hw_ext j (by omega)
  have hv_ext : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) := hw_ext (j + 1) (by omega)
  have hadj_uv : Hirsch.Adj (Hirsch.Hpoly a b) u v := by
    rcases hwstep j hjL with heq | hadj
    · exfalso
      have : f j = f (j + 1) := by dsimp [f]; rw [heq]
      omega
    · exact hadj
  have hcard_u : (TightSet a b u).ncard = d := hS.2 u hu_ext
  have hcard_v : (TightSet a b v).ncard = d := hS.2 v hv_ext
  have hTv_card : (tightFinset a b v).card = d := by rw [card_tightFinset_eq_ncard, hcard_v]
  let I₀ := tightFinset a b u ∩ Tx
  let I₁ := tightFinset a b u ∩ tightFinset a b v
  let I₂ := tightFinset a b v ∩ Ty
  have hI₀_card : I₀.card = k₃ + 1 := hfj
  have hI₁_card : I₁.card = d - 1 := adj_inter_tightFinset_card hd1 a b hu_ext hv_ext hcard_u hadj_uv
  have hI₂_card : I₂.card = k₁ + 1 := by
    have hpart : tightFinset a b v = (tightFinset a b v ∩ Tx) ∪ (tightFinset a b v ∩ Ty) := by
      rw [← Finset.inter_union_distrib_left, huniv, Finset.inter_univ]
    have hdisj_v : Disjoint (tightFinset a b v ∩ Tx) (tightFinset a b v ∩ Ty) :=
      hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have hsum_v : (tightFinset a b v).card =
        (tightFinset a b v ∩ Tx).card + (tightFinset a b v ∩ Ty).card := by
      conv_lhs => rw [hpart]
      exact Finset.card_union_of_disjoint hdisj_v
    have hvx : (tightFinset a b v ∩ Tx).card = k₃ := hfj1
    dsimp [I₂]
    omega
  have hx_I₀ : x ∈ faceOf a b I₀ :=
    ⟨hx_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_right hi)⟩
  have hu_I₀ : u ∈ faceOf a b I₀ :=
    ⟨hu_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_left hi)⟩
  have hu_I₁ : u ∈ faceOf a b I₁ :=
    ⟨hu_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_left hi)⟩
  have hv_I₁ : v ∈ faceOf a b I₁ :=
    ⟨hv_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_right hi)⟩
  have hv_I₂ : v ∈ faceOf a b I₂ :=
    ⟨hv_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_left hi)⟩
  have hy_I₂ : y ∈ faceOf a b I₂ :=
    ⟨hy_ext.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_right hi)⟩
  have hdim₀ : dim (faceOf a b I₀) = k₁ := by
    have hd := (dim_faceOf_at_simple_vertex a b hu_ext hcard_u I₀ hu_I₀).2
    omega
  have hdim₁ : dim (faceOf a b I₁) = 1 := by
    have hd := (dim_faceOf_at_simple_vertex a b hu_ext hcard_u I₁ hu_I₁).2
    omega
  have hdim₂ : dim (faceOf a b I₂) = k₃ := by
    have hd := (dim_faceOf_at_simple_vertex a b hv_ext hcard_v I₂ hv_I₂).2
    omega
  let K : Fin [k₁, 1, k₃].length → Set (EuclideanSpace ℝ (Fin d)) :=
    ![faceOf a b I₀, faceOf a b I₁, faceOf a b I₂]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro idx
    fin_cases idx
    · exact ⟨⟨⟨u, hu_I₀⟩, I₀, rfl⟩, hdim₀⟩
    · exact ⟨⟨⟨u, hu_I₁⟩, I₁, rfl⟩, hdim₁⟩
    · exact ⟨⟨⟨v, hv_I₂⟩, I₂, rfl⟩, hdim₂⟩
  · intro idx₁ idx₂ hnext
    fin_cases idx₁ <;> fin_cases idx₂ <;> simp at hnext ⊢
    · exact ⟨u, hu_I₀, hu_I₁⟩
    · exact ⟨v, hv_I₁, hv_I₂⟩
  · have hlen3 : 0 < [k₁, 1, k₃].length := by simp
    exact ⟨hlen3, by simpa [K] using hx_I₀, by simpa [K] using hy_I₂⟩
