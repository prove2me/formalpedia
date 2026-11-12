-- Prove2me | solution 1 for KleeWalkup67.FiveStep.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:57:33.015214+00:00
-- url     : https://prove2.me/submissions/00d4a032-2fa1-433b-bc61-dcf5ca093bda

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra
import Theorems.Thm_Hirsch_vertex_tight_rows_span

namespace Aux_KW67_proposition_4_1

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

lemma faceOf_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (I : Finset (Fin n)) : Convex ℝ (faceOf a b I) := by
  intro x hx y hy s t hs ht hst
  refine ⟨hpoly_convex a b hx.1 hy.1 hs ht hst, ?_⟩
  intro i hi
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hx.2 i hi, hy.2 i hi,
    ← add_mul, hst, one_mul]

lemma isExtreme_faceOf {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (I : Finset (Fin n)) : IsExtreme ℝ (Hirsch.Hpoly a b) (faceOf a b I) := by
  refine ⟨fun _ hz => hz.1, ?_⟩
  rintro x₁ hx₁ x₂ hx₂ z hz ⟨p, q, hp, hq, hpq, hcomb⟩
  refine ⟨hx₁, ?_⟩
  intro i hi
  have hzi : ⟪a i, z⟫ = b i := hz.2 i hi
  have h1 : ⟪a i, x₁⟫ ≤ b i := hx₁ i
  have h2 : ⟪a i, x₂⟫ ≤ b i := hx₂ i
  have hlin : p * ⟪a i, x₁⟫ + q * ⟪a i, x₂⟫ = b i := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb, hzi]
  by_contra hne1
  have hlt1 : ⟪a i, x₁⟫ < b i := lt_of_le_of_ne h1 hne1
  have hm1 : p * ⟪a i, x₁⟫ < p * b i := mul_lt_mul_of_pos_left hlt1 hp
  have hm2 : q * ⟪a i, x₂⟫ ≤ q * b i := mul_le_mul_of_nonneg_left h2 hq.le
  have hm3 : p * b i + q * b i = b i := by rw [← add_mul, hpq, one_mul]
  linarith

lemma isExtreme_of_isFace {d n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsFace a b K) :
    IsExtreme ℝ (Hirsch.Hpoly a b) K := by
  obtain ⟨_, I, rfl⟩ := hK
  exact isExtreme_faceOf a b I

lemma adj_symm {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {u v : E}
    (h : Hirsch.Adj P u v) : Hirsch.Adj P v u :=
  ⟨h.1.symm, segment_symm ℝ u v ▸ h.2⟩

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

lemma reach_trans {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {L₁ L₂ : ℕ} {u x v : E}
    (h₁ : Hirsch.Reach P L₁ u x) (h₂ : Hirsch.Reach P L₂ x v) :
    Hirsch.Reach P (L₁ + L₂) u v := by
  classical
  obtain ⟨w₁, a1, b1, s1⟩ := h₁
  obtain ⟨w₂, a2, b2, s2⟩ := h₂
  refine ⟨fun j => if j ≤ L₁ then w₁ j else w₂ (j - L₁), by simpa using a1, ?_, ?_⟩
  · dsimp only
    by_cases hc : L₁ + L₂ ≤ L₁
    · have hz : L₂ = 0 := by omega
      subst hz
      rw [if_pos hc]
      simpa using b1.trans (by rw [← a2, ← b2])
    · rw [if_neg hc]
      have : L₁ + L₂ - L₁ = L₂ := by omega
      rw [this]
      exact b2
  · intro j hj
    dsimp only
    by_cases hc : j ≤ L₁
    · by_cases hc1 : j + 1 ≤ L₁
      · rw [if_pos hc, if_pos hc1]
        exact s1 j (by omega)
      · have hjL : j = L₁ := by omega
        subst hjL
        rw [if_pos hc, if_neg hc1]
        have : j + 1 - j = 1 := by omega
        rw [this, b1, ← a2]
        exact s2 0 (by omega)
    · rw [if_neg hc, if_neg (by omega : ¬(j + 1 ≤ L₁))]
      have : j + 1 - L₁ = (j - L₁) + 1 := by omega
      rw [this]
      exact s2 _ (by omega)

lemma reach_of_isExtreme {E : Type*} [AddCommGroup E] [Module ℝ E] {P Q : Set E}
    (hPQ : IsExtreme ℝ P Q) {L : ℕ} {u v : E} (h : Hirsch.Reach Q L u v) :
    Hirsch.Reach P L u v := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨w, h0, hL, ?_⟩
  intro i hi
  rcases hstep i hi with heq | hadj
  · exact Or.inl heq
  · exact Or.inr ⟨hadj.1, hPQ.trans hadj.2⟩

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

lemma exists_strict_point_faceOf {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard : (TightSet a b v).ncard = d)
    (J : Finset (Fin n)) (hvJ : v ∈ faceOf a b J) :
    ∃ z₀ ∈ faceOf a b J, tightFinset a b z₀ = J := by
  classical
  have hJT : J ⊆ tightFinset a b v := fun i hi => mem_tightFinset.mpr (hvJ.2 i hi)
  let E := tightEquiv a b hv hcard
  let g₀ : tightFinset a b v → ℝ := fun k => if k.1 ∈ J then 0 else -1
  let u₀ := E.symm g₀
  have hu₀_le : ∀ i ∈ tightFinset a b v, ⟪a i, u₀⟫ ≤ 0 := by
    intro i hi
    have heq : ⟪a i, u₀⟫ = g₀ ⟨i, hi⟩ := by
      change E u₀ ⟨i, hi⟩ = g₀ ⟨i, hi⟩
      simp [u₀]
    rw [heq]
    dsimp [g₀]
    split_ifs <;> linarith
  obtain ⟨ε₀, hε₀_pos, hε₀⟩ := step_into_hpoly a b hv.1 hu₀_le
  let ε := ε₀ / 2
  have hε_pos : 0 < ε := half_pos hε₀_pos
  have hε_le : ε ≤ ε₀ := half_le_self hε₀_pos.le
  let z₀ := v + ε • u₀
  have hz₀_mem : z₀ ∈ faceOf a b J := by
    refine ⟨hε₀ ε hε_pos hε_le, ?_⟩
    intro i hi
    have hiT : i ∈ tightFinset a b v := hJT hi
    have heq : ⟪a i, u₀⟫ = g₀ ⟨i, hiT⟩ := by
      change E u₀ ⟨i, hiT⟩ = g₀ ⟨i, hiT⟩
      simp [u₀]
    dsimp [z₀]
    rw [inner_add_right, real_inner_smul_right, hvJ.2 i hi, heq]
    simp [g₀, hi]
  refine ⟨z₀, hz₀_mem, ?_⟩
  ext i
  rw [mem_tightFinset]
  constructor
  · intro hiz
    by_cases hiT : i ∈ tightFinset a b v
    · by_contra hiJ
      have heq : ⟪a i, u₀⟫ = g₀ ⟨i, hiT⟩ := by
        change E u₀ ⟨i, hiT⟩ = g₀ ⟨i, hiT⟩
        simp [u₀]
      have hvi : ⟪a i, v⟫ = b i := mem_tightFinset.mp hiT
      dsimp [z₀] at hiz
      rw [inner_add_right, real_inner_smul_right, hvi, heq] at hiz
      dsimp [g₀] at hiz
      rw [if_neg hiJ] at hiz
      linarith
    · exfalso
      have hvi_lt : ⟪a i, v⟫ < b i :=
        lt_of_le_of_ne (hv.1 i) (by rwa [mem_tightFinset] at hiT)
      have hz1 : v + ε₀ • u₀ ∈ Hirsch.Hpoly a b := hε₀ ε₀ hε₀_pos le_rfl
      have hz1_i : ⟪a i, v + ε₀ • u₀⟫ ≤ b i := hz1 i
      have hmid : z₀ = (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • (v + ε₀ • u₀) := by
        dsimp [z₀, ε]
        module
      rw [hmid, inner_add_right, real_inner_smul_right, real_inner_smul_right] at hiz
      linarith
  · intro hiJ
    exact hz₀_mem.2 i hiJ

lemma faceOf_subset_imp_subset {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard : (TightSet a b v).ncard = d)
    {J₁ J₂ : Finset (Fin n)} (hv₁ : v ∈ faceOf a b J₁)
    (hsub : faceOf a b J₁ ⊆ faceOf a b J₂) :
    J₂ ⊆ J₁ := by
  obtain ⟨z₀, hz₀₁, hz₀T⟩ := exists_strict_point_faceOf a b hv hcard J₁ hv₁
  have hz₀₂ := hsub hz₀₁
  intro i hi
  rw [← hz₀T, mem_tightFinset]
  exact hz₀₂.2 i hi

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
            rcases lt_trichotomy 0 ⟪a j₀, e₀⟫ with h1 | h1 | h1
            · exact absurd h1 hpos
            · exact absurd h1.symm hj₀
            · linarith
        let S : Finset (Fin n) := Finset.univ.filter (fun j => 0 < ⟪a j, e⟫)
        have hj₀S : j₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀_pos⟩
        obtain ⟨jstar, hjstarS, hjstar_min⟩ :=
          Finset.exists_min_image S (fun j => (b j - ⟪a j, z⟫) / ⟪a j, e⟫) ⟨j₀, hj₀S⟩
        have hjstar_e : 0 < ⟪a jstar, e⟫ := (Finset.mem_filter.mp hjstarS).2
        have hjstar_notT : jstar ∉ tightFinset a b z := fun hm => by
          linarith [heT jstar hm]
        have hjstar_lt : ⟪a jstar, z⟫ < b jstar :=
          lt_of_le_of_ne (hz.1 jstar) (by rwa [mem_tightFinset] at hjstar_notT)
        let tstar : ℝ := (b jstar - ⟪a jstar, z⟫) / ⟪a jstar, e⟫
        have htstar_pos : 0 < tstar := div_pos (sub_pos.mpr hjstar_lt) hjstar_e
        let z' := z + tstar • e
        have hz' : z' ∈ faceOf a b I := by
          refine ⟨?_, ?_⟩
          · intro j
            dsimp [z']
            rw [inner_add_right, real_inner_smul_right]
            rcases lt_or_ge 0 ⟪a j, e⟫ with hjp | hjn
            · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjp⟩
              have hle : tstar ≤ (b j - ⟪a j, z⟫) / ⟪a j, e⟫ := hjstar_min j hjS
              have hmul : tstar * ⟪a j, e⟫ ≤ b j - ⟪a j, z⟫ := (le_div_iff₀ hjp).mp hle
              linarith
            · have hmul : tstar * ⟪a j, e⟫ ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos htstar_pos.le hjn
              linarith [hz.1 j]
          · intro i hi
            have hiT : i ∈ tightFinset a b z := mem_tightFinset.mpr (hz.2 i hi)
            dsimp [z']
            rw [inner_add_right, real_inner_smul_right, hz.2 i hi, heT i hiT, mul_zero, add_zero]
        have hsub : tightFinset a b z ⊆ tightFinset a b z' := by
          intro j hj
          rw [mem_tightFinset] at hj ⊢
          dsimp [z']
          rw [inner_add_right, real_inner_smul_right, hj, heT j (mem_tightFinset.mpr hj),
            mul_zero, add_zero]
        have hjstar_in : jstar ∈ tightFinset a b z' := by
          rw [mem_tightFinset]
          dsimp [z', tstar]
          rw [inner_add_right, real_inner_smul_right, div_mul_cancel₀ _ (ne_of_gt hjstar_e)]
          ring
        have hssub : tightFinset a b z ⊂ tightFinset a b z' :=
          Finset.ssubset_iff_of_subset hsub |>.mpr ⟨jstar, hjstar_in, hjstar_notT⟩
        have hlt_card : (tightFinset a b z).card < (tightFinset a b z').card :=
          Finset.card_lt_card hssub
        have hcard_le : (tightFinset a b z').card ≤ n := by
          simpa using Finset.card_le_univ (tightFinset a b z')
        exact ih z' hz' (by omega)

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

lemma reach_one_of_inter_card_ge {d n : ℕ} (hd : 1 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {p₁ p₂ : EuclideanSpace ℝ (Fin d)}
    (hp₁ : p₁ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hp₂ : p₂ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard₁ : (TightSet a b p₁).ncard = d)
    (hinter : d - 1 ≤ (tightFinset a b p₁ ∩ tightFinset a b p₂).card) :
    Hirsch.Reach (Hirsch.Hpoly a b) 1 p₁ p₂ := by
  classical
  by_cases hp_eq : p₁ = p₂
  · subst hp_eq
    exact ⟨fun _ => p₁, rfl, rfl, fun i _ => Or.inl rfl⟩
  have hTp₁ : (tightFinset a b p₁).card = d := by
    rw [card_tightFinset_eq_ncard, hcard₁]
  have hle : (tightFinset a b p₁ ∩ tightFinset a b p₂).card ≤ d - 1 := by
    by_contra hgt
    push Not at hgt
    have hge : (tightFinset a b p₁).card ≤ (tightFinset a b p₁ ∩ tightFinset a b p₂).card := by
      omega
    have heq := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hge
    have hsub : tightFinset a b p₁ ⊆ tightFinset a b p₂ := by
      rw [← heq]
      exact Finset.inter_subset_right
    have hdiff0 : p₂ - p₁ = 0 := by
      refine Hirsch.vertex_tight_rows_span d n a b p₁ hp₁ (p₂ - p₁) ?_
      intro j hj
      have hj2 : ⟪a j, p₂⟫ = b j := mem_tightFinset.mp (hsub (mem_tightFinset.mpr hj))
      rw [inner_sub_right, hj2, hj, sub_self]
    exact hp_eq (sub_eq_zero.mp hdiff0).symm
  have hcard_eq : (tightFinset a b p₁ ∩ tightFinset a b p₂).card = d - 1 := by omega
  let J := tightFinset a b p₁ ∩ tightFinset a b p₂
  let E := faceOf a b J
  have hp₁E : p₁ ∈ E :=
    ⟨hp₁.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_left hi)⟩
  have hp₂E : p₂ ∈ E :=
    ⟨hp₂.1, fun i hi => mem_tightFinset.mp (Finset.inter_subset_right hi)⟩
  have hdimE : dim E = 1 := by
    have hdE := (dim_faceOf_at_simple_vertex a b hp₁ hcard₁ J hp₁E).2
    change dim (faceOf a b J) = 1
    rw [hdE]
    dsimp [J]
    omega
  have hE_eq : E = segment ℝ p₁ p₂ := by
    apply Set.Subset.antisymm
    · have hsub_span : (ℝ ∙ (p₂ - p₁)) ≤ (affineSpan ℝ E).direction := by
        rw [Submodule.span_singleton_le_iff_mem, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hp₂E hp₁E
      have hne_sub : p₂ - p₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hp_eq)
      have hfr1 : Module.finrank ℝ (ℝ ∙ (p₂ - p₁)) = 1 :=
        finrank_span_singleton_eq_one hne_sub
      have hdir_eq : (ℝ ∙ (p₂ - p₁)) = (affineSpan ℝ E).direction :=
        Submodule.eq_of_le_of_finrank_eq hsub_span (hfr1.trans hdimE.symm)
      intro z hz
      have hz_dir : z - p₁ ∈ (ℝ ∙ (p₂ - p₁)) := by
        rw [hdir_eq, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hz hp₁E
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hz_dir
      have hz_comb : z = (1 - t) • p₁ + t • p₂ := by
        have hz' : z = p₁ + (z - p₁) := by module
        rw [hz', ← ht]
        module
      have ht0 : 0 ≤ t := by
        by_contra hlt
        push Not at hlt
        have hden : 0 < 1 - t := by linarith
        have hopen : p₁ ∈ openSegment ℝ z p₂ := by
          refine ⟨1 / (1 - t), (-t) / (1 - t), div_pos one_pos hden,
            div_pos (by linarith) hden, by field_simp; ring, ?_⟩
          rw [hz_comb, smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
          have hc1 : (1 / (1 - t)) * (1 - t) = (1 : ℝ) := by field_simp
          have hc2 : (1 / (1 - t)) * t + (-t) / (1 - t) = (0 : ℝ) := by field_simp; ring
          rw [hc1, hc2, one_smul, zero_smul, add_zero]
        have hzp₁ : z = p₁ := hp₁.2 hz.1 hp₂.1 hopen
        rw [hzp₁, sub_self] at ht
        rcases smul_eq_zero.mp ht with ht_z | hsub_z
        · linarith
        · exact hne_sub hsub_z
      have ht1 : t ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have ht_pos : 0 < t := by linarith
        have hopen : p₂ ∈ openSegment ℝ p₁ z := by
          refine ⟨(t - 1) / t, 1 / t, div_pos (by linarith) ht_pos,
            div_pos one_pos ht_pos, by field_simp; ring, ?_⟩
          rw [hz_comb, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
          have hc1 : (t - 1) / t + (1 / t) * (1 - t) = (0 : ℝ) := by field_simp; ring
          have hc2 : (1 / t) * t = (1 : ℝ) := by field_simp
          rw [hc1, hc2, zero_smul, zero_add, one_smul]
        exact hp_eq (hp₂.2 hp₁.1 hz.1 hopen)
      exact ⟨1 - t, t, by linarith, ht0, by ring, hz_comb.symm⟩
    · exact (faceOf_convex a b J).segment_subset hp₁E hp₂E
  have hadj : Hirsch.Adj (Hirsch.Hpoly a b) p₁ p₂ :=
    ⟨hp_eq, hE_eq ▸ isExtreme_faceOf a b J⟩
  refine ⟨fun j => if j = 0 then p₁ else p₂, by simp, by simp, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  exact Or.inr (by simpa using hadj)

lemma ne_of_dim_segment_eq_one {d : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (hdim : dim (segment ℝ u v) = 1) : u ≠ v := by
  intro huv
  subst huv
  rw [segment_same] at hdim
  unfold dim at hdim
  rw [direction_affineSpan, vectorSpan_singleton, finrank_bot] at hdim
  omega

lemma endpoint_mem_of_segment_inter_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P Q : Set E} {u v : E} (hu : u ∈ P) (hv : v ∈ P) (hQ : IsExtreme ℝ P Q)
    (hne : (segment ℝ u v ∩ Q).Nonempty) : u ∈ Q ∨ v ∈ Q := by
  obtain ⟨z, hz_seg, hzQ⟩ := hne
  obtain ⟨p, q, hp, hq, hpq, hcomb⟩ := hz_seg
  rcases eq_or_lt_of_le hp with rfl | hp_pos
  · right
    have hq1 : q = 1 := by linarith
    subst hq1
    have hzv : v = z := by simpa using hcomb
    rwa [hzv]
  · rcases eq_or_lt_of_le hq with rfl | hq_pos
    · left
      have hp1 : p = 1 := by linarith
      subst hp1
      have hzu : u = z := by simpa using hcomb
      rwa [hzu]
    · left
      exact hQ.2 hu hv hzQ ⟨p, q, hp_pos, hq_pos, hpq, hcomb⟩

def facetAt {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (I_Q : Finset (Fin n)) (i : Fin n) : Set (EuclideanSpace ℝ (Fin d)) :=
  faceOf a b (insert i I_Q)

def facetPart {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (Q : Set (EuclideanSpace ℝ (Fin d))) (I_Q T : Finset (Fin n)) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  (facetAt a b I_Q '' ((T \ I_Q : Finset (Fin n)) : Set (Fin n))) ∩ facetsOfFace a b Q

lemma codim2_facet_insert {d n : ℕ} (hd3 : 3 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {v₀ : EuclideanSpace ℝ (Fin d)} (hv₀ : v₀ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hS : IsSimple a b) {Q : Set (EuclideanSpace ℝ (Fin d))} {I_Q : Finset (Fin n)}
    (hQ_eq : Q = faceOf a b I_Q) (hdimQ : dim Q = d - 2) (hIQ_card : I_Q.card = 2) :
    ∀ K ∈ facetsOfFace a b Q, ∃ i ∉ I_Q, K = facetAt a b I_Q i := by
  rintro K ⟨⟨hneK, I_K, hK_eq⟩, hKQ, hdimK⟩
  rw [hK_eq] at hneK
  obtain ⟨w, hw_ext, hw_IK⟩ := nonempty_faceOf_has_vertex a b hv₀ I_K hneK
  have hcard_w : (TightSet a b w).ncard = d := hS.2 w hw_ext
  have hTw_card : (tightFinset a b w).card = d := by rw [card_tightFinset_eq_ncard, hcard_w]
  have hIQ_sub_IK : I_Q ⊆ I_K :=
    faceOf_subset_imp_subset a b hw_ext hcard_w hw_IK (by rwa [hK_eq, hQ_eq] at hKQ)
  obtain ⟨hIK_Tw, hdim_IK⟩ := dim_faceOf_at_simple_vertex a b hw_ext hcard_w I_K hw_IK
  have hIK_le_d : I_K.card ≤ d := (Finset.card_le_card hIK_Tw).trans_eq hTw_card
  have hIK_card : I_K.card = 3 := by
    rw [hK_eq, hdim_IK, hdimQ] at hdimK
    omega
  have hsdiff_one : (I_K \ I_Q).card = 1 := by
    have hs := Finset.card_sdiff_add_card_eq_card hIQ_sub_IK
    omega
  obtain ⟨i, hi_eq⟩ := Finset.card_eq_one.mp hsdiff_one
  have hi_mem : i ∈ I_K \ I_Q := hi_eq ▸ Finset.mem_singleton_self i
  obtain ⟨hi_IK, hi_nIQ⟩ := Finset.mem_sdiff.mp hi_mem
  have hins_eq : insert i I_Q = I_K := by
    ext j
    simp only [Finset.mem_insert]
    constructor
    · rintro (rfl | hjQ)
      · exact hi_IK
      · exact hIQ_sub_IK hjQ
    · intro hjK
      by_cases hjQ : j ∈ I_Q
      · exact Or.inr hjQ
      · have hj_sd : j ∈ I_K \ I_Q := Finset.mem_sdiff.mpr ⟨hjK, hjQ⟩
        rw [hi_eq, Finset.mem_singleton] at hj_sd
        exact Or.inl hj_sd
  exact ⟨i, hi_nIQ, by unfold facetAt; rw [hins_eq, hK_eq]⟩

lemma codim2_facet_inj {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {v₀ : EuclideanSpace ℝ (Fin d)} (hv₀ : v₀ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hS : IsSimple a b) {Q : Set (EuclideanSpace ℝ (Fin d))} {I_Q : Finset (Fin n)}
    {K : Set (EuclideanSpace ℝ (Fin d))} {i₁ i₂ : Fin n}
    (hKfac : K ∈ facetsOfFace a b Q) (_hi₁ : i₁ ∉ I_Q) (hi₂ : i₂ ∉ I_Q)
    (hK1 : K = facetAt a b I_Q i₁) (hK2 : K = facetAt a b I_Q i₂) : i₁ = i₂ := by
  have hne1 : (faceOf a b (insert i₁ I_Q)).Nonempty := by
    have h := hKfac.1.1
    rwa [hK1, facetAt] at h
  obtain ⟨w, hw_ext, hw_1⟩ := nonempty_faceOf_has_vertex a b hv₀ (insert i₁ I_Q) hne1
  have hcard_w : (TightSet a b w).ncard = d := hS.2 w hw_ext
  have heq_face : faceOf a b (insert i₁ I_Q) = faceOf a b (insert i₂ I_Q) := by
    simpa [facetAt] using hK1.symm.trans hK2
  have hsub12 : insert i₂ I_Q ⊆ insert i₁ I_Q :=
    faceOf_subset_imp_subset a b hw_ext hcard_w hw_1 heq_face.le
  have h2in1 : i₂ ∈ insert i₁ I_Q := hsub12 (Finset.mem_insert_self i₂ I_Q)
  rcases Finset.mem_insert.mp h2in1 with rfl | h2Q
  · rfl
  · exact absurd h2Q hi₂

lemma mem_surroundedBy_facetPart {d n : ℕ} (hd3 : 3 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hS : IsSimple a b) {Q : Set (EuclideanSpace ℝ (Fin d))} {I_Q T₁ T₂ : Finset (Fin n)}
    (hQ_eq : Q = faceOf a b I_Q) (hQ_ext : IsExtreme ℝ (Hirsch.Hpoly a b) Q)
    (hdimQ : dim Q = d - 2) (hIQ_card : I_Q.card = 2)
    (huniv : T₁ ∪ T₂ = Finset.univ) (hIQ_T₂ : (I_Q ∩ T₂).card = 1)
    {w : EuclideanSpace ℝ (Fin d)} (hw_ext : w ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hwQ : w ∈ Q) (hw_T₂ : (tightFinset a b w ∩ T₂).card ≤ 1) :
    w ∈ surroundedBy a b Q (facetPart a b Q I_Q T₁) := by
  have hw_IQ : w ∈ faceOf a b I_Q := hQ_eq ▸ hwQ
  have hcard_w : (TightSet a b w).ncard = d := hS.2 w hw_ext
  have hIQ_Tw : I_Q ⊆ tightFinset a b w :=
    (dim_faceOf_at_simple_vertex a b hw_ext hcard_w I_Q hw_IQ).1
  refine ⟨by rw [hQ_ext.extremePoints_eq]; exact ⟨hwQ, hw_ext⟩, ?_⟩
  intro K hKf hwK
  obtain ⟨i, hi_nQ, hKi⟩ := codim2_facet_insert hd3 a b hw_ext hS hQ_eq hdimQ hIQ_card K hKf
  have hw_Fi : w ∈ faceOf a b (insert i I_Q) := by rwa [hKi, facetAt] at hwK
  have hi_Tw : i ∈ tightFinset a b w :=
    mem_tightFinset.mpr (hw_Fi.2 i (Finset.mem_insert_self i I_Q))
  have hi_nT₂ : i ∉ T₂ := by
    intro hiT₂
    have hsub : insert i (I_Q ∩ T₂) ⊆ tightFinset a b w ∩ T₂ := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjQ2
      · exact Finset.mem_inter.mpr ⟨hi_Tw, hiT₂⟩
      · exact Finset.mem_inter.mpr ⟨hIQ_Tw (Finset.inter_subset_left hjQ2),
          Finset.inter_subset_right hjQ2⟩
    have hi_not_inter : i ∉ I_Q ∩ T₂ := fun hm => hi_nQ (Finset.inter_subset_left hm)
    have hcard2 : (insert i (I_Q ∩ T₂)).card = 2 := by
      rw [Finset.card_insert_of_notMem hi_not_inter, hIQ_T₂]
    have hle1 := (Finset.card_le_card hsub).trans hw_T₂
    omega
  have hiT₁ : i ∈ T₁ := by
    have hi_u : i ∈ T₁ ∪ T₂ := by rw [huniv]; exact Finset.mem_univ i
    rcases Finset.mem_union.mp hi_u with h1 | h2
    · exact h1
    · exact absurd h2 hi_nT₂
  exact ⟨⟨i, Finset.mem_sdiff.mpr ⟨hiT₁, hi_nQ⟩, hKi.symm⟩, hKf⟩

lemma inter_card_ge_of_surroundedBy {d n : ℕ} (hd3 : 3 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hS : IsSimple a b) {Q : Set (EuclideanSpace ℝ (Fin d))} {I_Q T : Finset (Fin n)}
    (hQ_eq : Q = faceOf a b I_Q) (hQ_ext : IsExtreme ℝ (Hirsch.Hpoly a b) Q)
    (hdimQ : dim Q = d - 2) (hIQ_card : I_Q.card = 2) (hIQ_T : (I_Q ∩ T).card = 1)
    {u : EuclideanSpace ℝ (Fin d)} (hu_surr : u ∈ surroundedBy a b Q (facetPart a b Q I_Q T)) :
    u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧ d - 1 ≤ (tightFinset a b u ∩ T).card := by
  classical
  obtain ⟨hu_Qext, hu_facs⟩ := hu_surr
  rw [hQ_ext.extremePoints_eq] at hu_Qext
  obtain ⟨huQ, hu_ext⟩ := hu_Qext
  refine ⟨hu_ext, ?_⟩
  have hu_IQ : u ∈ faceOf a b I_Q := hQ_eq ▸ huQ
  have hcard_u : (TightSet a b u).ncard = d := hS.2 u hu_ext
  have hTu_card : (tightFinset a b u).card = d := by rw [card_tightFinset_eq_ncard, hcard_u]
  have hIQ_Tu : I_Q ⊆ tightFinset a b u :=
    (dim_faceOf_at_simple_vertex a b hu_ext hcard_u I_Q hu_IQ).1
  have hsdiff_sub : tightFinset a b u \ I_Q ⊆ T := by
    intro i hi
    obtain ⟨hi_Tu, hi_nQ⟩ := Finset.mem_sdiff.mp hi
    have hu_Fi : u ∈ facetAt a b I_Q i := by
      refine ⟨hu_ext.1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjQ
      · exact mem_tightFinset.mp hi_Tu
      · exact hu_IQ.2 j hjQ
    have hFi_fac : facetAt a b I_Q i ∈ facetsOfFace a b Q := by
      refine ⟨⟨⟨u, hu_Fi⟩, insert i I_Q, rfl⟩, ?_, ?_⟩
      · rw [hQ_eq]
        intro z hz
        exact ⟨hz.1, fun j hj => hz.2 j (Finset.mem_insert_of_mem hj)⟩
      · have hd_Fi := (dim_faceOf_at_simple_vertex a b hu_ext hcard_u (insert i I_Q) hu_Fi).2
        have hcard_ins : (insert i I_Q).card = 3 := by
          rw [Finset.card_insert_of_notMem hi_nQ, hIQ_card]
        change dim (faceOf a b (insert i I_Q)) + 1 = dim Q
        rw [hd_Fi, hcard_ins, hdimQ]
        omega
    have hFi_in : facetAt a b I_Q i ∈ facetPart a b Q I_Q T :=
      hu_facs (facetAt a b I_Q i) hFi_fac hu_Fi
    obtain ⟨⟨i', hi'_S, hFi'⟩, _⟩ := hFi_in
    obtain ⟨hi'T, hi'nQ⟩ := Finset.mem_sdiff.mp hi'_S
    have heq_ii' := codim2_facet_inj a b hu_ext hS hFi_fac hi_nQ hi'nQ rfl hFi'.symm
    rwa [heq_ii']
  have hsub_u : (tightFinset a b u \ I_Q) ∪ (I_Q ∩ T) ⊆ tightFinset a b u ∩ T := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi1 | hi2
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hi1).1, hsdiff_sub hi1⟩
    · exact Finset.mem_inter.mpr ⟨hIQ_Tu (Finset.inter_subset_left hi2),
        Finset.inter_subset_right hi2⟩
  have hdisj_u : Disjoint (tightFinset a b u \ I_Q) (I_Q ∩ T) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_sdiff.mp hi1).2 (Finset.inter_subset_left hi2)
  have hsd_u : (tightFinset a b u \ I_Q).card = d - 2 := by
    have hs := Finset.card_sdiff_add_card_eq_card hIQ_Tu
    omega
  have hc := Finset.card_le_card hsub_u
  rw [Finset.card_union_of_disjoint hdisj_u, hsd_u, hIQ_T] at hc
  omega

end Aux_KW67_proposition_4_1

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep Aux_KW67_proposition_4_1

theorem solution {d : ℕ} (hd : 2 ≤ d)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (_hB : Bornology.IsBounded (Hirsch.Hpoly a b))
    (x' y' : EuclideanSpace ℝ (Fin d)) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hx' : IsFace a b (segment ℝ x x') ∧ dim (segment ℝ x x') = 1)
    (hQ : IsFace a b Q ∧ dim Q = d - 2)
    (hy' : IsFace a b (segment ℝ y' y) ∧ dim (segment ℝ y' y) = 1)
    (hxQ : (segment ℝ x x' ∩ Q).Nonempty) (hQy : (Q ∩ segment ℝ y' y).Nonempty)
    (hA : HasPropertyA a b Q) :
    Hirsch.Reach (Hirsch.Hpoly a b) d x y := by
  classical
  have hd1 : 1 ≤ d := by omega
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
  have hQ_ext : IsExtreme ℝ (Hirsch.Hpoly a b) Q := isExtreme_of_isFace hQ.1
  have hadj_xx' : Hirsch.Adj (Hirsch.Hpoly a b) x x' :=
    ⟨ne_of_dim_segment_eq_one hx'.2, isExtreme_of_isFace hx'.1⟩
  have hx'_ext : x' ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) :=
    adj_right_mem_extremePoints hadj_xx'
  have hadj_y'y : Hirsch.Adj (Hirsch.Hpoly a b) y' y :=
    ⟨ne_of_dim_segment_eq_one hy'.2, isExtreme_of_isFace hy'.1⟩
  have hy'_ext : y' ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) :=
    adj_right_mem_extremePoints (adj_symm hadj_y'y)
  have hu₀_ex : ∃ u₀ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      u₀ ∈ Q ∧ Hirsch.Reach (Hirsch.Hpoly a b) 1 x u₀ ∧
      (tightFinset a b u₀ ∩ tightFinset a b y).card ≤ 1 := by
    rcases endpoint_mem_of_segment_inter_extreme hx_ext.1 hx'_ext.1 hQ_ext hxQ with hxQ_in | hx'Q_in
    · refine ⟨x, hx_ext, hxQ_in, ⟨fun _ => x, rfl, rfl, fun _ _ => Or.inl rfl⟩, ?_⟩
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
      simp
    · refine ⟨x', hx'_ext, hx'Q_in, ?_, ?_⟩
      · refine ⟨fun j => if j = 0 then x else x', by simp, by simp, ?_⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        exact Or.inr (by simpa using hadj_xx')
      · have hcard_x' : (TightSet a b x').ncard = d := hS.2 x' hx'_ext
        have hTx'_card : (tightFinset a b x').card = d := by
          rw [card_tightFinset_eq_ncard, hcard_x']
        have hinter_xx' : (tightFinset a b x ∩ tightFinset a b x').card = d - 1 :=
          adj_inter_tightFinset_card hd1 a b hx_ext hx'_ext hx_ncard hadj_xx'
        have hpart : tightFinset a b x' =
            (tightFinset a b x' ∩ tightFinset a b x) ∪ (tightFinset a b x' ∩ tightFinset a b y) := by
          rw [← Finset.inter_union_distrib_left, huniv, Finset.inter_univ]
        have hdisj_x' : Disjoint
            (tightFinset a b x' ∩ tightFinset a b x) (tightFinset a b x' ∩ tightFinset a b y) :=
          hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
        have hsum_x' : (tightFinset a b x').card =
            (tightFinset a b x' ∩ tightFinset a b x).card +
              (tightFinset a b x' ∩ tightFinset a b y).card := by
          conv_lhs => rw [hpart]
          exact Finset.card_union_of_disjoint hdisj_x'
        rw [Finset.inter_comm (tightFinset a b x') (tightFinset a b x)] at hsum_x'
        omega
  have hQy_symm : (segment ℝ y' y ∩ Q).Nonempty := by rwa [Set.inter_comm]
  have hv₀_ex : ∃ v₀ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      v₀ ∈ Q ∧ Hirsch.Reach (Hirsch.Hpoly a b) 1 v₀ y ∧
      (tightFinset a b v₀ ∩ tightFinset a b x).card ≤ 1 := by
    rcases endpoint_mem_of_segment_inter_extreme hy'_ext.1 hy_ext.1 hQ_ext hQy_symm with hy'Q_in | hyQ_in
    · refine ⟨y', hy'_ext, hy'Q_in, ?_, ?_⟩
      · refine ⟨fun j => if j = 0 then y' else y, by simp, by simp, ?_⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        exact Or.inr (by simpa using hadj_y'y)
      · have hcard_y' : (TightSet a b y').ncard = d := hS.2 y' hy'_ext
        have hTy'_card : (tightFinset a b y').card = d := by
          rw [card_tightFinset_eq_ncard, hcard_y']
        have hinter_yy' : (tightFinset a b y ∩ tightFinset a b y').card = d - 1 :=
          adj_inter_tightFinset_card hd1 a b hy_ext hy'_ext hy_ncard (adj_symm hadj_y'y)
        have hpart : tightFinset a b y' =
            (tightFinset a b y' ∩ tightFinset a b x) ∪ (tightFinset a b y' ∩ tightFinset a b y) := by
          rw [← Finset.inter_union_distrib_left, huniv, Finset.inter_univ]
        have hdisj_y' : Disjoint
            (tightFinset a b y' ∩ tightFinset a b x) (tightFinset a b y' ∩ tightFinset a b y) :=
          hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
        have hsum_y' : (tightFinset a b y').card =
            (tightFinset a b y' ∩ tightFinset a b x).card +
              (tightFinset a b y' ∩ tightFinset a b y).card := by
          conv_lhs => rw [hpart]
          exact Finset.card_union_of_disjoint hdisj_y'
        rw [Finset.inter_comm (tightFinset a b y') (tightFinset a b y)] at hsum_y'
        omega
    · refine ⟨y, hy_ext, hyQ_in, ⟨fun _ => y, rfl, rfl, fun _ _ => Or.inl rfl⟩, ?_⟩
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm]
      simp
  obtain ⟨u₀, hu₀_ext, hu₀Q, hreach_xu₀, hu₀_Ty⟩ := hu₀_ex
  obtain ⟨v₀, hv₀_ext, hv₀Q, hreach_v₀y, hv₀_Tx⟩ := hv₀_ex
  obtain ⟨_, I_Q, hQ_eq⟩ := hQ.1
  have hu₀_IQ : u₀ ∈ faceOf a b I_Q := hQ_eq ▸ hu₀Q
  have hv₀_IQ : v₀ ∈ faceOf a b I_Q := hQ_eq ▸ hv₀Q
  have hcard_u₀ : (TightSet a b u₀).ncard = d := hS.2 u₀ hu₀_ext
  have hcard_v₀ : (TightSet a b v₀).ncard = d := hS.2 v₀ hv₀_ext
  obtain ⟨hIQ_Tu₀, hdimQ_calc⟩ := dim_faceOf_at_simple_vertex a b hu₀_ext hcard_u₀ I_Q hu₀_IQ
  have hIQ_Tv₀ : I_Q ⊆ tightFinset a b v₀ :=
    (dim_faceOf_at_simple_vertex a b hv₀_ext hcard_v₀ I_Q hv₀_IQ).1
  have hTu₀_card : (tightFinset a b u₀).card = d := by
    rw [card_tightFinset_eq_ncard, hcard_u₀]
  have hIQ_le_d : I_Q.card ≤ d := (Finset.card_le_card hIQ_Tu₀).trans_eq hTu₀_card
  have hIQ_card : I_Q.card = 2 := by
    have h1 : dim Q = d - I_Q.card := by rwa [← hQ_eq] at hdimQ_calc
    have h2 := hQ.2
    omega
  by_cases hd2 : d = 2
  · subst hd2
    have hIQ_eq_Tu₀ : I_Q = tightFinset a b u₀ :=
      Finset.eq_of_subset_of_card_le hIQ_Tu₀ (by omega)
    have hv₀_eq_u₀ : v₀ - u₀ = 0 := by
      refine Hirsch.vertex_tight_rows_span 2 (2 * 2) a b u₀ hu₀_ext (v₀ - u₀) ?_
      intro j hj
      have hjIQ : j ∈ I_Q := hIQ_eq_Tu₀ ▸ mem_tightFinset.mpr hj
      rw [inner_sub_right, hv₀_IQ.2 j hjIQ, hj, sub_self]
    have huv0 : u₀ = v₀ := (sub_eq_zero.mp hv₀_eq_u₀).symm
    subst huv0
    exact reach_trans (Hirsch.Hpoly a b) hreach_xu₀ hreach_v₀y
  have hd3 : 3 ≤ d := by omega
  have hIQ_Tx_le : (I_Q ∩ tightFinset a b x).card ≤ 1 :=
    (Finset.card_le_card (Finset.inter_subset_inter_right hIQ_Tv₀)).trans hv₀_Tx
  have hIQ_Ty_le : (I_Q ∩ tightFinset a b y).card ≤ 1 :=
    (Finset.card_le_card (Finset.inter_subset_inter_right hIQ_Tu₀)).trans hu₀_Ty
  have hIQ_part : I_Q.card = (I_Q ∩ tightFinset a b x).card + (I_Q ∩ tightFinset a b y).card := by
    have hp : I_Q = (I_Q ∩ tightFinset a b x) ∪ (I_Q ∩ tightFinset a b y) := by
      rw [← Finset.inter_union_distrib_left, huniv, Finset.inter_univ]
    have hd_iq : Disjoint (I_Q ∩ tightFinset a b x) (I_Q ∩ tightFinset a b y) :=
      hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    conv_lhs => rw [hp]
    exact Finset.card_union_of_disjoint hd_iq
  have hIQ_Tx_eq : (I_Q ∩ tightFinset a b x).card = 1 := by omega
  have hIQ_Ty_eq : (I_Q ∩ tightFinset a b y).card = 1 := by omega
  have hXY_union :
      facetPart a b Q I_Q (tightFinset a b x) ∪ facetPart a b Q I_Q (tightFinset a b y) =
        facetsOfFace a b Q := by
    apply Set.Subset.antisymm
    · exact Set.union_subset Set.inter_subset_right Set.inter_subset_right
    · intro K hKf
      obtain ⟨i, hi_nQ, hKi⟩ :=
        codim2_facet_insert hd3 a b hx_ext hS hQ_eq hQ.2 hIQ_card K hKf
      have hi_univ : i ∈ tightFinset a b x ∪ tightFinset a b y := by
        rw [huniv]; exact Finset.mem_univ i
      rcases Finset.mem_union.mp hi_univ with hiX | hiY
      · exact Or.inl ⟨⟨i, Finset.mem_sdiff.mpr ⟨hiX, hi_nQ⟩, hKi.symm⟩, hKf⟩
      · exact Or.inr ⟨⟨i, Finset.mem_sdiff.mpr ⟨hiY, hi_nQ⟩, hKi.symm⟩, hKf⟩
  have hXY_disj :
      Disjoint (facetPart a b Q I_Q (tightFinset a b x))
        (facetPart a b Q I_Q (tightFinset a b y)) := by
    rw [Set.disjoint_left]
    rintro K ⟨⟨i₁, hi₁, hK1⟩, hKf⟩ ⟨⟨i₂, hi₂, hK2⟩, _⟩
    obtain ⟨hi₁X, hi₁nQ⟩ := Finset.mem_sdiff.mp hi₁
    obtain ⟨hi₂Y, hi₂nQ⟩ := Finset.mem_sdiff.mp hi₂
    have heq_i := codim2_facet_inj a b hx_ext hS hKf hi₁nQ hi₂nQ hK1.symm hK2.symm
    subst heq_i
    exact Finset.disjoint_left.mp hdisj hi₁X hi₂Y
  have hX_encard :
      (facetPart a b Q I_Q (tightFinset a b x)).encard ≤ ((dim Q + 1 : ℕ) : ℕ∞) := by
    let SX : Finset (Fin (2 * d)) := tightFinset a b x \ I_Q
    have hSX_card : SX.card = d - 1 := by
      have hs := Finset.card_sdiff_add_card_inter (tightFinset a b x) I_Q
      rw [Finset.inter_comm (tightFinset a b x) I_Q, hIQ_Tx_eq, hTx_card] at hs
      dsimp [SX]
      omega
    calc (facetPart a b Q I_Q (tightFinset a b x)).encard
        ≤ (facetAt a b I_Q '' (SX : Set (Fin (2 * d)))).encard :=
            Set.encard_le_encard Set.inter_subset_left
      _ ≤ (SX : Set (Fin (2 * d))).encard := Set.encard_image_le (facetAt a b I_Q) _
      _ = (SX.card : ℕ∞) := by simp
      _ = ((dim Q + 1 : ℕ) : ℕ∞) := by congr 1; rw [hSX_card, hQ.2]; omega
  have hY_encard :
      (facetPart a b Q I_Q (tightFinset a b y)).encard ≤ ((dim Q + 1 : ℕ) : ℕ∞) := by
    let SY : Finset (Fin (2 * d)) := tightFinset a b y \ I_Q
    have hSY_card : SY.card = d - 1 := by
      have hs := Finset.card_sdiff_add_card_inter (tightFinset a b y) I_Q
      rw [Finset.inter_comm (tightFinset a b y) I_Q, hIQ_Ty_eq, hTy_card] at hs
      dsimp [SY]
      omega
    calc (facetPart a b Q I_Q (tightFinset a b y)).encard
        ≤ (facetAt a b I_Q '' (SY : Set (Fin (2 * d)))).encard :=
            Set.encard_le_encard Set.inter_subset_left
      _ ≤ (SY : Set (Fin (2 * d))).encard := Set.encard_image_le (facetAt a b I_Q) _
      _ = (SY.card : ℕ∞) := by simp
      _ = ((dim Q + 1 : ℕ) : ℕ∞) := by congr 1; rw [hSY_card, hQ.2]; omega
  have hu₀_surr : u₀ ∈ surroundedBy a b Q (facetPart a b Q I_Q (tightFinset a b x)) :=
    mem_surroundedBy_facetPart hd3 a b hS hQ_eq hQ_ext hQ.2 hIQ_card huniv hIQ_Ty_eq
      hu₀_ext hu₀Q hu₀_Ty
  have huniv_symm : tightFinset a b y ∪ tightFinset a b x = Finset.univ := by
    rwa [Finset.union_comm]
  have hv₀_surr : v₀ ∈ surroundedBy a b Q (facetPart a b Q I_Q (tightFinset a b y)) :=
    mem_surroundedBy_facetPart hd3 a b hS hQ_eq hQ_ext hQ.2 hIQ_card huniv_symm hIQ_Tx_eq
      hv₀_ext hv₀Q hv₀_Tx
  obtain ⟨u, hu_surr, v, hv_surr, hreach_Q⟩ :=
    hA.2.2.2.2 _ _ hXY_union hXY_disj hX_encard hY_encard ⟨u₀, hu₀_surr⟩ ⟨v₀, hv₀_surr⟩
  obtain ⟨hu_ext, hinter_ux⟩ :=
    inter_card_ge_of_surroundedBy hd3 a b hS hQ_eq hQ_ext hQ.2 hIQ_card hIQ_Tx_eq hu_surr
  obtain ⟨hv_ext, hinter_vy⟩ :=
    inter_card_ge_of_surroundedBy hd3 a b hS hQ_eq hQ_ext hQ.2 hIQ_card hIQ_Ty_eq hv_surr
  have hinter_xu : d - 1 ≤ (tightFinset a b x ∩ tightFinset a b u).card := by
    rwa [Finset.inter_comm]
  have hreach_xu : Hirsch.Reach (Hirsch.Hpoly a b) 1 x u :=
    reach_one_of_inter_card_ge hd1 a b hx_ext hu_ext hx_ncard hinter_xu
  have hreach_vy : Hirsch.Reach (Hirsch.Hpoly a b) 1 v y :=
    reach_one_of_inter_card_ge hd1 a b hv_ext hy_ext (hS.2 v hv_ext) hinter_vy
  have hreach_uv : Hirsch.Reach (Hirsch.Hpoly a b) (d - 2) u v := by
    have hr := reach_of_isExtreme hQ_ext hreach_Q
    rwa [hQ.2] at hr
  have htot := reach_trans (Hirsch.Hpoly a b)
    (reach_trans (Hirsch.Hpoly a b) hreach_xu hreach_uv) hreach_vy
  have hsum_d : 1 + (d - 2) + 1 = d := by omega
  rwa [hsum_d] at htot
