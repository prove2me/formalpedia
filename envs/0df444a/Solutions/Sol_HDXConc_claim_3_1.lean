-- Prove2me | solution 1 for HDXConc.claim_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:08.729485+00:00
-- url     : https://prove2.me/submissions/bda00401-eea2-4f99-b000-c21950c5246f

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_tilt
import Definitions.Def_HDXConc_topVar
import Definitions.Def_HDXConc_walkOp

section
set_option autoImplicit false
namespace HDXConc.Dev.C31
open HDXConc

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def c1 (T : Finset (Finset V)) (ρ : Finset V → ℝ) (v : V) : ℝ :=
  ∑ t ∈ T, if v ∈ t then ρ t else 0

noncomputable def c2 (T : Finset (Finset V)) (ρ : Finset V → ℝ) (u v : V) : ℝ :=
  ∑ t ∈ T, if u ∈ t ∧ v ∈ t then ρ t else 0

lemma dc1 (T : Finset (Finset V)) (ρ : Finset V → ℝ) (a : V → ℝ) :
    ∑ v, c1 T ρ v * a v = ∑ t ∈ T, ρ t * ∑ v ∈ t, a v := by
  unfold c1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  simp [ite_mul, Finset.sum_ite_mem, Finset.mul_sum]

lemma dc2 (T : Finset (Finset V)) (ρ : Finset V → ℝ) (φ : V → V → ℝ) :
    ∑ u, ∑ v, c2 T ρ u v * φ u v = ∑ t ∈ T, ρ t * ∑ u ∈ t, ∑ v ∈ t, φ u v := by
  unfold c2
  simp_rw [Finset.sum_mul]
  have : ∀ u : V, ∑ v, ∑ t ∈ T, (if u ∈ t ∧ v ∈ t then ρ t else 0) * φ u v
      = ∑ t ∈ T, ∑ v, (if u ∈ t ∧ v ∈ t then ρ t else 0) * φ u v := fun u => Finset.sum_comm
  simp_rw [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  simp only [ite_and, ite_mul, zero_mul]
  have e : ∀ x, ∑ y, (if x ∈ t then if y ∈ t then ρ t * φ x y else 0 else 0) =
      if x ∈ t then ∑ y ∈ t, ρ t * φ x y else 0 := by
    intro x
    by_cases hx : x ∈ t
    · simp [hx, Finset.sum_ite_mem]
    · simp [hx]
  simp_rw [e]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  simp [Finset.mul_sum]

omit [Fintype V] in
lemma c2_diag (T : Finset (Finset V)) (ρ : Finset V → ℝ) (v : V) : c2 T ρ v v = c1 T ρ v := by
  simp [c1, c2]

omit [Fintype V] in
lemma c1_zero_of_c1 (T : Finset (Finset V)) (ρ : Finset V → ℝ) (hρ : ∀ t ∈ T, 0 ≤ ρ t)
    (u v : V) (h : c1 T ρ v = 0) : c2 T ρ u v = 0 := by
  unfold c1 at h; unfold c2
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun t ht => by
    split_ifs
    · exact hρ t ht
    · exact le_refl _)).1 h
  apply Finset.sum_eq_zero; intro t ht
  have := h0 t ht
  by_cases hu : u ∈ t ∧ v ∈ t
  · rw [if_pos hu]; rw [if_pos hu.2] at this; exact this
  · rw [if_neg hu]


variable {X : Finset (Finset V)} {d : ℕ} {ρ : Finset V → ℝ}

lemma fm1 (v : V) :
    faceMeasure X d ρ 1 {v} = c1 (SteurerHDX.faces X d) ρ v / d := by
  unfold faceMeasure c1
  simp only [Nat.choose_one_right, Finset.sum_filter, Finset.singleton_subset_iff]
  ring

lemma fm2 (u v : V) :
    faceMeasure X d ρ 2 {u, v} = c2 (SteurerHDX.faces X d) ρ u v / (d.choose 2 : ℝ) := by
  unfold faceMeasure c2
  simp only [Finset.sum_filter, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  ring

omit [Fintype V] in
lemma face_sub (hX : SteurerHDX.IsSimplicialComplex X) {t : Finset V}
    (ht : t ∈ SteurerHDX.faces X d) {s : Finset V} (hs : s ⊆ t) : s ∈ X :=
  hX t (Finset.mem_filter.1 ht).1 s hs

lemma c1_zero_vertex (hX : SteurerHDX.IsSimplicialComplex X) (v : V) (hv : v ∉ vertices X) :
    c1 (SteurerHDX.faces X d) ρ v = 0 := by
  unfold c1
  apply Finset.sum_eq_zero; intro t ht
  rw [if_neg]
  intro hvt
  apply hv
  simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact face_sub hX ht (Finset.singleton_subset_iff.2 hvt)

lemma c2_zero (hX : SteurerHDX.IsSimplicialComplex X) (u v : V)
    (h : ¬ (u ∈ vertices X ∧ ({u, v} : Finset V) ∈ X)) :
    c2 (SteurerHDX.faces X d) ρ u v = 0 := by
  unfold c2
  apply Finset.sum_eq_zero; intro t ht
  rw [if_neg]
  rintro ⟨hu, hv⟩
  apply h
  refine ⟨?_, face_sub hX ht ?_⟩
  · simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact face_sub hX ht (Finset.singleton_subset_iff.2 hu)
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption

lemma vsum (hX : SteurerHDX.IsSimplicialComplex X) (a : V → ℝ) :
    ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} * a v =
      (1 / (d : ℝ)) * ∑ v, c1 (SteurerHDX.faces X d) ρ v * a v := by
  simp only [fm1]
  rw [Finset.mul_sum]
  rw [Finset.sum_subset (Finset.subset_univ (vertices X))]
  · apply Finset.sum_congr rfl; intro v _; ring
  · intro v _ hv
    rw [c1_zero_vertex hX v hv]; simp

lemma inner (hX : SteurerHDX.IsSimplicialComplex X) (a : V → ℝ) (v : V) :
    ∑ u ∈ (vertices X).filter (fun u => u ≠ v ∧ ({u, v} : Finset V) ∈ X),
        faceMeasure X d ρ 2 {u, v} * a u =
      (1 / (d.choose 2 : ℝ)) *
        ∑ u ∈ Finset.univ.erase v, c2 (SteurerHDX.faces X d) ρ u v * a u := by
  rw [Finset.mul_sum]
  calc _ = ∑ u ∈ (vertices X).filter (fun u => u ≠ v ∧ ({u, v} : Finset V) ∈ X),
        (1 / (d.choose 2 : ℝ)) * (c2 (SteurerHDX.faces X d) ρ u v * a u) := by
          apply Finset.sum_congr rfl; intro u _
          rw [fm2]; ring
    _ = _ := by
          apply Finset.sum_subset
          · intro u hu
            simp only [Finset.mem_filter] at hu
            simp [hu.2.1]
          · intro u hu hu'
            have : ¬ (u ∈ vertices X ∧ ({u, v} : Finset V) ∈ X) := by
              intro hh
              apply hu'
              simp only [Finset.mem_filter]
              exact ⟨hh.1, (Finset.mem_erase.1 hu).1, hh.2⟩
            rw [c2_zero hX u v this]; simp

theorem main (hd : 2 ≤ d) (hX : SteurerHDX.IsSimplicialComplex X)
    (hρ : ∀ t ∈ SteurerHDX.faces X d, 0 ≤ ρ t) (f : V → ℝ) :
    topVar X d ρ (topSum f) = (d : ℝ) * vertexVar X d ρ f +
      (d : ℝ) * ((d : ℝ) - 1) *
        vertexInner X d ρ (fun v => f v - vertexMean X d ρ f)
          (walkOp X d ρ (fun v => f v - vertexMean X d ρ f)) := by
  set T := SteurerHDX.faces X d with hT
  set μ := vertexMean X d ρ f with hμdef
  set h : V → ℝ := fun v => f v - μ with hh
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hK : (d.choose 2 : ℝ) = d * (d - 1) / 2 := Nat.cast_choose_two ℝ d
  have hμ : μ = (1 / (d : ℝ)) * ∑ v, c1 T ρ v * f v := vsum hX f
  have hm : topMean X d ρ (topSum f) = d * μ := by
    unfold topMean topSum
    rw [← dc1 T ρ f, hμ]; field_simp
  -- left side
  have hL : topVar X d ρ (topSum f) = ∑ u, ∑ v, c2 T ρ u v * (h u * h v) := by
    rw [dc2]
    unfold topVar
    rw [hm]
    apply Finset.sum_congr rfl; intro t ht
    have hc : t.card = d := (Finset.mem_filter.1 ht).2
    have : topSum f t - d * μ = ∑ v ∈ t, h v := by
      simp [topSum, hh, Finset.sum_sub_distrib, hc]
    rw [this, sq, Finset.sum_mul_sum]
  -- variance term
  have hV : (d : ℝ) * vertexVar X d ρ f = ∑ v, c1 T ρ v * h v ^ 2 := by
    unfold vertexVar
    rw [vsum hX (fun v => (f v - vertexMean X d ρ f) ^ 2)]
    field_simp
    rfl
  -- inner product term
  have hI : (d : ℝ) * ((d : ℝ) - 1) * vertexInner X d ρ h (walkOp X d ρ h) =
      ∑ u, ∑ v, c2 T ρ u v * (h u * h v) - ∑ v, c1 T ρ v * h v ^ 2 := by
    have e1 : vertexInner X d ρ h (walkOp X d ρ h) =
        (1 / (d : ℝ)) * ∑ v, c1 T ρ v * (h v * walkOp X d ρ h v) := by
      unfold vertexInner
      rw [← vsum hX (fun v => h v * walkOp X d ρ h v)]
      apply Finset.sum_congr rfl; intro v _; ring
    have e2 : ∀ v, c1 T ρ v * (h v * walkOp X d ρ h v) =
        (h v * ∑ u, c2 T ρ u v * h u - c1 T ρ v * h v ^ 2) / ((d : ℝ) - 1) := by
      intro v
      have hE : ∑ u ∈ Finset.univ.erase v, c2 T ρ u v * h u =
          ∑ u, c2 T ρ u v * h u - c1 T ρ v * h v := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ v), c2_diag]
      have hw : walkOp X d ρ h v = (1 / (2 * (c1 T ρ v / d))) *
          ((1 / (d.choose 2 : ℝ)) * (∑ u, c2 T ρ u v * h u - c1 T ρ v * h v)) := by
        unfold walkOp
        rw [inner hX h v, fm1, hE]
      rw [hw]
      by_cases hc : c1 T ρ v = 0
      · have : ∀ u, c2 T ρ u v = 0 := fun u => c1_zero_of_c1 T ρ hρ u v hc
        simp [this, hc]
      · rw [hK]; field_simp
    rw [e1]
    simp_rw [e2]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    have : ∑ v, h v * ∑ u, c2 T ρ u v * h u = ∑ u, ∑ v, c2 T ρ u v * (h u * h v) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _
      ring
    rw [this]
    field_simp
  rw [hL, hV, hI]; ring

end HDXConc.Dev.C31

namespace HDXConc
open HDXConc.Dev.C31 in
theorem chk_claim_3_1 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d)
    {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π)
    (f : V → ℝ) (t : ℝ) :
    topVar X d (tilt X d π f t) (topSum f) =
      (d : ℝ) * vertexVar X d (tilt X d π f t) f +
        (d : ℝ) * ((d : ℝ) - 1) *
          vertexInner X d (tilt X d π f t)
            (fun v => f v - vertexMean X d (tilt X d π f t) f)
            (walkOp X d (tilt X d π f t) (fun v => f v - vertexMean X d (tilt X d π f t) f)) := by
  apply main hd hX.1
  intro σ hσ
  unfold tilt
  apply div_nonneg
  · exact mul_nonneg (hπ.pos σ hσ).le (Real.exp_pos _).le
  · exact Finset.sum_nonneg (fun σ' hσ' => mul_nonneg (hπ.pos σ' hσ').le (Real.exp_pos _).le)
end HDXConc
end

theorem solution : type_of% @HDXConc.chk_claim_3_1 := @HDXConc.chk_claim_3_1
