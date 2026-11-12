-- Prove2me | solution 1 for HDXConc.tilted_variance_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:10.445191+00:00
-- url     : https://prove2.me/submissions/f327c255-6315-4150-855a-9b10d3492f73

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_tilt
import Definitions.Def_HDXConc_topVar
import Definitions.Def_HDXConc_walkOp
import Theorems.Thm_HDXConc_claim_3_1
import Theorems.Thm_HDXConc_claim_3_2

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace HDXConc.Dev.TV
open HDXConc

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mem_faces {d : ℕ} {X : Finset (Finset V)} {t : Finset V} :
    t ∈ SteurerHDX.faces X d ↔ t ∈ X ∧ t.card = d := by
  simp [SteurerHDX.faces]

lemma tilt_density {d : ℕ} {X : Finset (Finset V)} {π : Finset V → ℝ} (hπ : IsTopDensity X d π)
    (f : V → ℝ) (t : ℝ) : IsTopDensity X d (tilt X d π f t) := by
  have hZ : 0 < ∑ σ' ∈ SteurerHDX.faces X d, π σ' * Real.exp (t * topSum f σ') := by
    have hne : (SteurerHDX.faces X d).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have := hπ.sum_eq_one; rw [h] at this; simp at this
    exact Finset.sum_pos (fun σ hσ => mul_pos (hπ.pos σ hσ) (Real.exp_pos _)) hne
  refine ⟨fun σ hσ => ?_, ?_⟩
  · unfold tilt; exact div_pos (mul_pos (hπ.pos σ hσ) (Real.exp_pos _)) hZ
  · unfold tilt
    rw [← Finset.sum_div, div_self hZ.ne']


lemma exists_facet {d : ℕ} {X : Finset (Finset V)} (hX : SteurerHDX.IsPure X d) {σ : Finset V}
    (hσ : σ ∈ X) : ∃ t ∈ SteurerHDX.faces X d, σ ⊆ t := by
  have hne : (X.filter (fun τ => σ ⊆ τ)).Nonempty := ⟨σ, by simp [hσ]⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter] at hm
  refine ⟨m, ?_, hm.2⟩
  have : m.card = d := by
    apply hX.2 m hm.1
    intro ρ hρ hmρ
    have := hmax ρ (by simp [hρ, hm.2.trans hmρ])
    exact (Finset.eq_of_subset_of_card_le hmρ this).symm
  simp [SteurerHDX.faces, hm.1, this]

section gen0
variable {d : ℕ} {X : Finset (Finset V)} {ρ : Finset V → ℝ}
lemma face_sub (hX : SteurerHDX.IsPure X d) {t : Finset V} (ht : t ∈ SteurerHDX.faces X d) :
    ∀ u ∈ t, u ∈ vertices X := by
  intro u hu
  rw [mem_faces] at ht
  simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hX.1 t ht.1 _ (by simpa using hu)

lemma vertices_eq : linkVerts X ∅ = vertices X := by
  ext v; simp [linkVerts, vertices]

lemma pi1_eq (hd : 2 ≤ d) (v : V) :
    faceMeasure X d ρ 1 {v} = (1 / (d : ℝ)) * ∑ t ∈ SteurerHDX.faces X d, if v ∈ t then ρ t else 0 := by
  unfold faceMeasure
  rw [Nat.choose_one_right, ← Finset.sum_filter]
  congr 2
  ext t; simp

lemma pi1_sum (hX : SteurerHDX.IsPure X d) (hd : 2 ≤ d) (a : V → ℝ) :
    ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} * a v =
      (1 / (d : ℝ)) * ∑ t ∈ SteurerHDX.faces X d, ρ t * ∑ v ∈ t, a v := by
  simp_rw [pi1_eq hd, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t ht
  have := face_sub hX ht
  have e : ∑ v ∈ vertices X, (if v ∈ t then ρ t else 0) * a v = ∑ v ∈ t, ρ t * a v := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (fun u hu => this u hu)]
  rw [e, Finset.mul_sum]

lemma pi1_total (hX : SteurerHDX.IsPure X d) (hd : 2 ≤ d) (hρ : IsTopDensity X d ρ) :
    ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} = 1 := by
  have := pi1_sum (ρ := ρ) hX hd (fun _ => (1 : ℝ))
  simp only [mul_one] at this
  rw [this]
  have h1 : ∀ t ∈ SteurerHDX.faces X d, ρ t * ∑ v ∈ t, (1 : ℝ) = ρ t * d := by
    intro t ht; rw [mem_faces] at ht; simp [ht.2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, hρ.sum_eq_one]
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : (d : ℝ) ≠ 0 := by linarith
  field_simp

lemma pi1_pos (hX : SteurerHDX.IsPure X d) (hd : 2 ≤ d) (hρ : IsTopDensity X d ρ) {v : V}
    (hv : v ∈ vertices X) : 0 < faceMeasure X d ρ 1 {v} := by
  obtain ⟨t, ht, hsub⟩ := exists_facet hX (σ := {v}) (by simpa [vertices] using hv)
  rw [pi1_eq hd]
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply mul_pos (by positivity)
  have hnn : ∀ t' ∈ SteurerHDX.faces X d, 0 ≤ (if v ∈ t' then ρ t' else 0) := by
    intro t' ht'; split_ifs
    · exact (hρ.pos t' ht').le
    · exact le_rfl
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn ht)
  rw [if_pos (by simpa using hsub)]
  exact hρ.pos t ht

lemma lw_empty (u v : V) : linkWeight X d ρ ∅ u v =
    if u ≠ v then ∑ t ∈ (SteurerHDX.faces X d).filter (fun t => ({u, v} : Finset V) ⊆ t), ρ t else 0 := by
  unfold linkWeight; simp

lemma deg_eq (hX : SteurerHDX.IsPure X d) (hd : 2 ≤ d) {v : V} (hv : v ∈ vertices X) :
    weightedDeg (linkVerts X ∅) (linkWeight X d ρ ∅) v =
      ((d : ℝ) - 1) * ((d : ℝ) * faceMeasure X d ρ 1 {v}) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  rw [pi1_eq hd, ← mul_assoc, mul_assoc ((d : ℝ) - 1) (d : ℝ), ← mul_assoc (d : ℝ) (1 / (d : ℝ)), mul_one_div_cancel hd0, one_mul]
  unfold weightedDeg
  rw [vertices_eq]
  simp_rw [lw_empty]
  rw [← Finset.sum_filter, Finset.sum_congr rfl (fun u _ => Finset.sum_filter _ _), Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t ht
  have hsub := face_sub hX ht
  have hc := (mem_faces.1 ht).2
  by_cases hvt : v ∈ t
  · rw [if_pos hvt]
    have : ((vertices X).filter (fun u => v ≠ u)) = (vertices X).erase v := by
      ext u; simp only [Finset.mem_filter, Finset.mem_erase]; constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> first | exact h.1 | exact h.2 | exact fun e => h.1 e.symm | exact fun e => h.2 e.symm
    have e : ∀ u ∈ (vertices X).filter (fun u => v ≠ u),
        (if ({v, u} : Finset V) ⊆ t then ρ t else 0) = if u ∈ t then ρ t else 0 := by
      intro u hu
      simp [Finset.insert_subset_iff, hvt]
    rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
    have : ((vertices X).filter (fun u => v ≠ u)).filter (fun u => u ∈ t) = t.erase v := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, h⟩, h2⟩; exact ⟨fun e => h e.symm, h2⟩
      · rintro ⟨h, h2⟩; exact ⟨⟨hsub u h2, fun e => h e.symm⟩, h2⟩
    rw [this, Finset.sum_const, Finset.card_erase_of_mem hvt, hc]
    simp [Nat.cast_sub (by omega : 1 ≤ d)]
  · rw [if_neg hvt]
    simp only [mul_zero]
    apply Finset.sum_eq_zero; intro u hu
    rw [if_neg]
    intro h; exact hvt (h (by simp))

lemma R_zero (hX : SteurerHDX.IsPure X d) {u v : V} (h : ({u, v} : Finset V) ∉ X) :
    ∑ t ∈ (SteurerHDX.faces X d).filter (fun t => ({u, v} : Finset V) ⊆ t), ρ t = 0 := by
  apply Finset.sum_eq_zero; intro t ht
  rw [Finset.mem_filter, mem_faces] at ht
  exact absurd (hX.1 t ht.1.1 _ ht.2) h

lemma Q_eq (hX : SteurerHDX.IsPure X d) (hd : 2 ≤ d) (hρ : IsTopDensity X d ρ) (h : V → ℝ) :
    ∑ u ∈ linkVerts X ∅, ∑ v ∈ linkVerts X ∅, linkWeight X d ρ ∅ u v * h u * h v =
      (d : ℝ) * ((d : ℝ) - 1) * vertexInner X d ρ h (walkOp X d ρ h) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hC : ((d.choose 2 : ℕ) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ d
  have hC0 : (d : ℝ) * ((d : ℝ) - 1) ≠ 0 := by nlinarith
  rw [vertices_eq]
  unfold vertexInner
  have step : ∀ v ∈ vertices X, faceMeasure X d ρ 1 {v} * h v * walkOp X d ρ h v =
      h v / 2 * ∑ u ∈ vertices X, (if u ≠ v then
        (1 / ((d : ℝ) * ((d : ℝ) - 1) / 2)) *
          (∑ t ∈ (SteurerHDX.faces X d).filter (fun t => ({u, v} : Finset V) ⊆ t), ρ t) * h u else 0) := by
    intro v hv
    have hp := (pi1_pos hX hd hρ hv).ne'
    unfold walkOp
    rw [← Finset.sum_filter]
    have hS : ∑ u ∈ (vertices X).filter (fun u => u ≠ v ∧ ({u, v} : Finset V) ∈ X),
          faceMeasure X d ρ 2 {u, v} * h u =
        ∑ u ∈ (vertices X).filter (fun u => u ≠ v),
          (1 / ((d : ℝ) * ((d : ℝ) - 1) / 2)) *
            (∑ t ∈ (SteurerHDX.faces X d).filter (fun t => ({u, v} : Finset V) ⊆ t), ρ t) * h u := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro u hu
      by_cases huv : u ≠ v
      · by_cases hm : ({u, v} : Finset V) ∈ X
        · simp only [huv, hm, ne_eq, not_false_eq_true, and_self, if_true]
          unfold faceMeasure; rw [hC]
        · simp only [huv, hm, ne_eq, not_false_eq_true, and_false, if_false, if_true]
          rw [R_zero hX hm]; simp
      · simp [huv]
    rw [hS, Finset.sum_filter]
    field_simp
  rw [Finset.sum_congr rfl step, Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v hv
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro u hu
  rw [lw_empty]
  by_cases huv : u ≠ v
  · have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    rw [if_pos huv, if_pos huv]
    field_simp
  · simp [huv]

end gen0
end HDXConc.Dev.TV

namespace HDXConc
open HDXConc.Dev.TV in
theorem chk_tilted_variance_le {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {t : ℝ} (ht : |t| ≤ η / 2) :
    topVar X d (tilt X d π f t) (topSum f) ≤ (d : ℝ) / (2 * η) := by
  have hρ := tilt_density hπ f t
  set ρ := tilt X d π f t with hρdef
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h32 := claim_3_2 hd hη0 hη1 hX hπ hexp f hf ht
  have h31 := claim_3_1 hd hX hπ f t
  rw [← hρdef] at h32 h31
  set μ := vertexMean X d ρ f with hμ
  have htot := pi1_total hX hd hρ
  have hμ' : ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} * f v = μ := rfl
  have hdeg : ∀ v ∈ linkVerts X ∅, weightedDeg (linkVerts X ∅) (linkWeight X d ρ ∅) v =
      ((d : ℝ) - 1) * ((d : ℝ) * faceMeasure X d ρ 1 {v}) := by
    intro v hv; rw [vertices_eq] at hv; exact deg_eq hX hd hv
  have hsum0 : ∑ v ∈ linkVerts X ∅, weightedDeg (linkVerts X ∅) (linkWeight X d ρ ∅) v * (f v - μ) = 0 := by
    rw [Finset.sum_congr rfl (fun v hv => by rw [hdeg v hv]), vertices_eq]
    have : ∑ v ∈ vertices X, ((d : ℝ) - 1) * ((d : ℝ) * faceMeasure X d ρ 1 {v}) * (f v - μ) =
        ((d : ℝ) - 1) * (d : ℝ) * (∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} * f v -
          μ * ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v}) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _; ring
    rw [this, hμ', htot]; ring
  have hspec := h32 (fun v => f v - μ) hsum0
  rw [Q_eq hX hd hρ] at hspec
  have hden : ∑ v ∈ linkVerts X ∅, weightedDeg (linkVerts X ∅) (linkWeight X d ρ ∅) v * (f v - μ) ^ 2 =
      ((d : ℝ) - 1) * (d : ℝ) * vertexVar X d ρ f := by
    rw [Finset.sum_congr rfl (fun v hv => by rw [hdeg v hv]), vertices_eq]
    unfold vertexVar
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _; ring
  rw [hden] at hspec
  have hV : vertexVar X d ρ f ≤ 1 / 4 := by
    unfold vertexVar
    have : ∀ v ∈ vertices X, faceMeasure X d ρ 1 {v} * (f v - μ) ^ 2 ≤
        faceMeasure X d ρ 1 {v} * f v - 2 * μ * (faceMeasure X d ρ 1 {v} * f v) +
          μ ^ 2 * faceMeasure X d ρ 1 {v} := by
      intro v hv
      have hp := (pi1_pos hX hd hρ hv).le
      have hfv := hf v (by simpa [vertices] using hv)
      have : f v ^ 2 ≤ f v := by nlinarith [hfv.1, hfv.2]
      nlinarith
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hμ', htot]
    nlinarith [sq_nonneg (μ - 1 / 2)]
  have hV0 : 0 ≤ vertexVar X d ρ f :=
    Finset.sum_nonneg (fun v hv => mul_nonneg (pi1_pos hX hd hρ hv).le (sq_nonneg _))
  rw [h31]
  have hlam : (2 / η - 1) / ((d : ℝ) - 1) * (((d : ℝ) - 1) * (d : ℝ) * vertexVar X d ρ f) =
      (2 / η - 1) * (d : ℝ) * vertexVar X d ρ f := by
    have : (d : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hlam] at hspec
  have hfin : (d : ℝ) * vertexVar X d ρ f + (2 / η - 1) * (d : ℝ) * vertexVar X d ρ f =
      2 / η * ((d : ℝ) * vertexVar X d ρ f) := by ring
  have h2η : 0 ≤ 2 / η := by positivity
  calc _ ≤ (d : ℝ) * vertexVar X d ρ f + (2 / η - 1) * (d : ℝ) * vertexVar X d ρ f := by linarith
    _ = 2 / η * ((d : ℝ) * vertexVar X d ρ f) := hfin
    _ ≤ 2 / η * ((d : ℝ) * (1 / 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV (by linarith)) h2η
    _ = (d : ℝ) / (2 * η) := by field_simp; ring
end HDXConc
end

theorem solution : type_of% @HDXConc.chk_tilted_variance_le := @HDXConc.chk_tilted_variance_le
