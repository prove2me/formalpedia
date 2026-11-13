-- Prove2me | solution 1 for HDXHitting.good_vertex
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:53.127088+00:00
-- url     : https://prove2.me/submissions/bcd9661b-ceee-4997-9aa2-0411d567a549

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_linkDist
import Theorems.Thm_HDXHitting_fact_2_1_eigenvalue

section
set_option autoImplicit false
namespace HDXHitting.Dev.GV
open HDXHitting

/-- degree of a vertex: `P u = Pr[u ∈ σ]`. -/
noncomputable def P {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (u : V) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => u ∈ σ), p σ

theorem lw_eq {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (u w : V) :
    linkWeight p ∅ u w = ∑ σ : Finset V, if (u ≠ w ∧ u ∈ σ ∧ w ∈ σ) then p σ else 0 := by
  unfold linkWeight
  by_cases h : u ≠ w
  · rw [if_pos (by simpa using h), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    have : (insert u (insert w (∅ : Finset V)) ⊆ σ) ↔ (u ∈ σ ∧ w ∈ σ) := by
      simp [Finset.insert_subset_iff]
    simp only [this]
    simp [h]
  · rw [if_neg (by simpa using h)]
    simp only [h, false_and, if_false, Finset.sum_const_zero]

theorem lw_nonneg {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (hp : IsTopDist d p) (u w : V) : 0 ≤ linkWeight p ∅ u w := by
  rw [lw_eq]
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact hp.1 σ
  · exact le_rfl

theorem lw_symm {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (u w : V) :
    linkWeight p ∅ u w = linkWeight p ∅ w u := by
  rw [lw_eq, lw_eq]
  apply Finset.sum_congr rfl
  intro σ _
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a.symm, c, b⟩
  · rintro ⟨a, b, c⟩; exact ⟨a.symm, c, b⟩

theorem sum_P {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (hp : IsTopDist d p) : ∑ u, P p u = d := by
  unfold P
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  have : ∀ σ : Finset V, (∑ u : V, if u ∈ σ then p σ else 0) = d * p σ := by
    intro σ
    by_cases h : p σ = 0
    · simp [h]
    · rw [← Finset.sum_filter, Finset.sum_const]
      have : Finset.univ.filter (fun u : V => u ∈ σ) = σ := by ext; simp
      rw [this, hp.2.1 σ h]
      simp
  simp_rw [this, ← Finset.mul_sum, hp.2.2, mul_one]

theorem sum_W {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (hp : IsTopDist d p) (u : V) :
    ∑ w, linkWeight p ∅ u w = ((d : ℝ) - 1) * P p u := by
  simp_rw [lw_eq]
  rw [Finset.sum_comm]
  unfold P
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : p σ = 0
  · simp [h]
  · by_cases hu : u ∈ σ
    · have hc : σ.card = d := hp.2.1 σ h
      have hd1 : 1 ≤ d := by
        rw [← hc]; exact Finset.card_pos.mpr ⟨u, hu⟩
      rw [← Finset.sum_filter, Finset.sum_const]
      have : Finset.univ.filter (fun w : V => u ≠ w ∧ u ∈ σ ∧ w ∈ σ) = σ.erase u := by
        ext w; simp [hu]; tauto
      rw [this, Finset.card_erase_of_mem hu, hc, if_pos hu]
      simp [Nat.cast_sub hd1]
    · simp [hu]

theorem scale_secondEig {V : Type*} [Fintype V] (W : V → V → ℝ) (lam c : ℝ) (hc : 0 < c)
    (h : HDXConc.SecondEigLE Finset.univ W lam) :
    HDXConc.SecondEigLE Finset.univ (fun u v => c * W u v) lam := by
  intro g hg
  have hd : ∀ v, HDXConc.weightedDeg Finset.univ (fun u v => c * W u v) v =
      c * HDXConc.weightedDeg Finset.univ W v := by
    intro v; unfold HDXConc.weightedDeg; rw [Finset.mul_sum]
  simp_rw [hd] at hg ⊢
  have hg' : ∑ v, HDXConc.weightedDeg Finset.univ W v * g v = 0 := by
    have : ∑ v, c * HDXConc.weightedDeg Finset.univ W v * g v =
        c * ∑ v, HDXConc.weightedDeg Finset.univ W v * g v := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
    rw [this] at hg
    exact (mul_eq_zero.mp hg).resolve_left hc.ne'
  have := h g hg'
  have e1 : ∑ u, ∑ v, c * W u v * g u * g v = c * ∑ u, ∑ v, W u v * g u * g v := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
  have e2 : ∑ v, c * HDXConc.weightedDeg Finset.univ W v * g v ^ 2 =
      c * ∑ v, HDXConc.weightedDeg Finset.univ W v * g v ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
  rw [e1, e2]
  nlinarith

theorem link_sum {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (v w : V)
    (hv : 0 < P p v) :
    P p v * ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => w ∈ σ), linkDist p {v} σ =
      linkWeight p ∅ v w := by
  by_cases hw : w = v
  · subst hw
    rw [lw_eq]
    simp only [ne_eq, not_true_eq_false, false_and, if_false, Finset.sum_const_zero]
    have : ∀ σ ∈ Finset.univ.filter (fun σ : Finset V => w ∈ σ), linkDist p {w} σ = 0 := by
      intro σ hσ
      unfold linkDist
      rw [if_neg]
      rw [Finset.disjoint_singleton_left]
      simpa using hσ
    rw [Finset.sum_eq_zero this, mul_zero]
  · rw [lw_eq]
    unfold linkDist
    have hP : (∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => ({v} : Finset V) ⊆ σ'), p σ') = P p v := by
      unfold P; apply Finset.sum_congr _ (fun _ _ => rfl); ext; simp
    simp_rw [hP]
    rw [Finset.mul_sum, Finset.sum_filter]
    have e : ∀ σ : Finset V, (if w ∈ σ then P p v * (if Disjoint ({v} : Finset V) σ then p ({v} ∪ σ) / P p v else 0) else 0)
        = if (w ∈ σ ∧ v ∉ σ) then p (insert v σ) else 0 := by
      intro σ
      by_cases h1 : w ∈ σ
      · by_cases h2 : v ∈ σ
        · simp [h1, h2]
        · have : Disjoint ({v} : Finset V) σ := by simpa using h2
          rw [if_pos h1, if_pos this, if_pos ⟨h1, h2⟩]
          rw [Finset.singleton_union]
          field_simp
      · simp [h1]
    simp_rw [e]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun σ => insert v σ) (fun σ => σ.erase v) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ; simp at hσ ⊢; exact ⟨fun h => hw h.symm, Or.inr hσ.1⟩
    · intro σ hσ; simp at hσ ⊢; exact ⟨hw, hσ.2.2⟩
    · intro σ hσ; simp at hσ ⊢; exact hσ.2
    · intro σ hσ; simp at hσ ⊢; exact Finset.insert_erase hσ.2.1
    · intro σ hσ; rfl

theorem link_mean {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 2 ≤ d)
    (p : Finset V → ℝ) (v : V) (hv : 0 < P p v) (f : V → ℝ) :
    mean (d - 1) (linkDist p {v}) f * (((d : ℝ) - 1) * P p v) = ∑ w, linkWeight p ∅ v w * f w := by
  unfold mean vertexMeasure
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hpos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [hd1, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  have := link_sum p v w hv
  rw [← this]
  field_simp

theorem vm_eq {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ) (v : V) :
    vertexMeasure d p v = (1 / (d : ℝ)) * P p v := rfl

end HDXHitting.Dev.GV
namespace HDXHitting
open HDXHitting.Dev.GV in
theorem chk_good_vertex {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 2 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsOneSidedHDX d p lam) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    (hμ : 0 < mean d p f) :
    ∃ v, 0 < f v ∧ 0 < vertexMeasure d p v ∧
      mean (d - 1) (linkDist p {v}) f ≤ mean d p f + lam := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hd1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
  set T : ℝ := (d : ℝ) * ((d : ℝ) - 1) with hT
  have hTpos : 0 < T := by rw [hT]; nlinarith
  set μ := mean d p f with hμdef
  have hμP : μ = ∑ u, (1 / (d : ℝ)) * P p u * f u := by
    rw [hμdef]; unfold mean; simp_rw [vm_eq]
  set W' : V → V → ℝ := fun u w => (1 / T) * linkWeight p ∅ u w with hW'
  have h1 := HDXHitting.fact_2_1_eigenvalue W'
    (fun u w => mul_nonneg (by positivity) (lw_nonneg d p hp u w))
    (fun u w => by simp only [hW']; rw [lw_symm])
    (by
      simp only [hW']
      simp_rw [← Finset.mul_sum, sum_W d p hp]
      rw [← Finset.mul_sum, sum_P d p hp, hT]
      field_simp)
    lam hlam (scale_secondEig _ lam (1 / T) (by positivity) (hX ∅ (by simpa using hd))) f hf μ
    (by
      rw [hμP]
      apply Finset.sum_congr rfl
      intro u _
      simp only [hW']
      rw [← Finset.mul_sum, sum_W d p hp, hT]
      field_simp)
  have hS : ∑ u, ∑ w, linkWeight p ∅ u w * f u * f w ≤ T * (μ ^ 2 + lam * μ) := by
    have := h1.1.trans h1.2
    simp only [hW'] at this
    have e : ∑ u, ∑ w, 1 / T * linkWeight p ∅ u w * f u * f w =
        (1 / T) * ∑ u, ∑ w, linkWeight p ∅ u w * f u * f w := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left this hTpos.le
    rw [← mul_assoc, mul_one_div_cancel hTpos.ne', one_mul] at this
    exact this
  by_contra hcon
  push Not at hcon
  -- every good candidate has link mean > μ + lam
  have strict : ∀ u, 0 < f u → 0 < P p u →
      (((d : ℝ) - 1) * P p u * (μ + lam)) * f u < f u * ∑ w, linkWeight p ∅ u w * f w := by
    intro u hfu hPu
    have hvm : 0 < vertexMeasure d p u := by
      rw [vm_eq]; positivity
    have h3 := hcon u hfu hvm
    have hm := link_mean d hd p u hPu f
    have hpos : 0 < ((d : ℝ) - 1) * P p u := mul_pos (by linarith) hPu
    have : (μ + lam) * (((d : ℝ) - 1) * P p u) < ∑ w, linkWeight p ∅ u w * f w := by
      rw [← hm]; exact mul_lt_mul_of_pos_right h3 hpos
    nlinarith
  have key : ∀ u, (((d : ℝ) - 1) * P p u * (μ + lam)) * f u ≤ f u * ∑ w, linkWeight p ∅ u w * f w := by
    intro u
    have hPu : 0 ≤ P p u := by
      unfold P; exact Finset.sum_nonneg (fun σ _ => hp.1 σ)
    by_cases h0 : f u = 0
    · simp [h0]
    · have hf0 : 0 < f u := lt_of_le_of_ne (hf u).1 (Ne.symm h0)
      by_cases hP0 : P p u = 0
      · have : ∀ w, linkWeight p ∅ u w = 0 := by
          intro w
          have hs := sum_W d p hp u
          rw [hP0, mul_zero] at hs
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => lw_nonneg d p hp u w)).mp hs w (Finset.mem_univ w)
        simp [this, hP0]
      · exact (strict u hf0 (lt_of_le_of_ne hPu (Ne.symm hP0))).le
  have hlt : ∃ u ∈ (Finset.univ : Finset V), (((d : ℝ) - 1) * P p u * (μ + lam)) * f u <
      f u * ∑ w, linkWeight p ∅ u w * f w := by
    by_contra hno
    push Not at hno
    have hall : ∀ u, P p u * f u ≤ 0 := by
      intro u
      by_contra hc
      push Not at hc
      have hPu : 0 < P p u := by
        by_contra h; push Not at h
        have : P p u = 0 := le_antisymm h (by unfold P; exact Finset.sum_nonneg (fun σ _ => hp.1 σ))
        rw [this] at hc; simp at hc
      have hfu : 0 < f u := by
        by_contra h; push Not at h
        have : f u = 0 := le_antisymm h (hf u).1
        rw [this] at hc; simp at hc
      exact absurd (strict u hfu hPu) (not_lt.mpr (hno u (Finset.mem_univ u)))
    have h2 : ∑ u, P p u * f u = d * μ := by
      rw [hμP, Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; field_simp
    have : ∑ u, P p u * f u ≤ 0 := Finset.sum_nonpos (fun u _ => hall u)
    rw [h2] at this
    have : 0 < (d : ℝ) * μ := by positivity
    linarith
  have := Finset.sum_lt_sum (fun u _ => key u) hlt
  have e1 : ∑ u, (((d : ℝ) - 1) * P p u * (μ + lam)) * f u = T * (μ ^ 2 + lam * μ) := by
    have : ∑ u, (((d : ℝ) - 1) * P p u * (μ + lam)) * f u =
        ((d : ℝ) - 1) * (μ + lam) * ∑ u, P p u * f u := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
    rw [this]
    have h2 : ∑ u, P p u * f u = d * μ := by
      rw [hμP, Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; field_simp
    rw [h2, hT]; ring
  have e2 : ∑ u, f u * ∑ w, linkWeight p ∅ u w * f w = ∑ u, ∑ w, linkWeight p ∅ u w * f u * f w := by
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring
  rw [e1, e2] at this
  linarith

end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_good_vertex := @HDXHitting.chk_good_vertex
