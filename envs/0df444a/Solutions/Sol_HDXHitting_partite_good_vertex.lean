-- Prove2me | solution 1 for HDXHitting.partite_good_vertex
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:53.668359+00:00
-- url     : https://prove2.me/submissions/0bdd8a14-98c9-48b5-bd8c-ccc830bcd6e9

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX
import Definitions.Def_HDXHitting_linkDist
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly
import Theorems.Thm_HDXHitting_fact_2_1_bipartite
import Theorems.Thm_HDXHitting_cpoly_monotone_log_concave

section
set_option autoImplicit false
namespace HDXHitting.Dev.PGV
open HDXHitting

noncomputable def Pm {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (v : V) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ

theorem card_colour {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (S : Finset ι) (hc : IsRainbow p c S) {σ : Finset V}
    (hσ : p σ ≠ 0) {k : ι} (hk : k ∈ S) :
    (Finset.univ.filter (fun w => w ∈ σ ∧ c w = k)).card = 1 := by
  obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := (hc σ hσ).2 k hk
  rw [Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => hu w h, fun h => h ▸ ⟨hu1, hu2⟩⟩

theorem row_sum {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (S : Finset ι) (hc : IsRainbow p c S) {k : ι}
    (hk : k ∈ S) (u : V) (hu : c u ≠ k) :
    ∑ w ∈ Finset.univ.filter (fun w => c w = k), linkWeight p ∅ u w = Pm p u := by
  have h1 : ∀ w ∈ Finset.univ.filter (fun w => c w = k), linkWeight p ∅ u w =
      ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => u ∈ σ ∧ w ∈ σ), p σ := by
    intro w hw
    have hne : u ≠ w := by
      intro h; subst h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hu hw
    unfold linkWeight
    rw [if_pos ⟨hne, by simp, by simp⟩]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext σ; simp [Finset.insert_subset_iff]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ w : V, ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => u ∈ σ ∧ w ∈ σ), p σ =
      ∑ σ : Finset V, if u ∈ σ ∧ w ∈ σ then p σ else 0 := fun w => by rw [Finset.sum_filter]
  simp only [h2]
  rw [Finset.sum_comm]
  unfold Pm; rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro σ _
  by_cases h0 : p σ = 0
  · simp [h0]
  · by_cases hu' : u ∈ σ
    · simp only [hu', true_and, if_true]
      have := card_colour p c S hc h0 hk
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_filter]
      have e : (Finset.univ.filter (fun w => c w = k ∧ w ∈ σ)) =
          Finset.univ.filter (fun w => w ∈ σ ∧ c w = k) := by
        ext w; simp [and_comm]
      rw [e, this]; simp
    · simp [hu']

theorem Pm_nonneg {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (h0 : ∀ σ, 0 ≤ p σ) (v : V) : 0 ≤ Pm p v :=
  Finset.sum_nonneg (fun σ _ => h0 σ)

theorem colour_swap {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (k : ι) (a : V → ℝ) :
    ∑ u ∈ Finset.univ.filter (fun u => c u = k), Pm p u * a u =
      ∑ σ : Finset V, p σ * ∑ u ∈ Finset.univ.filter (fun u => u ∈ σ ∧ c u = k), a u := by
  have h1 : ∑ u ∈ Finset.univ.filter (fun u => c u = k), Pm p u * a u =
      ∑ u : V, ∑ σ : Finset V, if (c u = k ∧ u ∈ σ) then p σ * a u else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro u _
    unfold Pm
    rw [Finset.sum_filter, Finset.sum_mul]
    by_cases hu : c u = k
    · simp [hu, ite_mul]
    · simp [hu]
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro σ _
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro u _
  by_cases h : u ∈ σ <;> by_cases h' : c u = k <;> simp [h, h']

theorem total_mass {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι) (S : Finset ι)
    (hc : IsRainbow p c S) {k : ι} (hk : k ∈ S) :
    ∑ u ∈ Finset.univ.filter (fun u => c u = k), Pm p u = 1 := by
  have := colour_swap p c k (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  refine Eq.trans (Finset.sum_congr rfl (g := p) ?_) hp.2.2
  intro σ _
  by_cases h0 : p σ = 0
  · simp [h0]
  · rw [Finset.sum_const, card_colour p c S hc h0 hk]; simp

theorem lw_symm {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (u w : V) :
    linkWeight p ∅ u w = linkWeight p ∅ w u := by
  unfold linkWeight
  rw [Finset.insert_comm]
  simp only [Finset.notMem_empty, not_false_eq_true, and_true, ne_comm]

theorem lw_nonneg {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (h0 : ∀ σ, 0 ≤ p σ) (τ : Finset V) (u w : V) : 0 ≤ linkWeight p τ u w := by
  unfold linkWeight
  split_ifs
  · exact Finset.sum_nonneg (fun σ _ => h0 σ)
  · exact le_rfl

theorem col_sum {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (S : Finset ι) (hc : IsRainbow p c S) {k : ι}
    (hk : k ∈ S) (w : V) (hw : c w ≠ k) :
    ∑ u ∈ Finset.univ.filter (fun u => c u = k), linkWeight p ∅ u w = Pm p w := by
  rw [← row_sum p c S hc hk w hw]
  exact Finset.sum_congr rfl (fun u _ => lw_symm p u w)

theorem link_sum {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (v w : V) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => w ∈ σ), linkDist p {v} σ =
      linkWeight p ∅ v w / Pm p v := by
  by_cases hvw : v = w
  · subst hvw
    have : ∀ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), linkDist p {v} σ = 0 := by
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      unfold linkDist
      rw [if_neg]
      rw [Finset.disjoint_singleton_left]; exact not_not.mpr hσ
    rw [Finset.sum_eq_zero this]
    unfold linkWeight; simp
  · unfold linkWeight
    rw [if_pos ⟨hvw, by simp, by simp⟩]
    rw [Finset.sum_div]
    unfold linkDist Pm
    have hP : ∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => {v} ⊆ σ'), p σ' =
        ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ := by
      simp only [Finset.singleton_subset_iff]
    rw [hP]
    generalize (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ) = P
    have e1 : (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => w ∈ σ),
        if Disjoint {v} σ then p ({v} ∪ σ) / P else 0) =
        ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => w ∈ σ ∧ v ∉ σ),
          p (insert v σ) / P := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro σ _
      by_cases h1 : w ∈ σ <;> by_cases h2 : v ∈ σ <;>
        simp [h1, h2, Finset.disjoint_singleton_left]
    rw [e1]
    refine Finset.sum_nbij' (fun σ => insert v σ) (fun σ => σ.erase v) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      simp [Finset.insert_subset_iff, hσ.1]
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff,
        Finset.empty_subset, and_true] at hσ ⊢
      refine ⟨Finset.mem_erase.2 ⟨fun h => hvw h.symm, hσ.2⟩, by simp⟩
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      simp [hσ.2]
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff,
        Finset.empty_subset, and_true] at hσ
      simp [hσ.1]
    · intro σ _; rfl

theorem lw_le_Pm {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (h0 : ∀ σ, 0 ≤ p σ) (u w : V) : linkWeight p ∅ u w ≤ Pm p u := by
  unfold linkWeight Pm
  split_ifs
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff] at hσ ⊢
      exact hσ.1
    · intro σ _ _; exact h0 σ
  · exact Finset.sum_nonneg (fun σ _ => h0 σ)

theorem cm_link {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (f : V → ℝ) (v : V) (j : ι) :
    colourMean (linkDist p {v}) c f j =
      ∑ w ∈ Finset.univ.filter (fun w => c w = j), (linkWeight p ∅ v w / Pm p v) * f w := by
  unfold colourMean
  apply Finset.sum_congr rfl; intro w _
  rw [link_sum]

theorem cm_link_nonneg {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (h0 : ∀ σ, 0 ≤ p σ) (c : V → ι) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v)
    (v : V) (j : ι) : 0 ≤ colourMean (linkDist p {v}) c f j := by
  rw [cm_link]
  exact Finset.sum_nonneg (fun w _ =>
    mul_nonneg (div_nonneg (lw_nonneg p h0 ∅ v w) (Pm_nonneg p h0 v)) (hf w))

theorem part_one {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι) (S : Finset ι)
    (hd : 2 ≤ d) (hc : IsRainbow p c S) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsPartiteHDX p c S lam) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (i : ι)
    (hi : i ∈ S) (hpos : 0 < colourMean p c f i) (j : ι) (hj : j ∈ S) (hji : j ≠ i) :
    ∑ v ∈ Finset.univ.filter (fun v => c v = i),
          ((d : ℝ) * vertexMeasure d p v * f v / colourMean p c f i) *
            colourMean (linkDist p {v}) c f j ≤
        colourMean p c f j + lam * Real.sqrt (colourMean p c f j / colourMean p c f i) := by
  have hd0 : (d : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  set B : V → V → ℝ := fun u w => if c u = i ∧ c w = j then linkWeight p ∅ u w else 0 with hBdef
  have hBs : BipSingLE B lam := hX i hi j hj hji.symm ∅ (by simp)
  have hB0 : ∀ u w, 0 ≤ B u w := by
    intro u w; simp only [hBdef]; split_ifs
    · exact lw_nonneg p hp.1 ∅ u w
    · exact le_rfl
  have hrow : ∀ u, ∑ w, B u w = if c u = i then Pm p u else 0 := by
    intro u
    by_cases hu : c u = i
    · rw [if_pos hu]
      rw [← row_sum p c S hc hj u (by rw [hu]; exact hji.symm), Finset.sum_filter]
      apply Finset.sum_congr rfl; intro w _
      simp [hBdef, hu]
    · rw [if_neg hu]
      apply Finset.sum_eq_zero; intro w _
      simp [hBdef, hu]
  have hcol : ∀ w, ∑ u, B u w = if c w = j then Pm p w else 0 := by
    intro w
    by_cases hw : c w = j
    · rw [if_pos hw]
      rw [← col_sum p c S hc hi w (by rw [hw]; exact hji), Finset.sum_filter]
      apply Finset.sum_congr rfl; intro u _
      simp [hBdef, hw]
    · rw [if_neg hw]
      apply Finset.sum_eq_zero; intro u _
      simp [hBdef, hw]
  have hB1 : ∑ u, ∑ w, B u w = 1 := by
    simp only [hrow]
    rw [← Finset.sum_filter]
    exact total_mass d p hp c S hc hi
  have hμ : colourMean p c f i = ∑ u, (∑ w, B u w) * f u := by
    simp only [hrow, ite_mul, zero_mul]
    rw [← Finset.sum_filter]; rfl
  have hν : colourMean p c f j = ∑ w, (∑ u, B u w) * f w := by
    simp only [hcol, ite_mul, zero_mul]
    rw [← Finset.sum_filter]; rfl
  obtain ⟨h1, h2⟩ := fact_2_1_bipartite B hB0 hB1 lam hlam hBs f f hf hf _ _ hμ hν
  set μi := colourMean p c f i with hμi
  set μj := colourMean p c f j with hμj
  have hμj0 : 0 ≤ μj := Finset.sum_nonneg (fun w _ => mul_nonneg (Pm_nonneg p hp.1 w) (hf w).1)
  have hSB : ∑ u, ∑ w, B u w * f u * f w =
      ∑ v ∈ Finset.univ.filter (fun v => c v = i),
        f v * ∑ w ∈ Finset.univ.filter (fun w => c w = j), linkWeight p ∅ v w * f w := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro u _
    by_cases hu : c u = i
    · simp only [hu, if_true]
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro w _
      by_cases hw : c w = j
      · simp [hBdef, hu, hw]; ring
      · simp [hBdef, hw]
    · simp only [hu, if_false]
      apply Finset.sum_eq_zero; intro w _
      simp [hBdef, hu]
  have hkey : ∑ v ∈ Finset.univ.filter (fun v => c v = i),
          ((d : ℝ) * vertexMeasure d p v * f v / μi) * colourMean (linkDist p {v}) c f j =
        (∑ u, ∑ w, B u w * f u * f w) / μi := by
    rw [hSB, Finset.sum_div]
    apply Finset.sum_congr rfl; intro v _
    have hdv : (d : ℝ) * vertexMeasure d p v = Pm p v := by
      unfold vertexMeasure Pm; field_simp
    rw [hdv, cm_link]
    by_cases hP : Pm p v = 0
    · have : ∀ w, linkWeight p ∅ v w = 0 := fun w =>
        le_antisymm (hP ▸ lw_le_Pm p hp.1 v w) (lw_nonneg p hp.1 ∅ v w)
      simp [this, hP]
    · have e : ∑ w ∈ Finset.univ.filter (fun w => c w = j), (linkWeight p ∅ v w / Pm p v) * f w =
          (∑ w ∈ Finset.univ.filter (fun w => c w = j), linkWeight p ∅ v w * f w) / Pm p v := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      rw [e]
      field_simp
  rw [hkey]
  have hSB' : ∑ u, ∑ w, B u w * f u * f w ≤ μi * μj + lam * Real.sqrt (μi * μj) := by
    have := (abs_le.1 h1).2
    linarith
  rw [div_le_iff₀ hpos]
  have hsq : Real.sqrt (μi * μj) = μi * Real.sqrt (μj / μi) := by
    have : μi * μj = μi ^ 2 * (μj / μi) := by field_simp
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
  rw [hsq] at hSB'
  nlinarith [hSB']

theorem cPoly_nonneg' {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : ι → ℝ) (hx : ∀ j ∈ S, 0 ≤ x j) : 0 ≤ cPoly S lam x := by
  unfold cPoly
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg; intro k hk
  apply mul_nonneg (hx k hk)
  apply Finset.prod_nonneg; intro j hj
  have := hx j (Finset.mem_of_mem_erase hj)
  have : (0 : ℝ) ≤ S.card * lam := by positivity
  linarith

end HDXHitting.Dev.PGV
namespace HDXHitting
open HDXHitting.Dev.PGV in
theorem chk_partite_good_vertex {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι) (S : Finset ι)
    (hS : S.card = d) (hd : 2 ≤ d) (hc : IsRainbow p c S) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsPartiteHDX p c S lam) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (i : ι)
    (hi : i ∈ S) (hmax : ∀ j ∈ S, colourMean p c f j ≤ colourMean p c f i)
    (hpos : 0 < colourMean p c f i) :
    (∀ j ∈ S.erase i,
      ∑ v ∈ Finset.univ.filter (fun v => c v = i),
          ((d : ℝ) * vertexMeasure d p v * f v / colourMean p c f i) *
            colourMean (linkDist p {v}) c f j ≤
        colourMean p c f j + lam * Real.sqrt (colourMean p c f j / colourMean p c f i) ∧
      colourMean p c f j + lam * Real.sqrt (colourMean p c f j / colourMean p c f i) ≤
        colourMean p c f j + lam) ∧
    ∃ v, c v = i ∧ 0 < f v ∧ 0 < vertexMeasure d p v ∧
      cPoly (S.erase i) lam (colourMean (linkDist p {v}) c f) ≤
        cPoly (S.erase i) lam (fun j => colourMean p c f j + lam) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP1 : ∀ j ∈ S.erase i,
      ∑ v ∈ Finset.univ.filter (fun v => c v = i),
          ((d : ℝ) * vertexMeasure d p v * f v / colourMean p c f i) *
            colourMean (linkDist p {v}) c f j ≤
        colourMean p c f j + lam * Real.sqrt (colourMean p c f j / colourMean p c f i) := by
    intro j hj
    exact part_one d p hp c S hd hc lam hlam hX f hf i hi hpos j (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj)
  have hP2 : ∀ j ∈ S.erase i, colourMean p c f j + lam *
      Real.sqrt (colourMean p c f j / colourMean p c f i) ≤ colourMean p c f j + lam := by
    intro j hj
    have : Real.sqrt (colourMean p c f j / colourMean p c f i) ≤ 1 :=
      Real.sqrt_le_one.mpr ((div_le_one hpos).2 (hmax j (Finset.mem_of_mem_erase hj)))
    nlinarith
  refine ⟨fun j hj => ⟨hP1 j hj, hP2 j hj⟩, ?_⟩
  set μi := colourMean p c f i with hμi
  set S' := S.erase i with hS'
  set a : V → ℝ := fun v => (d : ℝ) * vertexMeasure d p v * f v / μi with ha
  set m : V → ι → ℝ := fun v => colourMean (linkDist p {v}) c f with hm
  have hdv : ∀ v, (d : ℝ) * vertexMeasure d p v = Pm p v := by
    intro v; unfold vertexMeasure Pm; field_simp
  have hvm0 : ∀ v, 0 ≤ vertexMeasure d p v := by
    intro v; unfold vertexMeasure
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun σ _ => hp.1 σ))
  have ha0 : ∀ v, 0 ≤ a v := by
    intro v; simp only [ha]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (hvm0 v)) (hf v).1) hpos.le
  have hasum : ∑ v ∈ Finset.univ.filter (fun v => c v = i), a v = 1 := by
    have : ∀ v, a v = Pm p v * f v / μi := by intro v; simp only [ha]; rw [hdv]
    simp only [this]
    rw [← Finset.sum_div]
    exact div_self hpos.ne'
  set T := Finset.univ.filter (fun v => c v = i ∧ a v ≠ 0) with hT
  have hTsum : ∀ g : V → ℝ, ∑ v ∈ T, a v * g v =
      ∑ v ∈ Finset.univ.filter (fun v => c v = i), a v * g v := by
    intro g
    apply Finset.sum_subset
    · intro v hv; simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hv.1
    · intro v hv hvT
      have : a v = 0 := by
        by_contra hne
        apply hvT
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨hv, hne⟩
      simp [this]
  have hTa : ∑ v ∈ T, a v = 1 := by
    have := hTsum (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; exact hasum
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hTa; simp at hTa
  obtain ⟨v0, hv0T, hv0min⟩ := Finset.exists_min_image T (fun v => cPoly S' lam (m v)) hTne
  have hm0 : ∀ v, ∀ j, 0 ≤ m v j := fun v j => cm_link_nonneg p hp.1 c f (fun w => (hf w).1) v j
  set mm := cPoly S' lam (m v0) with hmm
  have hmm0 : 0 ≤ mm := cPoly_nonneg' S' lam hlam _ (fun j _ => hm0 v0 j)
  obtain ⟨hmono, hlogc, -⟩ := cpoly_monotone_log_concave S' lam hlam
  set C : Set (ι → ℝ) := {x | (∀ j ∈ S', 0 ≤ x j) ∧ mm ≤ cPoly S' lam x} with hC
  have hconv : Convex ℝ C := by
    intro x hx y hy t u ht hu htu
    have hu' : u = 1 - t := by linarith
    subst hu'
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ht (hx.1 j hj)) (mul_nonneg hu (hy.1 j hj))
    · have hl := hlogc x y hx.1 hy.1 t ht (by linarith)
      calc mm = mm ^ t * mm ^ (1 - t) := by
            rw [← Real.rpow_add' hmm0 (by linarith)]; simp
        _ ≤ cPoly S' lam x ^ t * cPoly S' lam y ^ (1 - t) :=
            mul_le_mul (Real.rpow_le_rpow hmm0 hx.2 ht) (Real.rpow_le_rpow hmm0 hy.2 hu)
              (Real.rpow_nonneg hmm0 _) (Real.rpow_nonneg (le_trans hmm0 hx.2) _)
        _ ≤ _ := hl
  have hmem : (∑ v ∈ T, a v • m v) ∈ C := by
    refine hconv.sum_mem (fun v _ => ha0 v) hTa (fun v hv => ⟨fun j _ => hm0 v j, ?_⟩)
    exact hv0min v hv
  have hbar : ∀ j ∈ S', (∑ v ∈ T, a v • m v) j ≤ colourMean p c f j + lam := by
    intro j hj
    have e : (∑ v ∈ T, a v • m v) j = ∑ v ∈ T, a v * m v j := by
      simp [Finset.sum_apply]
    rw [e, hTsum (fun v => m v j)]
    exact (hP1 j hj).trans (hP2 j hj)
  have hfin : cPoly S' lam (∑ v ∈ T, a v • m v) ≤ cPoly S' lam (fun j => colourMean p c f j + lam) := by
    apply hmono _ _ hmem.1 hbar
  refine ⟨v0, ?_, ?_, ?_, le_trans hmem.2 hfin⟩
  all_goals
    have hv0 := hv0T
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hv0
  · exact hv0.1
  · rcases (hf v0).1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hv0.2; simp only [ha]; rw [← h]; simp
  · rcases (hvm0 v0).lt_or_eq with h | h
    · exact h
    · exfalso; apply hv0.2; simp only [ha]; rw [← h]; simp

end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_partite_good_vertex := @HDXHitting.chk_partite_good_vertex
