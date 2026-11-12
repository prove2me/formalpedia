-- Prove2me | solution 1 for HDXConc.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:09.510906+00:00
-- url     : https://prove2.me/submissions/cd8a5787-97f7-43fa-9445-cf96eb325db8

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_tilt
import Theorems.Thm_HDXConc_lemma_3_3
import Theorems.Thm_HDXConc_theorem_2_3

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace HDXConc.Dev.C32
open HDXConc

variable {V : Type*} [Fintype V] [DecidableEq V]

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

lemma mem_faces {d : ℕ} {X : Finset (Finset V)} {t : Finset V} :
    t ∈ SteurerHDX.faces X d ↔ t ∈ X ∧ t.card = d := by
  simp [SteurerHDX.faces]

lemma linkWeight_eq {d : ℕ} {X : Finset (Finset V)} (ρ : Finset V → ℝ) {s : Finset V}
    (hs : s.card + 2 = d) {u v : V} (huv : u ≠ v) (hu : u ∉ s) (hv : v ∉ s) :
    linkWeight X d ρ s u v = if s ∪ {u, v} ∈ X then ρ (s ∪ {u, v}) else 0 := by
  have hcard : (s ∪ {u, v}).card = d := by
    rw [Finset.card_union_of_disjoint, Finset.card_pair huv]
    · omega
    · simp [Finset.disjoint_left, hu, hv]; grind
  unfold linkWeight
  rw [if_pos ⟨huv, hu, hv⟩]
  split_ifs with h
  · have : (SteurerHDX.faces X d).filter (fun t => s ∪ {u, v} ⊆ t) = {s ∪ {u, v}} := by
      ext t
      simp only [Finset.mem_filter, mem_faces, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, ht⟩, hsub⟩
        exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      · rintro rfl; exact ⟨⟨h, hcard⟩, subset_rfl⟩
    rw [this, Finset.sum_singleton]
  · apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, mem_faces] at ht
    exfalso; apply h
    have := Finset.eq_of_subset_of_card_le ht.2 (by omega)
    rw [this]; exact ht.1.1

lemma tilt_density {d : ℕ} {X : Finset (Finset V)} {π : Finset V → ℝ} (hπ : IsTopDensity X d π)
    (f : V → ℝ) (t : ℝ) :
    IsTopDensity X d (tilt X d π f t) ∧
      0 < ∑ σ' ∈ SteurerHDX.faces X d, π σ' * Real.exp (t * topSum f σ') := by
  have hZ : 0 < ∑ σ' ∈ SteurerHDX.faces X d, π σ' * Real.exp (t * topSum f σ') := by
    have hne : (SteurerHDX.faces X d).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have := hπ.sum_eq_one; rw [h] at this; simp at this
    exact Finset.sum_pos (fun σ hσ => mul_pos (hπ.pos σ hσ) (Real.exp_pos _)) hne
  refine ⟨⟨fun σ hσ => ?_, ?_⟩, hZ⟩
  · unfold tilt; exact div_pos (mul_pos (hπ.pos σ hσ) (Real.exp_pos _)) hZ
  · unfold tilt
    rw [← Finset.sum_div, div_self hZ.ne']

lemma secondEigLE_congr (W : Finset V) {w w' : V → V → ℝ} {lam : ℝ}
    (h : ∀ u ∈ W, ∀ v ∈ W, w u v = w' u v) (hS : SecondEigLE W w lam) : SecondEigLE W w' lam := by
  have hd : ∀ v ∈ W, weightedDeg W w v = weightedDeg W w' v := fun v hv =>
    Finset.sum_congr rfl (fun u hu => h v hv u hu)
  intro g hg
  have hg' : ∑ v ∈ W, weightedDeg W w v * g v = 0 := by
    rw [← hg]; exact Finset.sum_congr rfl (fun v hv => by rw [hd v hv])
  have := hS g hg'
  have e1 : ∑ u ∈ W, ∑ v ∈ W, w u v * g u * g v = ∑ u ∈ W, ∑ v ∈ W, w' u v * g u * g v :=
    Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => by rw [h u hu v hv]))
  have e2 : ∑ v ∈ W, weightedDeg W w v * g v ^ 2 = ∑ v ∈ W, weightedDeg W w' v * g v ^ 2 :=
    Finset.sum_congr rfl (fun v hv => by rw [hd v hv])
  rw [← e1, ← e2]; exact this

lemma secondEigLE_mono (W : Finset V) {w : V → V → ℝ} {lam lam' : ℝ}
    (hdeg : ∀ v ∈ W, 0 ≤ weightedDeg W w v) (hle : lam ≤ lam') (hS : SecondEigLE W w lam) :
    SecondEigLE W w lam' := by
  intro g hg
  refine (hS g hg).trans ?_
  apply mul_le_mul_of_nonneg_right hle
  exact Finset.sum_nonneg (fun v hv => mul_nonneg (hdeg v hv) (sq_nonneg _))

section link
variable {d : ℕ} (hd : 2 ≤ d) {η : ℝ} {X : Finset (Finset V)} {π : Finset V → ℝ}

lemma link_nbr (hX : SteurerHDX.IsPure X d) {s : Finset V} (hs : s ∈ X) (hcs : s.card + 2 = d)
    {v : V} (hv : v ∈ linkVerts X s) :
    ∃ u ∈ linkVerts X s, u ≠ v ∧ s ∪ {u, v} ∈ X := by
  simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨t, ht, hsub⟩ := exists_facet hX hv.2
  rw [mem_faces] at ht
  have hc : (t \ insert v s).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, ht.2, Finset.card_insert_of_notMem hv.1]; omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc
  have hu' : u ∈ t \ insert v s := by rw [hu]; simp
  rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hu'
  have hsub2 : s ∪ {u, v} ⊆ t := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | rfl | rfl
    · exact hsub (by simp [hx])
    · exact hu'.1
    · exact hsub (by simp)
  have hmem : s ∪ {u, v} ∈ X := hX.1 t ht.1 _ hsub2
  refine ⟨u, ?_, hu'.2.1, hmem⟩
  simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hu'.2.2, hX.1 t ht.1 _ ?_⟩
  intro x hx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hu'.1
  · exact hsub (by simp [hx])

lemma link_nonempty (hX : SteurerHDX.IsPure X d) {s : Finset V} (hs : s ∈ X) (hcs : s.card + 2 = d) :
    (linkVerts X s).Nonempty := by
  obtain ⟨t, ht, hsub⟩ := exists_facet hX hs
  rw [mem_faces] at ht
  have hc : 0 < (t \ s).card := by
    rw [Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hc
  rw [Finset.mem_sdiff] at hv
  refine ⟨v, ?_⟩
  simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hv.2, hX.1 t ht.1 _ ?_⟩
  intro x hx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hv.1
  · exact hsub hx

lemma link_basic (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π) {s : Finset V} (hs : s ∈ X)
    (hcs : s.card + 2 = d) :
    (∀ u ∈ linkVerts X s, ∀ v ∈ linkVerts X s,
        linkWeight X d π s u v = linkWeight X d π s v u) ∧
    (∀ u ∈ linkVerts X s, ∀ v ∈ linkVerts X s, 0 ≤ linkWeight X d π s u v) ∧
    (∀ v ∈ linkVerts X s, 0 < weightedDeg (linkVerts X s) (linkWeight X d π s) v) := by
  have hnn : ∀ u v, 0 ≤ linkWeight X d π s u v := by
    intro u v
    unfold linkWeight
    split_ifs
    · exact Finset.sum_nonneg (fun t ht => by
        rw [Finset.mem_filter] at ht; exact (hπ.pos t ht.1).le)
    · exact le_rfl
  refine ⟨?_, fun u _ v _ => hnn u v, ?_⟩
  · intro u _ v _
    unfold linkWeight
    rw [Finset.pair_comm, eq_comm]
    simp only [ne_comm, and_comm, and_left_comm]
  · intro v hv
    obtain ⟨u, hu, huv, hmem⟩ := link_nbr hX hs hcs hv
    have hv' := hv
    have hu' := hu
    simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv' hu'
    have hcard : (s ∪ {u, v}).card = d := by
      rw [Finset.card_union_of_disjoint, Finset.card_pair huv]
      · omega
      · rw [Finset.disjoint_left]; intro x hx hx2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
        rcases hx2 with rfl | rfl
        · exact hu'.1 hx
        · exact hv'.1 hx
    have hpos : 0 < linkWeight X d π s v u := by
      rw [linkWeight_eq π hcs huv.symm hv'.1 hu'.1, Finset.pair_comm, if_pos hmem]
      exact hπ.pos _ (mem_faces.2 ⟨hmem, hcard⟩)
    unfold weightedDeg
    calc 0 < linkWeight X d π s v u := hpos
      _ ≤ _ := Finset.single_le_sum (f := fun u => linkWeight X d π s v u)
            (fun u _ => hnn v u) hu


lemma link_tilt (hd : 2 ≤ d) (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π) {η : ℝ}
    (hη : 0 < η)
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {t : ℝ} (ht : |t| ≤ η / 2)
    {s : Finset V} (hs : s ∈ X) (hcs : s.card + 2 = d)
    (hS : SecondEigLE (linkVerts X s) (linkWeight X d π s) ((1 - η) / ((d : ℝ) - 1)))
    (hη1 : η ≤ 1) :
    SecondEigLE (linkVerts X s) (linkWeight X d (tilt X d π f t) s)
      (Real.exp (η / 2) * ((1 - η) / ((d : ℝ) - 1))) := by
  obtain ⟨hZ0, hZ⟩ := tilt_density hπ f t
  set Z := ∑ σ' ∈ SteurerHDX.faces X d, π σ' * Real.exp (t * topSum f σ') with hZdef
  obtain ⟨hsymm, hnn, hdeg⟩ := link_basic hX hπ hs hcs
  have hW := link_nonempty hX hs hcs
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlam0 : 0 ≤ (1 - η) / ((d : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
  set K := Real.exp (t * topSum f s) / Z with hK
  have hKpos : 0 < K := div_pos (Real.exp_pos _) hZ
  set g : V → ℝ := fun u => Real.sqrt K * Real.exp (t * f u) with hg
  have hgpos : ∀ v ∈ linkVerts X s, 0 < g v := fun v _ =>
    mul_pos (Real.sqrt_pos.2 hKpos) (Real.exp_pos _)
  have h33 := lemma_3_3 (linkVerts X s) hW (linkWeight X d π s) _ hlam0 hsymm hnn hdeg g hgpos hS
  have hcongr : ∀ u ∈ linkVerts X s, ∀ v ∈ linkVerts X s,
      linkWeight X d π s u v * g u * g v = linkWeight X d (tilt X d π f t) s u v := by
    intro u hu v hv
    have hu' := hu
    have hv' := hv
    simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hu' hv'
    by_cases huv : u = v
    · subst huv; simp [linkWeight]
    · rw [linkWeight_eq π hcs huv hu'.1 hv'.1, linkWeight_eq _ hcs huv hu'.1 hv'.1]
      split_ifs with hm
      · have hsum : topSum f (s ∪ {u, v}) = topSum f s + f u + f v := by
          unfold topSum
          rw [Finset.sum_union, Finset.sum_pair huv]
          · ring
          · rw [Finset.disjoint_left]; intro x hx hx2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
            rcases hx2 with rfl | rfl
            · exact hu'.1 hx
            · exact hv'.1 hx
        unfold tilt
        rw [hsum]
        have e : Real.exp (t * (topSum f s + f u + f v)) =
            Real.exp (t * topSum f s) * Real.exp (t * f u) * Real.exp (t * f v) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        have hsq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hKpos.le
        simp only [hg]
        rw [e, hK] at *
        rw [show π (s ∪ {u, v}) * (Real.sqrt (Real.exp (t * topSum f s) / Z) * Real.exp (t * f u)) *
            (Real.sqrt (Real.exp (t * topSum f s) / Z) * Real.exp (t * f v)) =
            π (s ∪ {u, v}) * (Real.sqrt (Real.exp (t * topSum f s) / Z) *
              Real.sqrt (Real.exp (t * topSum f s) / Z)) * Real.exp (t * f u) * Real.exp (t * f v)
          by ring, hsq]
        rw [← hZdef]
        field_simp
      · simp
  have hnnρ : ∀ v ∈ linkVerts X s, 0 ≤ weightedDeg (linkVerts X s)
      (linkWeight X d (tilt X d π f t) s) v := by
    intro v hv
    refine Finset.sum_nonneg (fun u hu => ?_)
    rw [← hcongr v hv u hu]
    have := hgpos v hv; have := hgpos u hu; have := hnn v hv u hu
    positivity
  have hS' := secondEigLE_congr _ (fun u hu v hv => hcongr u hu v hv) h33
  refine secondEigLE_mono _ hnnρ ?_ hS'
  -- ratio bound
  have hB : (linkVerts X s).sup' hW g / (linkVerts X s).inf' hW g ≤ Real.exp (η / 2) := by
    obtain ⟨v0, hv0, hv0e⟩ := Finset.exists_mem_eq_inf' hW g
    have hpos0 := hgpos v0 hv0
    rw [div_le_iff₀ (by rw [hv0e]; exact hpos0), hv0e]
    apply Finset.sup'_le
    intro u hu
    have hfu := hf u (by
      have := hu; simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hX.1 _ this.2 _ (by intro x hx; simp at hx; simp [hx]))
    have hfv := hf v0 (by
      have := hv0; simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hX.1 _ this.2 _ (by intro x hx; simp at hx; simp [hx]))
    simp only [hg]
    have : t * f u ≤ η / 2 + t * f v0 := by
      have h1 : t * (f u - f v0) ≤ |t * (f u - f v0)| := le_abs_self _
      rw [abs_mul] at h1
      have h2 : |f u - f v0| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hfu.1, hfu.2, hfv.1, hfv.2]
      have h3 : |t| * |f u - f v0| ≤ |t| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      nlinarith
    calc Real.sqrt K * Real.exp (t * f u) ≤ Real.sqrt K * Real.exp (η / 2 + t * f v0) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.exp_add]; ring
  exact mul_le_mul_of_nonneg_right hB hlam0

end link
end HDXConc.Dev.C32
namespace HDXConc
open HDXConc.Dev.C32 in
theorem chk_claim_3_2 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {t : ℝ} (ht : |t| ≤ η / 2) :
    SecondEigLE (linkVerts X ∅) (linkWeight X d (tilt X d π f t) ∅) ((2 / η - 1) / ((d : ℝ) - 1)) := by
  obtain ⟨hρ, hZ⟩ := tilt_density hπ f t
  have hn : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set n : ℝ := (d : ℝ) - 1 with hndef
  have hn0 : 0 < n := by linarith
  set E := Real.exp (η / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E * (1 - η / 2) ≤ 1 := by
    have h := Real.add_one_le_exp (-(η / 2))
    have : E * Real.exp (-(η / 2)) = 1 := by
      rw [hE, ← Real.exp_add]; simp
    nlinarith
  set δ := E * ((1 - η) / n) with hδ
  have hδn : δ * n = E * (1 - η) := by rw [hδ]; field_simp
  have hδpos : 0 ≤ δ := by rw [hδ]; exact mul_nonneg hE0.le (div_nonneg (by linarith) hn0.le)
  have ha1 : E * (1 - η) < 1 := by nlinarith
  have hδlt : δ < 1 / n := by
    rw [lt_div_iff₀ hn0]; linarith
  have hd2 : (d : ℝ) - 2 = n - 1 := by rw [hndef]; ring
  have hlink : ∀ s ∈ X, s.card + 2 = d → SecondEigLE (linkVerts X s) (linkWeight X d (tilt X d π f t) s) δ := by
    intro s hs hcs
    exact link_tilt hd hX hπ hη0 f hf ht hs hcs (hexp.link_le s hs hcs) hη1
  have h23 := theorem_2_3 hd hX hρ hexp.connected hδlt hlink ∅
    (by
      obtain ⟨t', ht', _⟩ := exists_facet hX (σ := ∅) (by
        by_contra h
        have := hπ.sum_eq_one
        have hne : (SteurerHDX.faces X d).Nonempty := by
          by_contra h'
          rw [Finset.not_nonempty_iff_eq_empty] at h'
          rw [h'] at this; simp at this
        obtain ⟨u, hu⟩ := hne
        rw [mem_faces] at hu
        exact h (hX.1 u hu.1 ∅ (Finset.empty_subset _)))
      exact hX.1 t' (mem_faces.1 ht').1 ∅ (Finset.empty_subset _))
    (by simp [hd])
  refine secondEigLE_mono _ ?_ ?_ h23
  · intro v _
    refine Finset.sum_nonneg (fun u _ => ?_)
    unfold linkWeight
    split_ifs
    · exact Finset.sum_nonneg (fun t ht => by
        rw [Finset.mem_filter] at ht; exact (hρ.pos t ht.1).le)
    · exact le_rfl
  · rw [hd2]
    have hK : 2 / η - 1 = (2 - η) / η := by field_simp
    have hden : 0 < 1 - (n - 1) * δ := by nlinarith
    rw [hK, div_le_div_iff₀ hden hn0, div_mul_eq_mul_div, le_div_iff₀ hη0]
    -- key inequality
    have hb : E * (1 - η) * (2 - η) ≤ 2 - 2 * η := by
      have : E * (2 - η) ≤ 2 := by nlinarith
      nlinarith
    have hG : (2 - η) * (E * (1 - η) * (η * n + (2 - η) * (n - 1))) ≤ (2 - η) * ((2 - η) * n) := by
      have hB : 0 ≤ η * n + (2 - η) * (n - 1) := by nlinarith
      calc (2 - η) * (E * (1 - η) * (η * n + (2 - η) * (n - 1)))
          = (E * (1 - η) * (2 - η)) * (η * n + (2 - η) * (n - 1)) := by ring
        _ ≤ (2 - 2 * η) * (η * n + (2 - η) * (n - 1)) := mul_le_mul_of_nonneg_right hb hB
        _ ≤ (2 - η) * ((2 - η) * n) := by nlinarith [mul_nonneg (sq_nonneg η) hn0.le, mul_nonneg (sub_nonneg.2 hη1) (by linarith : (0:ℝ) ≤ 2 - η)]
    have hG' : E * (1 - η) * (η * n + (2 - η) * (n - 1)) ≤ (2 - η) * n :=
      le_of_mul_le_mul_left hG (by linarith)
    have : δ * n * (η * n + (2 - η) * (n - 1)) ≤ (2 - η) * n := by rw [hδn]; exact hG'
    have : δ * (η * n + (2 - η) * (n - 1)) ≤ (2 - η) := by
      by_contra hc; rw [not_le] at hc
      nlinarith
    nlinarith
end HDXConc
end

theorem solution : type_of% @HDXConc.chk_claim_3_2 := @HDXConc.chk_claim_3_2
