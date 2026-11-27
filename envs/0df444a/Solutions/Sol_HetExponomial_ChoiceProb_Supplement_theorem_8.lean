-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:23.879817+00:00
-- url     : https://prove2.me/submissions/3f59ce2f-90bc-4f5c-9837-b6fe9aa06acc

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (l : Fin n) (p : Fin n → ℝ)
    (hp : IsOptimalMonopolyPrice α β lam l p) :
    (∀ i j, i ≠ l → j ≠ l → α i ≤ α j → p i ≤ p j ∧ util α β p i ≤ util α β p j) ∧
      ((∀ i j, i ≠ l → j ≠ l → i ≠ j → α i ≠ α j) →
        ∃ B : Finset (Fin n), l ∉ B ∧
          (∀ i ∈ B, ∀ j, j ≠ l → j ∉ B → α i < α j) ∧
          (∀ i ∈ B, util α β p i ≤ α l) ∧
          (∀ j, j ≠ l → j ∉ B → α l ≤ util α β p j) ∧
          (∀ i ∈ B, ∀ j ∈ B, p i = p j) ∧
          (∀ i j, i ≠ l → j ≠ l → i ∉ B → j ∉ B → α i < α j → p i < p j) ∧
          (∀ i ∈ B, ∀ j, j ≠ l → j ∉ B → p i < p j)) := by
            have alg : ∀ (Ψ : ℝ → ℝ), p l = 0 → (∀ x, 0 < Ψ x) → StrictMono Ψ →
                (∀ i, i ≠ l → ∑ k, lam k * (p i - p k) * min (Ψ (util α β p k)) (Ψ (util α β p i))
                  = Ψ (util α β p i) / β) →
                (0 < ∑ k, lam k * p k * Ψ (util α β p k)) →
                ((∀ i j, i ≠ l → j ≠ l → α i ≤ α j → p i ≤ p j ∧ util α β p i ≤ util α β p j) ∧
                ((∀ i j, i ≠ l → j ≠ l → i ≠ j → α i ≠ α j) →
                  ∃ B : Finset (Fin n), l ∉ B ∧
                    (∀ i ∈ B, ∀ j, j ≠ l → j ∉ B → α i < α j) ∧
                    (∀ i ∈ B, util α β p i ≤ α l) ∧
                    (∀ j, j ≠ l → j ∉ B → α l ≤ util α β p j) ∧
                    (∀ i ∈ B, ∀ j ∈ B, p i = p j) ∧
                    (∀ i j, i ≠ l → j ≠ l → i ∉ B → j ∉ B → α i < α j → p i < p j) ∧
                    (∀ i ∈ B, ∀ j, j ≠ l → j ∉ B → p i < p j))) := by
              intro Ψ hpl hΨpos hΨmono hFOC hRpos
              set u := util α β p with hu
              have hul : u l = α l := by simp [hu, util, hpl]
              have hα : ∀ k, α k = u k + β * p k := by intro k; simp [hu, util]
              set ψ : Fin n → ℝ := fun k => Ψ (u k) with hψdef
              have hψpos : ∀ k, 0 < ψ k := fun k => hΨpos _
              have hψiff : ∀ a b, ψ a < ψ b ↔ u a < u b := fun a b => hΨmono.lt_iff_lt
              have hψeq : ∀ a b, ψ a = ψ b ↔ u a = u b := fun a b => hΨmono.injective.eq_iff
              have hFOC' : ∀ i, i ≠ l → ∑ k, lam k * (p i - p k) * min (ψ k) (ψ i) = ψ i / β := hFOC
              clear_value ψ
              clear hFOC
              set L := ∑ k, lam k with hL
              set S := ∑ k, lam k * p k with hS
              have hLpos : 0 < L := by
                have : (Finset.univ : Finset (Fin n)).Nonempty := ⟨l, Finset.mem_univ _⟩
                exact Finset.sum_pos (fun k _ => hlam k) this
              set c := (1 / β + S) / L with hc
              have hcL : c * L - S = 1 / β := by
                rw [hc]; field_simp; ring
              set M : Fin n → ℝ := fun j => ∑ k, lam k * min (ψ k) (ψ j) with hM
              have hMpos : ∀ j, 0 < M j := by
                intro j
                have : (Finset.univ : Finset (Fin n)).Nonempty := ⟨l, Finset.mem_univ _⟩
                exact Finset.sum_pos (fun k _ => mul_pos (hlam k) (lt_min (hψpos k) (hψpos j))) this
              -- reference identity with c
              have hrefc : ∀ j, j ≠ l → M j * (p j - c) =
                  ∑ k, lam k * (c - p k) * (ψ j - min (ψ k) (ψ j)) := by
                intro j hj
                have h1 := hFOC' j hj
                have e : ∑ k, lam k * (c - p k) * (ψ j - min (ψ k) (ψ j)) =
                    ψ j * (c * L - S) - ∑ k, lam k * (p j - p k) * min (ψ k) (ψ j)
                      - (c - p j) * M j := by
                  simp only [hM, hL, hS, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun k _ => ?_
                  ring
                rw [e, h1, hcL]; ring
              have hrefi : ∀ i j, i ≠ l → j ≠ l → (ψ i * M j) * (p j - p i) =
                  ∑ k, lam k * (p i - p k) * (ψ j * min (ψ k) (ψ i) - ψ i * min (ψ k) (ψ j)) := by
                intro i j hi hj
                have h1 := hFOC' i hi
                have h2 := hFOC' j hj
                have e : ∑ k, lam k * (p i - p k) * (ψ j * min (ψ k) (ψ i) - ψ i * min (ψ k) (ψ j)) =
                    ψ j * ∑ k, lam k * (p i - p k) * min (ψ k) (ψ i)
                      - ψ i * ((p i - p j) * M j + ∑ k, lam k * (p j - p k) * min (ψ k) (ψ j)) := by
                  simp only [hM, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun k _ => ?_
                  ring
                rw [e, h1, h2]; field_simp; ring
              -- sign lemma
              have hsign : ∀ j, j ≠ l → ∀ r, (r = c ∨ ∃ i, i ≠ l ∧ ψ i < ψ j ∧ p i = r) →
                  ∃ C > 0, ∃ w : Fin n → ℝ, (∀ k, 0 ≤ w k) ∧ (∀ k, ¬ ψ k < ψ j → w k = 0) ∧
                    (ψ l < ψ j → 0 < w l) ∧ C * (p j - r) = ∑ k, lam k * (r - p k) * w k := by
                intro j hj r hr
                rcases hr with rfl | ⟨i, hi, hij, rfl⟩
                · refine ⟨M j, hMpos j, fun k => ψ j - min (ψ k) (ψ j), fun k => ?_, fun k hk => ?_,
                    fun h => ?_, hrefc j hj⟩
                  · simp only; linarith [min_le_right (ψ k) (ψ j)]
                  · simp only; rw [min_eq_right (not_lt.1 hk)]; ring
                  · simp only; rw [min_eq_left h.le]; linarith
                · refine ⟨ψ i * M j, mul_pos (hψpos i) (hMpos j),
                    fun k => ψ j * min (ψ k) (ψ i) - ψ i * min (ψ k) (ψ j), fun k => ?_, fun k hk => ?_,
                    fun h => ?_, hrefi i j hi hj⟩
                  · simp only
                    have := hψpos i; have := hψpos j; have := hψpos k
                    rcases le_total (ψ k) (ψ i) with h1 | h1
                    · rw [min_eq_left h1, min_eq_left (h1.trans hij.le)]; nlinarith
                    · rw [min_eq_right h1]
                      rcases le_total (ψ k) (ψ j) with h2 | h2
                      · rw [min_eq_left h2]; nlinarith
                      · rw [min_eq_right h2]; nlinarith
                  · simp only
                    rw [min_eq_right (not_lt.1 hk), min_eq_right (hij.le.trans (not_lt.1 hk))]; ring
                  · simp only
                    have := hψpos i; have := hψpos j; have := hψpos l
                    rcases le_total (ψ l) (ψ i) with h1 | h1
                    · rw [min_eq_left h1, min_eq_left h.le]; nlinarith
                    · rw [min_eq_right h1, min_eq_left h.le]; nlinarith
              have hge : ∀ j, j ≠ l → ∀ r, (r = c ∨ ∃ i, i ≠ l ∧ ψ i < ψ j ∧ p i = r) →
                  (∀ k, ψ k < ψ j → p k ≤ r) → r ≤ p j := by
                intro j hj r hr hk
                obtain ⟨C, hC, w, hw0, hwz, -, he⟩ := hsign j hj r hr
                have : 0 ≤ ∑ k, lam k * (r - p k) * w k := by
                  apply Finset.sum_nonneg; intro k _
                  by_cases h : ψ k < ψ j
                  · exact mul_nonneg (mul_nonneg (hlam k).le (by linarith [hk k h])) (hw0 k)
                  · rw [hwz k h]; simp
                rw [← he] at this
                by_contra hcon
                have : C * (p j - r) < 0 := mul_neg_of_pos_of_neg hC (by linarith)
                linarith
              have hgt : ∀ j, j ≠ l → ∀ r, (r = c ∨ ∃ i, i ≠ l ∧ ψ i < ψ j ∧ p i = r) →
                  (∀ k, ψ k < ψ j → p k ≤ r) → ψ l < ψ j → 0 < r → r < p j := by
                intro j hj r hr hk hlj hr0
                obtain ⟨C, hC, w, hw0, hwz, hwl, he⟩ := hsign j hj r hr
                have : 0 < ∑ k, lam k * (r - p k) * w k := by
                  apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun k => lam k * (r - p k) * w k)
                    (fun k _ => ?_) (Finset.mem_univ l))
                  · rw [hpl]; exact mul_pos (mul_pos (hlam l) (by linarith)) (hwl hlj)
                  · by_cases h : ψ k < ψ j
                    · exact mul_nonneg (mul_nonneg (hlam k).le (by linarith [hk k h])) (hw0 k)
                    · rw [hwz k h]; simp
                rw [← he] at this
                by_contra hcon
                have : C * (p j - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC.le (by linarith)
                linarith
              have hle : ∀ j, j ≠ l → ∀ r, (r = c ∨ ∃ i, i ≠ l ∧ ψ i < ψ j ∧ p i = r) →
                  (∀ k, ψ k < ψ j → r ≤ p k) → p j ≤ r := by
                intro j hj r hr hk
                obtain ⟨C, hC, w, hw0, hwz, -, he⟩ := hsign j hj r hr
                have : ∑ k, lam k * (r - p k) * w k ≤ 0 := by
                  apply Finset.sum_nonpos; intro k _
                  by_cases h : ψ k < ψ j
                  · exact mul_nonpos_of_nonpos_of_nonneg
                      (mul_nonpos_of_nonneg_of_nonpos (hlam k).le (by linarith [hk k h])) (hw0 k)
                  · rw [hwz k h]; simp
                rw [← he] at this
                by_contra hcon
                have : 0 < C * (p j - r) := mul_pos hC (by linarith)
                linarith
              -- the reference set
              set refs : Fin n → Finset ℝ := fun j =>
                insert c ((Finset.univ.filter (fun i => i ≠ l ∧ ψ i < ψ j)).image p) with hrefs
              have hrefs_ne : ∀ j, (refs j).Nonempty := fun j => Finset.insert_nonempty _ _
              have hrefs_mem : ∀ j r, r ∈ refs j → (r = c ∨ ∃ i, i ≠ l ∧ ψ i < ψ j ∧ p i = r) := by
                intro j r hr
                simp only [hrefs, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
                  Finset.mem_univ, true_and] at hr
                rcases hr with h | ⟨i, ⟨hi, hij⟩, he⟩
                · exact Or.inl h
                · exact Or.inr ⟨i, hi, hij, he⟩
              have hrefs_p : ∀ j i, i ≠ l → ψ i < ψ j → p i ∈ refs j := by
                intro j i hi hij
                simp only [hrefs, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                exact Or.inr ⟨i, ⟨hi, hij⟩, rfl⟩
              have hrefs_c : ∀ j, c ∈ refs j := fun j => Finset.mem_insert_self _ _
              -- G1
              have G1 : ∀ j, j ≠ l → ψ j ≤ ψ l → p j = c := by
                intro j hj hjl
                have hmax := hge j hj ((refs j).max' (hrefs_ne j))
                  (hrefs_mem j _ (Finset.max'_mem _ _)) (fun k hk => ?_)
                have hmin := hle j hj ((refs j).min' (hrefs_ne j))
                  (hrefs_mem j _ (Finset.min'_mem _ _)) (fun k hk => ?_)
                · have h1 := Finset.le_max' _ _ (hrefs_c j)
                  have h2 := Finset.min'_le _ _ (hrefs_c j)
                  linarith
                · have hkl : k ≠ l := by rintro rfl; linarith
                  exact Finset.min'_le _ _ (hrefs_p j k hkl hk)
                · have hkl : k ≠ l := by rintro rfl; linarith
                  exact Finset.le_max' _ _ (hrefs_p j k hkl hk)
              -- G2
              have G2 : 0 < c := by
                by_contra hc0
                push Not at hc0
                have hall : ∀ j, p j ≤ 0 := by
                  intro j
                  by_cases hj : j = l
                  · rw [hj, hpl]
                  have hmin := hle j hj ((refs j).min' (hrefs_ne j))
                    (hrefs_mem j _ (Finset.min'_mem _ _)) (fun k hk => ?_)
                  · have h2 := Finset.min'_le _ _ (hrefs_c j)
                    linarith
                  · by_cases hkl : k = l
                    · rw [hkl, hpl]; have h2 := Finset.min'_le _ _ (hrefs_c j); linarith
                    · exact Finset.min'_le _ _ (hrefs_p j k hkl hk)
                have : ∑ k, lam k * p k * ψ k ≤ 0 := by
                  apply Finset.sum_nonpos; intro k _
                  have := hall k; have := hlam k; have := hψpos k
                  have : lam k * p k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
                  exact mul_nonpos_of_nonpos_of_nonneg this (by linarith)
                exact absurd hRpos (not_lt.2 (by simpa [hψdef] using this))
              -- G3
              have G3 : ∀ j, j ≠ l → ψ l < ψ j → ∀ k, ψ k < ψ j → p k < p j := by
                intro j hj hlj
                have hmax := hgt j hj ((refs j).max' (hrefs_ne j))
                  (hrefs_mem j _ (Finset.max'_mem _ _)) (fun k hk => ?_) hlj
                  (lt_of_lt_of_le G2 (Finset.le_max' _ _ (hrefs_c j)))
                · intro k hk
                  by_cases hkl : k = l
                  · rw [hkl, hpl]; linarith [Finset.le_max' _ _ (hrefs_c j)]
                  · exact lt_of_le_of_lt (Finset.le_max' _ _ (hrefs_p j k hkl hk)) hmax
                · by_cases hkl : k = l
                  · rw [hkl, hpl]; linarith [Finset.le_max' _ _ (hrefs_c j)]
                  · exact Finset.le_max' _ _ (hrefs_p j k hkl hk)
              -- G4
              have G4 : ∀ i j, i ≠ l → j ≠ l → ψ i = ψ j → p i = p j := by
                intro i j hi hj hij
                have h1 := hFOC' i hi
                have h2 := hFOC' j hj
                rw [hij] at h1
                have e1 : ∑ k, lam k * (p i - p k) * min (ψ k) (ψ j) = p i * M j - ∑ k, lam k * p k * min (ψ k) (ψ j) := by
                  simp only [hM, Finset.mul_sum, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun k _ => ?_; ring
                have e2 : ∑ k, lam k * (p j - p k) * min (ψ k) (ψ j) = p j * M j - ∑ k, lam k * p k * min (ψ k) (ψ j) := by
                  simp only [hM, Finset.mul_sum, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun k _ => ?_; ring
                have := hMpos j
                have h3 : (p i - p j) * M j = 0 := by rw [e1] at h1; rw [e2] at h2; linarith
                rcases mul_eq_zero.1 h3 with h | h
                · linarith
                · linarith
              -- price monotone in utility
              have Pmono : ∀ i j, i ≠ l → j ≠ l → u i ≤ u j → p i ≤ p j := by
                intro i j hi hj hij
                rcases lt_or_eq_of_le hij with h | h
                · have hψ := (hψiff i j).2 h
                  by_cases hjl : ψ j ≤ ψ l
                  · rw [G1 i hi (hψ.le.trans hjl), G1 j hj hjl]
                  · exact (G3 j hj (lt_of_not_ge hjl) i hψ).le
                · exact (G4 i j hi hj ((hψeq i j).2 h)).le
              have part1 : ∀ i j, i ≠ l → j ≠ l → α i ≤ α j → p i ≤ p j ∧ u i ≤ u j := by
                intro i j hi hj hαij
                have huij : u i ≤ u j := by
                  by_contra h
                  push Not at h
                  have := Pmono j i hj hi h.le
                  have := hα i; have := hα j
                  nlinarith
                exact ⟨Pmono i j hi hj huij, huij⟩
              refine ⟨part1, fun _ => ?_⟩
              refine ⟨Finset.univ.filter (fun i => i ≠ l ∧ u i ≤ α l), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp
              · intro i hi j hj hjB
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hi hjB
                have hju := hjB hj
                have huij : u i < u j := lt_of_le_of_lt hi.2 hju
                have := Pmono i j hi.1 hj huij.le
                rw [hα i, hα j]; nlinarith
              · intro i hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                exact hi.2
              · intro j hj hjB
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hjB
                exact (hjB hj).le
              · intro i hi j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
                have h1 : ψ i ≤ ψ l := not_lt.1 (fun h => absurd ((hψiff l i).1 h) (not_lt.2 (hul ▸ hi.2)))
                have h2 : ψ j ≤ ψ l := not_lt.1 (fun h => absurd ((hψiff l j).1 h) (not_lt.2 (hul ▸ hj.2)))
                rw [G1 i hi.1 h1, G1 j hj.1 h2]
              · intro i j hi hj hiB hjB hαij
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hiB hjB
                have h1 := part1 i j hi hj hαij.le
                rcases lt_or_eq_of_le h1.2 with h | h
                · have hψ := (hψiff i j).2 h
                  exact G3 j hj ((hψiff l j).2 (by rw [hul]; exact hjB hj)) i hψ
                · exfalso
                  have hp := G4 i j hi hj ((hψeq i j).2 h)
                  have e1 := hα i; have e2 := hα j
                  rw [h, hp] at e1
                  linarith
              · intro i hi j hj hjB
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hi hjB
                have hju := hjB hj
                exact G3 j hj ((hψiff l j).2 (by rw [hul]; exact hju)) i
                  ((hψiff i j).2 (lt_of_le_of_lt hi.2 hju))

            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hP : ∀ k, IsProbabilityMeasure (expMeasure (lam k)) :=
              fun k => isProbabilityMeasure_expMeasure (hlam k)
            have hS : ∀ r : ℝ, 0 < r → ∀ c : ℝ,
                expMeasure r (Set.Ici c) = ENNReal.ofReal (Real.exp (-(r * max c 0))) := by
              intro r hr c
              haveI := isProbabilityMeasure_expMeasure hr
              have hac : expMeasure r ≪ volume := withDensity_absolutelyContinuous _ _
              have h0 : expMeasure r {c} = 0 := hac (Real.volume_singleton)
              have h1 : expMeasure r (Set.Ici c) = expMeasure r (Set.Ioi c) := by
                apply le_antisymm
                · calc expMeasure r (Set.Ici c) ≤ expMeasure r (Set.Ioi c ∪ {c}) := by
                        apply measure_mono
                        intro x hx
                        rcases eq_or_lt_of_le (Set.mem_Ici.1 hx) with h | h
                        · right; exact h.symm
                        · left; exact h
                    _ ≤ expMeasure r (Set.Ioi c) + expMeasure r {c} := measure_union_le _ _
                    _ = expMeasure r (Set.Ioi c) := by rw [h0, add_zero]
                · exact measure_mono Set.Ioi_subset_Ici_self
              have h2 : expMeasure r (Set.Ioi c) = 1 - expMeasure r (Set.Iic c) := by
                rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
              rw [h1, h2, ← ofReal_cdf, cdf_expMeasure_eq hr]
              split_ifs with hc
              · rw [max_eq_left hc]
                have he : Real.exp (-(r * c)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
                rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
                congr 1; ring
              · rw [max_eq_right (by linarith)]
                simp
            set Hf : (Fin (m+1) → ℝ) → ℝ → ℝ := fun v w => Real.exp (-(∑ k, lam k * max (v k - w) 0))
              with hHf
            have hHcont : ∀ v, Continuous (Hf v) := by intro v; simp only [hHf]; fun_prop
            have hHpos : ∀ v w, 0 < Hf v w := fun v w => Real.exp_pos _
            have hHle : ∀ v w k, Hf v w ≤ Real.exp (lam k * w - lam k * v k) := by
              intro v w k
              simp only [hHf]
              apply Real.exp_le_exp.2
              have h1 : lam k * max (v k - w) 0 ≤ ∑ j, lam j * max (v j - w) 0 :=
                Finset.single_le_sum (f := fun j => lam j * max (v j - w) 0)
                  (fun j _ => mul_nonneg (hlam j).le (le_max_right _ _)) (Finset.mem_univ k)
              have h2 : lam k * (v k - w) ≤ lam k * max (v k - w) 0 :=
                mul_le_mul_of_nonneg_left (le_max_left _ _) (hlam k).le
              linarith
            have hHint : ∀ v a, MeasureTheory.IntegrableOn (Hf v) (Set.Iic a) := by
              intro v a
              have hi : MeasureTheory.IntegrableOn (fun w => Real.exp (-(lam 0 * v 0)) * Real.exp (lam 0 * w))
                  (Set.Iic a) := (integrableOn_exp_mul_Iic (hlam 0) a).const_mul _
              refine hi.mono' (hHcont v).aestronglyMeasurable.restrict ?_
              refine Filter.Eventually.of_forall fun w => ?_
              rw [Real.norm_eq_abs, abs_of_pos (hHpos v w), ← Real.exp_add]
              have := hHle v w 0
              calc Hf v w ≤ Real.exp (lam 0 * w - lam 0 * v 0) := this
                _ = _ := by ring_nf
            have hQ : ∀ (v : Fin (m+1) → ℝ) (i : Fin (m+1)),
                choiceProb v lam i = lam i * ∫ w in Set.Iic (v i), Hf v w := by
              intro u i
              set H : ℝ → ℝ := Hf u with hH
              have hHc : Continuous H := hHcont u
              set Ψ : ℝ → ENNReal := fun a => ∫⁻ w in Set.Iic a, ENNReal.ofReal (H w) with hΨ
              have key : errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                  = ENNReal.ofReal (lam i) * Ψ (u i) := by
                have hmp := measurePreserving_piFinSuccAbove (fun k => expMeasure (lam k)) i
                set B : Set (ℝ × (Fin m → ℝ)) :=
                  {p | ∀ j, u (i.succAbove j) - p.2 j ≤ u i - p.1} with hB
                have hBm : MeasurableSet B := by
                  simp only [hB, Set.setOf_forall]
                  exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
                have hA : {z : Fin (m + 1) → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                    = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' B := by
                  ext z
                  simp only [Set.mem_setOf_eq, Set.mem_preimage, hB, MeasurableEquiv.piFinSuccAbove_apply]
                  rw [Fin.forall_iff_succAbove i]
                  simp [Fin.succAbove_ne]
                  exact Iff.rfl
                have h1 : errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                    = ((expMeasure (lam i)).prod (Measure.pi fun j => expMeasure (lam (i.succAbove j)))) B := by
                  rw [hA, errorLaw]
                  exact hmp.measure_preimage hBm.nullMeasurableSet
                rw [h1, Measure.prod_apply hBm]
                have hsec : ∀ t : ℝ, Prod.mk t ⁻¹' B
                    = Set.univ.pi (fun j => Set.Ici (u (i.succAbove j) - u i + t)) := by
                  intro t; ext y
                  simp only [hB, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
                    Set.mem_Ici]
                  constructor
                  · intro h j; linarith [h j]
                  · intro h j; linarith [h j]
                have hF : ∀ t : ℝ, (Measure.pi fun j => expMeasure (lam (i.succAbove j))) (Prod.mk t ⁻¹' B)
                    = ∏ j, ENNReal.ofReal (Real.exp (-(lam (i.succAbove j) *
                        max (u (i.succAbove j) - u i + t) 0))) := by
                  intro t
                  rw [hsec, Measure.pi_pi]
                  exact Finset.prod_congr rfl fun j _ => hS _ (hlam _) _
                simp_rw [hF]
                have hmeasF : Measurable fun t : ℝ => ∏ j, ENNReal.ofReal (Real.exp (-(lam (i.succAbove j) *
                        max (u (i.succAbove j) - u i + t) 0))) := by
                  apply Finset.measurable_prod
                  intro j _
                  apply ENNReal.measurable_ofReal.comp
                  apply Continuous.measurable
                  fun_prop
                rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
                  (show Measurable (gammaPDF 1 (lam i)) from
                    (measurable_gammaPDFReal 1 (lam i)).ennreal_ofReal) hmeasF]
                have hind : Measurable ((Set.Iic (u i)).indicator fun w => ENNReal.ofReal (H w)) :=
                  (ENNReal.measurable_ofReal.comp hHc.measurable).indicator measurableSet_Iic
                calc ∫⁻ t, (gammaPDF 1 (lam i) * fun t => ∏ j, ENNReal.ofReal (Real.exp (-(lam (i.succAbove j) *
                        max (u (i.succAbove j) - u i + t) 0)))) t
                    = ∫⁻ t, ENNReal.ofReal (lam i) *
                        (Set.Iic (u i)).indicator (fun w => ENNReal.ofReal (H w)) (u i - t) := by
                      apply lintegral_congr
                      intro t
                      show exponentialPDF (lam i) t * _ = _
                      rcases le_or_gt 0 t with ht | ht
                      · rw [exponentialPDF_of_nonneg ht, Set.indicator_of_mem (by simp [ht])]
                        beta_reduce
                        rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
                          ← ENNReal.ofReal_mul (by have := hlam i; positivity),
                          ← ENNReal.ofReal_mul (hlam i).le]
                        congr 1
                        rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
                        simp only [hH, hHf]
                        congr 2
                        rw [Fin.sum_univ_succAbove _ i]
                        have e1 : ∀ k, u k - (u i - t) = u k - u i + t := fun k => by ring
                        simp only [e1, sub_self, zero_add, max_eq_left ht]
                        rw [neg_add, ← Finset.sum_neg_distrib]
                      · rw [exponentialPDF_of_neg ht, Set.indicator_of_notMem (by simp; linarith)]
                        simp
                  _ = ENNReal.ofReal (lam i) * Ψ (u i) := by
                      rw [lintegral_const_mul _ (show Measurable fun t => (Set.Iic (u i)).indicator
                          (fun w => ENNReal.ofReal (H w)) (u i - t) from hind.comp (measurable_const.sub measurable_id)),
                        lintegral_sub_left_eq_self (fun w => (Set.Iic (u i)).indicator
                          (fun w => ENNReal.ofReal (H w)) w) (u i),
                        lintegral_indicator measurableSet_Iic]
              rw [choiceProb, key, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hlam i).le]
              congr 1
              rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => (hHpos u w).le)
                (hHc.aestronglyMeasurable)]
            have hΨpos : ∀ v a, 0 < ∫ w in Set.Iic a, Hf v w := by
              intro v a
              rw [integral_pos_iff_support_of_nonneg (fun w => (hHpos v w).le) (hHint v a)]
              have : Function.support (Hf v) = Set.univ :=
                Set.eq_univ_of_forall fun w => (hHpos v w).ne'
              rw [this, Measure.restrict_apply_univ, Real.volume_Iic]
              exact ENNReal.zero_lt_top
            set u := util α β p with hu
            set H : ℝ → ℝ := Hf u with hH
            set Ψ : ℝ → ℝ := fun a => ∫ w in Set.Iic a, H w with hΨ
            have hΨsub : ∀ a b, Ψ b - Ψ a = ∫ w in a..b, H w := by
              intro a b
              exact intervalIntegral.integral_Iic_sub_Iic (hHint u a) (hHint u b)
            have hΨmono : StrictMono Ψ := by
              intro a b hab
              have := hΨsub a b
              have : 0 < ∫ w in a..b, H w :=
                intervalIntegral.intervalIntegral_pos_of_pos_on
                  ((hHcont u).intervalIntegrable a b) (fun w _ => hHpos u w) hab
              linarith
            have hΨderiv : ∀ x, HasDerivAt Ψ (H x) x := by
              intro x
              have h1 := ((hHcont u).integral_hasStrictDerivAt x x).hasDerivAt
              have h2 : Ψ = fun y => Ψ x + ∫ w in x..y, H w := by
                funext y; rw [← hΨsub x y]; ring
              rw [h2]
              exact h1.const_add _
            have hΨcont : Continuous Ψ := continuous_iff_continuousAt.2 fun x => (hΨderiv x).continuousAt
            -- F3
            have hF3 : ∀ a, H a = ∑ k, lam k * Ψ (min (u k) a) := by
              set L := ∑ k, lam k with hL
              have hLpos : 0 < L := Finset.sum_pos (fun k _ => hlam k) ⟨0, Finset.mem_univ _⟩
              set T := Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ u with hT
              have hTle : ∀ k, T ≤ u k := fun k => Finset.inf'_le _ (Finset.mem_univ k)
              set C := ∑ k, lam k * u k with hC
              have hHlow : ∀ w, w ≤ T → H w = Real.exp (-C) * Real.exp (L * w) := by
                intro w hw
                simp only [hH, hHf]
                rw [← Real.exp_add]
                congr 1
                have : ∀ k, max (u k - w) 0 = u k - w := fun k => max_eq_left (by linarith [hTle k])
                simp only [this, hC, hL, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun k _ => ?_; ring
              have hlow : ∀ a, a ≤ T → H a = ∑ k, lam k * Ψ (min (u k) a) := by
                intro a ha
                have hmin : ∀ k, min (u k) a = a := fun k => min_eq_right (ha.trans (hTle k))
                simp only [hmin]
                rw [← Finset.sum_mul, ← hL]
                have : Ψ a = Real.exp (-C) * (Real.exp (L * a) / L) := by
                  simp only [hΨ]
                  rw [setIntegral_congr_fun measurableSet_Iic (fun w hw => hHlow w (le_trans hw ha)),
                    integral_const_mul, integral_exp_mul_Iic hLpos]
                rw [this, hHlow a ha]; field_simp
              intro a
              rcases le_or_gt a T with ha | ha
              · exact hlow a ha
              -- right derivative argument on [T, a]
              set F : ℝ → ℝ := fun x => ∑ k, lam k * Ψ (min (u k) x) - H x with hF
              have hFcont : Continuous F := by
                simp only [hF]
                exact (continuous_finsetSum _ fun k _ => continuous_const.mul
                  (hΨcont.comp (continuous_const.min continuous_id))).sub (hHcont u)
              have hFd : ∀ x ∈ Set.Ico T a, HasDerivWithinAt F 0 (Set.Ici x) x := by
                intro x _
                have hterm : ∀ k, HasDerivWithinAt (fun y => lam k * Ψ (min (u k) y))
                    (lam k * (if x < u k then H x else 0)) (Set.Ici x) x := by
                  intro k
                  apply HasDerivWithinAt.const_mul
                  split_ifs with hxk
                  · apply (hΨderiv x).hasDerivWithinAt.congr_of_eventuallyEq
                    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hxk)] with y hy
                      rw [min_eq_right (le_of_lt hy)]
                    · rw [min_eq_right hxk.le]
                  · apply (hasDerivWithinAt_const x (Set.Ici x) (Ψ (u k))).congr_of_mem
                    · intro y hy; rw [min_eq_left (le_trans (not_lt.1 hxk) hy)]
                    · exact Set.mem_Ici.2 le_rfl
                have hg : ∀ k, HasDerivWithinAt (fun y => -(lam k * max (u k - y) 0))
                    (if x < u k then lam k else 0) (Set.Ici x) x := by
                  intro k
                  split_ifs with hxk
                  · have h0 : HasDerivAt (fun y => -(lam k * (u k - y))) (lam k) x := by
                      have h := ((hasDerivAt_id x).const_mul (lam k)).sub_const (lam k * u k)
                      have e : (fun y => -(lam k * (u k - y))) = fun y => lam k * id y - lam k * u k := by
                        funext y; simp only [id]; ring
                      rw [e]; exact h.congr_deriv (by ring)
                    apply h0.hasDerivWithinAt.congr_of_eventuallyEq
                    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hxk)] with y hy
                      rw [max_eq_left (by have := Set.mem_Iio.1 hy; linarith)]
                    · rw [max_eq_left (by linarith)]
                  · apply (hasDerivWithinAt_const x (Set.Ici x) (0:ℝ)).congr_of_mem
                    · intro y hy
                      rw [max_eq_right (by linarith [le_trans (not_lt.1 hxk) hy])]; simp
                    · exact Set.mem_Ici.2 le_rfl
                have hHd : HasDerivWithinAt H (H x * ∑ k, (if x < u k then lam k else 0)) (Set.Ici x) x := by
                  have := (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ => hg k)).exp
                  have e : H = fun y => Real.exp (∑ k, -(lam k * max (u k - y) 0)) := by
                    funext y; simp only [hH, hHf, Finset.sum_neg_distrib]
                  rw [e]
                  exact this
                have hsum := (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ => hterm k)).sub hHd
                refine hsum.congr_deriv ?_
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                apply Finset.sum_eq_zero
                intro k _
                split_ifs <;> ring
              have := constant_of_has_deriv_right_zero hFcont.continuousOn hFd a ⟨ha.le, le_rfl⟩
              have h2 : F T = 0 := by simp only [hF]; rw [hlow T le_rfl]; ring
              simp only [hF] at this h2
              linarith
            -- first-order conditions
            have hui : ∀ i, α i - β * p i = u i := by intro i; simp [hu, util]
            have hFOC : ∀ i, i ≠ l →
                p i * H (u i) = Ψ (u i) / β + ∑ k, lam k * p k * Ψ (min (u k) (u i)) := by
              intro i hi
              have hli := hlam i
              set E : ℝ → ℝ → ℝ := fun x w => Real.exp (lam i * (max (u i - w) 0 - max (x - w) 0))
                with hE
              have hHG : ∀ w, H w * Real.exp (lam i * max (u i - w) 0) ≤ 1 := by
                intro w
                simp only [hH, hHf]
                rw [← Real.exp_add, Real.exp_le_one_iff]
                have h1 : lam i * max (u i - w) 0 ≤ ∑ j, lam j * max (u j - w) 0 :=
                  Finset.single_le_sum (f := fun j => lam j * max (u j - w) 0)
                    (fun j _ => mul_nonneg (hlam j).le (le_max_right _ _)) (Finset.mem_univ i)
                linarith
              have hE0 : ∀ w, E (u i) w = 1 := by intro w; simp [hE]
              have hHcontu : Continuous H := hHcont u
              have hHintu : ∀ a, IntegrableOn H (Set.Iic a) := hHint u
              have hJ : ∀ b, HasDerivAt (fun x => ∫ w in Set.Iic b, H w * E x w)
                  (-(lam i) * ∫ w in Set.Iic (min b (u i)), H w) (u i) := by
                intro b
                set g : ℝ → ℝ := fun w => (Set.Iic (u i)).indicator (fun w => -(lam i) * H w) w with hg
                have hgm : Measurable g :=
                  ((measurable_const.mul hHcontu.measurable)).indicator measurableSet_Iic
                have hEcont : ∀ x, Continuous (fun w => H w * E x w) := by
                  intro x; rw [hE]; exact hHcontu.mul (by fun_prop)
                have key := hasFDerivAt_integral_of_dominated_loc_of_lip' (μ := volume.restrict (Set.Iic b))
                  (F := fun x w => H w * E x w) (x₀ := (u i))
                  (F' := fun w => g w • ContinuousLinearMap.id ℝ ℝ)
                  (bound := fun w => 2 * (lam i) * H w)
                  (Metric.ball_mem_nhds (u i) (show (0:ℝ) < 1 / (lam i) by positivity))
                  (fun x _ => (hEcont x).aestronglyMeasurable)
                  (by simp only [hE0, mul_one]; exact hHintu b)
                  (hgm.aestronglyMeasurable.smul_const _)
                  ?lip ((hHintu b).const_mul _) ?diff
                case lip =>
                  refine Filter.Eventually.of_forall fun w x hx => ?_
                  rw [hE0, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, ← mul_sub_one, abs_mul,
                    abs_of_pos (hHpos u w)]
                  have hx' : |x - (u i)| < 1 / (lam i) := by
                    rw [Metric.mem_ball, Real.dist_eq] at hx; exact hx
                  have hd : |(lam i) * (max ((u i) - w) 0 - max (x - w) 0)| ≤ (lam i) * |x - (u i)| := by
                    rw [abs_mul, abs_of_pos hli]
                    apply mul_le_mul_of_nonneg_left _ hli.le
                    have := abs_max_sub_max_le_abs ((u i) - w) (x - w) 0
                    calc _ ≤ |(u i) - w - (x - w)| := this
                      _ = |x - (u i)| := by rw [abs_sub_comm]; ring_nf
                  have hd1 : |(lam i) * (max ((u i) - w) 0 - max (x - w) 0)| ≤ 1 := by
                    have : (lam i) * |x - (u i)| ≤ 1 := by
                      have := mul_lt_mul_of_pos_left hx' hli
                      rw [mul_one_div_cancel hli.ne'] at this; linarith
                    linarith
                  have h3 := Real.abs_exp_sub_one_le hd1
                  have h4 : |E x w - 1| ≤ 2 * ((lam i) * |x - (u i)|) := by
                    rw [hE]; exact h3.trans (by linarith)
                  calc H w * |E x w - 1| ≤ H w * (2 * ((lam i) * |x - (u i)|)) :=
                        mul_le_mul_of_nonneg_left h4 (hHpos u w).le
                    _ = 2 * (lam i) * H w * |x - (u i)| := by ring
                case diff =>
                  have hae : ∀ᵐ w ∂(volume.restrict (Set.Iic b)), w ≠ (u i) := by
                    apply ae_restrict_of_ae
                    rw [ae_iff]
                    have : {a : ℝ | ¬a ≠ (u i)} = {(u i)} := by ext a; simp
                    rw [this]; exact Real.volume_singleton
                  filter_upwards [hae] with w hw
                  have hd : HasDerivAt (fun x => H w * E x w) (g w) (u i) := by
                    rcases lt_or_gt_of_ne hw with h | h
                    · -- w < (u i)
                      have h1 : HasDerivAt (fun x => H w * Real.exp ((lam i) * ((u i) - x))) (-(lam i) * H w) (u i) := by
                        have := (((hasDerivAt_id (u i)).const_sub (u i)).const_mul (lam i)).exp.const_mul (H w)
                        refine this.congr_deriv ?_
                        simp; ring
                      have hgw : g w = -(lam i) * H w := by
                        simp only [hg]; rw [Set.indicator_of_mem (Set.mem_Iic.2 h.le)]
                      rw [hgw]
                      apply h1.congr_of_eventuallyEq
                      filter_upwards [Ioi_mem_nhds h] with x hx
                      rw [hE]; simp only
                      rw [max_eq_left (by linarith), max_eq_left (by have := Set.mem_Ioi.1 hx; linarith)]
                      congr 2; ring
                    · -- w > (u i)
                      have hgw : g w = 0 := by
                        simp only [hg]; rw [Set.indicator_of_notMem (by simp; linarith)]
                      rw [hgw]
                      apply (hasDerivAt_const (u i) (H w)).congr_of_eventuallyEq
                      filter_upwards [Iio_mem_nhds h] with x hx
                      rw [hE]; simp only
                      rw [max_eq_right (by linarith), max_eq_right (by have := Set.mem_Iio.1 hx; linarith)]
                      simp
                  have e : g w • ContinuousLinearMap.id ℝ ℝ = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g w) := by
                    ext; simp
                  rw [e]; exact hd.hasFDerivAt
                obtain ⟨-, hfd⟩ := key
                have h2 := hfd.hasDerivAt
                rw [integral_smul_const] at h2
                refine h2.congr_deriv ?_
                simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
                simp only [hg]
                rw [setIntegral_indicator measurableSet_Iic, Set.Iic_inter_Iic, integral_const_mul]
              have hK : HasDerivAt (fun x => ∫ w in Set.Iic x, H w * E x w)
                  (H (u i) - (lam i) * ∫ w in Set.Iic (u i), H w) (u i) := by
                set Gf : ℝ → ℝ := fun w => H w * Real.exp ((lam i) * max ((u i) - w) 0) * Real.exp ((lam i) * w)
                  with hGf
                have hGc : Continuous Gf := by simp only [hGf]; exact (hHcontu.mul (by fun_prop)).mul (by fun_prop)
                have hGint : ∀ a, IntegrableOn Gf (Set.Iic a) := by
                  intro a
                  refine (integrableOn_exp_mul_Iic hli a).mono' hGc.aestronglyMeasurable.restrict ?_
                  refine Filter.Eventually.of_forall fun w => ?_
                  have h1 := hHG w
                  have h2 : 0 ≤ H w * Real.exp ((lam i) * max ((u i) - w) 0) :=
                    mul_nonneg (hHpos u w).le (Real.exp_pos _).le
                  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 (Real.exp_pos _).le)]
                  calc Gf w ≤ 1 * Real.exp ((lam i) * w) :=
                        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
                    _ = _ := one_mul _
                set Φ : ℝ → ℝ := fun a => ∫ w in Set.Iic a, Gf w with hΦ
                have hΦd : HasDerivAt Φ (Gf (u i)) (u i) := by
                  have h1 := (hGc.integral_hasStrictDerivAt (u i) (u i)).hasDerivAt
                  have h2 : Φ = fun y => Φ (u i) + ∫ w in (u i)..y, Gf w := by
                    funext y
                    rw [← intervalIntegral.integral_Iic_sub_Iic (hGint (u i)) (hGint y)]; ring
                  rw [h2]
                  exact h1.const_add _
                have hKeq : (fun x => ∫ w in Set.Iic x, H w * E x w) =
                    fun x => Real.exp (-((lam i) * x)) * Φ x := by
                  funext x
                  simp only [hΦ]
                  rw [← integral_const_mul]
                  refine setIntegral_congr_fun measurableSet_Iic fun w hw => ?_
                  have hw' : w ≤ x := hw
                  simp only [hE, hGf]
                  rw [max_eq_left (show (0:ℝ) ≤ x - w by linarith)]
                  have e : Real.exp ((lam i) * (max ((u i) - w) 0 - (x - w))) = Real.exp (-((lam i) * x)) *
                      Real.exp ((lam i) * max ((u i) - w) 0) * Real.exp ((lam i) * w) := by
                    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
                  rw [e]; ring
                rw [hKeq]
                have hexp : HasDerivAt (fun x => Real.exp (-((lam i) * x))) (Real.exp (-((lam i) * (u i))) * (-((lam i) * 1))) (u i) :=
                  (((hasDerivAt_id (u i)).const_mul (lam i)).neg).exp
                refine (hexp.mul hΦd).congr_deriv ?_
                have hK0 : Real.exp (-((lam i) * (u i))) * Φ (u i) = ∫ w in Set.Iic (u i), H w := by
                  have := congrFun hKeq (u i)
                  simp only [hE0, mul_one] at this
                  exact this.symm
                have hG0 : Gf (u i) = H (u i) * Real.exp ((lam i) * (u i)) := by simp [hGf]
                rw [hG0, ← hK0]
                have : Real.exp (-((lam i) * (u i))) * (H (u i) * Real.exp ((lam i) * (u i))) = H (u i) := by
                  rw [mul_comm, mul_assoc, ← Real.exp_add]; simp
                linear_combination this

              have hutil : ∀ t, util α β (Function.update p i t) = Function.update u i (α i - β * t) := by
                intro t; funext k
                by_cases hk : k = i
                · subst hk; simp [util]
                · simp [util, Function.update_of_ne hk, hu]
              have hHv : ∀ x w, Hf (Function.update u i x) w = H w * E x w := by
                intro x w
                simp only [hH, hHf, hE]
                rw [← Real.exp_add]
                congr 1
                have h : ∑ k, lam k * max (Function.update u i x k - w) 0 - ∑ k, lam k * max (u k - w) 0
                    = lam i * (max (x - w) 0 - max (u i - w) 0) := by
                  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
                  · simp; ring
                  · intro b _ hb; simp [Function.update_of_ne hb]
                  · simp
                linarith
              have hf : ∀ t, revenue α β lam (Function.update p i t) = ∑ k, Function.update p i t k *
                  (lam k * ∫ w in Set.Iic (Function.update u i (α i - β * t) k), H w * E (α i - β * t) w) := by
                intro t
                unfold revenue
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [hQ, hutil]
                simp only [hHv]
              have hx : HasDerivAt (fun t => α i - β * t) (-β) (p i) := by
                have := ((hasDerivAt_id (p i)).const_mul β).const_sub (α i)
                exact this.congr_deriv (by simp)
              set D : Fin (m+1) → ℝ := fun k => lam k * p k * β * lam i * Ψ (min (u k) (u i)) +
                (if k = i then lam i * Ψ (u i) - β * lam i * p i * H (u i) else 0) with hD
              have hterm : ∀ k, HasDerivAt (fun t => Function.update p i t k *
                  (lam k * ∫ w in Set.Iic (Function.update u i (α i - β * t) k), H w * E (α i - β * t) w))
                  (D k) (p i) := by
                intro k
                by_cases hk : k = i
                · subst hk
                  have e : (fun t => Function.update p k t k *
                      (lam k * ∫ w in Set.Iic (Function.update u k (α k - β * t) k), H w * E (α k - β * t) w))
                      = fun t => t * (lam k * (fun x => ∫ w in Set.Iic x, H w * E x w) (α k - β * t)) := by
                    funext t; simp
                  rw [e]
                  have hK' := hK
                  rw [← hui k] at hK'
                  have h2 := (hasDerivAt_id (p k)).mul ((hK'.comp (p k) hx).const_mul (lam k))
                  refine h2.congr_deriv ?_
                  simp only [hD, if_pos rfl, id, Function.comp]
                  rw [hui k]
                  simp only [hE0, mul_one, min_self, if_true, hΨ]
                  ring
                · have e : (fun t => Function.update p i t k *
                      (lam k * ∫ w in Set.Iic (Function.update u i (α i - β * t) k), H w * E (α i - β * t) w))
                      = fun t => p k * (lam k * (fun x => ∫ w in Set.Iic (u k), H w * E x w) (α i - β * t)) := by
                    funext t; simp [Function.update_of_ne hk]
                  rw [e]
                  have hJ' := hJ (u k)
                  rw [← hui i] at hJ'
                  have h2 := ((hJ'.comp (p i) hx).const_mul (lam k)).const_mul (p k)
                  refine h2.congr_deriv ?_
                  simp only [hD, if_neg hk]
                  rw [hui i]
                  ring
              have hderiv := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hterm k)
              have hmax : IsLocalMax (fun t => revenue α β lam (Function.update p i t)) (p i) := by
                refine Filter.Eventually.of_forall fun t => ?_
                simp only [Function.update_eq_self]
                exact hp.2 _ (by rw [Function.update_of_ne (Ne.symm hi)]; exact hp.1)
              have hfeq : (fun t => revenue α β lam (Function.update p i t)) = fun t => ∑ k, Function.update p i t k *
                  (lam k * ∫ w in Set.Iic (Function.update u i (α i - β * t) k), H w * E (α i - β * t) w) := by
                funext t; exact hf t
              rw [hfeq] at hmax
              have h0 := hmax.hasDerivAt_eq_zero hderiv
              have hsumD : ∑ k, D k = β * lam i * ∑ k, lam k * p k * Ψ (min (u k) (u i)) +
                  (lam i * Ψ (u i) - β * lam i * p i * H (u i)) := by
                simp only [hD, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
                  Finset.mul_sum]
                congr 1
                refine Finset.sum_congr rfl fun k _ => ?_; ring
              rw [hsumD] at h0
              have hbl : 0 < β * lam i := mul_pos hβ hli
              field_simp
              have : β * lam i * (p i * H (u i) * β) = β * lam i * (Ψ (u i) + β * ∑ k, lam k * p k * Ψ (min (u k) (u i))) := by
                linear_combination (-β) * h0
              have := mul_left_cancel₀ hbl.ne' this
              linarith
            -- revenue positive
            have hRpos : 0 < ∑ k, lam k * p k * Ψ (u k) := by
              have hrev : revenue α β lam p = ∑ k, lam k * p k * Ψ (u k) := by
                unfold revenue
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [hQ]; simp only [hΨ, hH, hu]; ring
              rw [← hrev]
              obtain ⟨k0, hk0⟩ : ∃ k, k ≠ l := by
                by_contra h
                push Not at h
                have := Fintype.card_le_one_iff.2 (fun a b => (h a).trans (h b).symm)
                simp at this; omega
              set q : Fin (m+1) → ℝ := fun k => if k = l then 0 else 1 with hq
              have hql : q l = 0 := by simp [hq]
              refine lt_of_lt_of_le ?_ (hp.2 q hql)
              unfold revenue
              apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun k => q k * choiceProb (util α β q) lam k)
                (fun k _ => ?_) (Finset.mem_univ k0))
              · simp only [hq, if_neg hk0, one_mul]
                rw [hQ]; exact mul_pos (hlam k0) (hΨpos _ _)
              · rw [hQ]
                by_cases hkl : k = l
                · simp [hq, hkl]
                · simp only [hq, if_neg hkl, one_mul]; exact (mul_pos (hlam k) (hΨpos _ _)).le
            have hFOC2 : ∀ i, i ≠ l → ∑ k, lam k * (p i - p k) * min (Ψ (util α β p k)) (Ψ (util α β p i))
                  = Ψ (util α β p i) / β := by
              intro i hi
              have h1 := hFOC i hi
              rw [hF3 (u i)] at h1
              have hmin : ∀ k, Ψ (min (u k) (u i)) = min (Ψ (u k)) (Ψ (u i)) :=
                fun k => hΨmono.monotone.map_min
              simp only [hmin] at h1
              have e : ∑ k, lam k * (p i - p k) * min (Ψ (u k)) (Ψ (u i)) =
                  p i * ∑ k, lam k * min (Ψ (u k)) (Ψ (u i)) - ∑ k, lam k * p k * min (Ψ (u k)) (Ψ (u i)) := by
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun k _ => ?_; ring
              show ∑ k, lam k * (p i - p k) * min (Ψ (u k)) (Ψ (u i)) = Ψ (u i) / β
              rw [e]; linarith
            exact alg Ψ hp.1 (hΨpos u) hΨmono hFOC2 hRpos
