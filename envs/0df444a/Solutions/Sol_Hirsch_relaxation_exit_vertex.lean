-- Prove2me | solution 1 for Hirsch.relaxation_exit_vertex
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:36:59.946745+00:00
-- url     : https://prove2.me/submissions/686b1545-0451-4a54-b47f-cc843b2fcda9

import Mathlib
import Definitions.Def_Hirsch_model
set_option autoImplicit false
open scoped RealInnerProductSpace
open Set Filter Topology Hirsch

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : Finset (Fin n)) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hPQ : Hpoly a b ⊆ Q) (hQ : ∀ z ∈ Q, ∀ j ∈ T, ⟪a j, z⟫ ≤ b j)
    (x y : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) (hadj : Adj Q x y) :
    (y ∈ Hpoly a b → Adj (Hpoly a b) x y) ∧
    (y ∉ Hpoly a b → ∃ z ∈ segment ℝ x y, (z = x ∨ Adj (Hpoly a b) x z) ∧
        ∃ j, j ∉ T ∧ ⟪a j, z⟫ = b j) := by
  classical
  have hconv : Convex ℝ (Hpoly a b) := by
    intro u hu v hv α β hα hβ hsum
    intro j
    simp only [inner_add_right, inner_smul_right]
    have h1 := mul_le_mul_of_nonneg_left (hu j) hα
    have h2 := mul_le_mul_of_nonneg_left (hv j) hβ
    have heq : α * b j + β * b j = b j := by rw [← add_mul, hsum, one_mul]
    linarith
  refine ⟨fun hy => ⟨hadj.1, hadj.2.mono hPQ (hconv.segment_subset hx hy)⟩, ?_⟩
  intro hy
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) := AffineMap.lineMap x y
  let C : Set ℝ := Icc 0 1 ∩ {t | L t ∈ Hpoly a b}
  have hc : IsClosed {t : ℝ | L t ∈ Hpoly a b} := by
    change IsClosed {t : ℝ | ∀ j, ⟪a j, L t⟫ ≤ b j}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_le
    · dsimp [L]
      fun_prop
    · fun_prop
  have hcompact : IsCompact C := isCompact_Icc.inter_right hc
  have hnonempty : C.Nonempty := ⟨0, by simp [C, L, hx]⟩
  obtain ⟨r, hr⟩ := hcompact.exists_isGreatest hnonempty
  have hr0 : 0 ≤ r := hr.1.1.1
  have hr1 : r ≤ 1 := hr.1.1.2
  have hrP : L r ∈ Hpoly a b := hr.1.2
  have hrlt : r < 1 := by
    apply lt_of_le_of_ne hr1
    intro heq
    apply hy
    simpa [heq, L] using hrP
  let z := L r
  have hzseg : z ∈ segment ℝ x y := lineMap_mem_segment ℝ x y ⟨hr0, hr1⟩
  have hztight : ∃ j, j ∉ T ∧ ⟪a j, z⟫ = b j := by
    by_contra hn
    push Not at hn
    have hev : ∀ᶠ t : ℝ in 𝓝 r, ∀ j, t ∈ Icc (0 : ℝ) 1 → ⟪a j, L t⟫ ≤ b j := by
      apply Filter.eventually_all.mpr
      intro j
      by_cases hj : j ∈ T
      · filter_upwards [] with t ht
        exact hQ (L t) (hadj.2.subset (lineMap_mem_segment ℝ x y ht)) j hj
      · have hstrict : ⟪a j, L r⟫ < b j := lt_of_le_of_ne (hrP j) (hn j hj)
        have hcont : Continuous (fun t : ℝ => ⟪a j, L t⟫) := by dsimp [L]; fun_prop
        filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hstrict)] with t ht
        exact fun _ => le_of_lt ht
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    let ε := min δ (1 - r) / 2
    have hepos : 0 < ε := half_pos (lt_min hδ (sub_pos.mpr hrlt))
    have heδ : ε < δ := by
      have h := min_le_left δ (1 - r)
      dsimp [ε]
      linarith
    have heone : ε ≤ 1 - r := by
      have h := min_le_right δ (1 - r)
      dsimp [ε]
      linarith
    have htIcc : r + ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have htineq : ∀ j, r + ε ∈ Icc (0 : ℝ) 1 → ⟪a j, L (r + ε)⟫ ≤ b j := hball (by
      simpa [Real.dist_eq, abs_of_pos hepos] using heδ)
    have htC : r + ε ∈ C := ⟨htIcc, fun j => htineq j htIcc⟩
    have hmax := hr.2 htC
    linarith
  have hsegimage : segment ℝ x z = L '' Icc (0 : ℝ) r := by
    rw [← segment_eq_Icc hr0, image_segment]
    simp [L, z]
  have hintersection : segment ℝ x z = Hpoly a b ∩ segment ℝ x y := by
    apply Subset.antisymm
    · intro p hp
      refine ⟨hconv.segment_subset hx hrP hp, ?_⟩
      rw [hsegimage] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      exact lineMap_mem_segment ℝ x y ⟨ht.1, ht.2.trans hr1⟩
    · rintro p ⟨hpP, hpSeg⟩
      rw [segment_eq_image_lineMap] at hpSeg
      obtain ⟨t, ht, htP⟩ := hpSeg
      have htC : t ∈ C := ⟨ht, by simpa [L, htP] using hpP⟩
      rw [hsegimage]
      exact ⟨t, ⟨ht.1, hr.2 htC⟩, htP⟩
  have hext : IsExtreme ℝ (Hpoly a b) (Hpoly a b ∩ segment ℝ x y) := by
    refine ⟨inter_subset_left, ?_⟩
    intro p hp q hq v hv hmem
    exact ⟨hp, hadj.2.left_mem_of_mem_openSegment (hPQ hp) (hPQ hq) hv.2 hmem⟩
  rw [← hintersection] at hext
  refine ⟨z, hzseg, ?_, hztight⟩
  by_cases hzx : z = x
  · exact Or.inl hzx
  · exact Or.inr ⟨Ne.symm hzx, hext⟩
#print axioms solution
