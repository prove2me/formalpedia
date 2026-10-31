-- Prove2me | solution 1 for HighDimStat.GraphicalModels.thm11_8_hammersley_clifford
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:56:09.98653+00:00
-- url     : https://prove2.me/submissions/61712bf9-6d85-49b3-9ebb-21d4d9d542e9

import Mathlib
import Definitions.Def_HighDimStat_GraphicalModels_Core

open MeasureTheory ProbabilityTheory HighDimStat.GraphicalModels

noncomputable def f : ℝ → ℝ := gaussianPDFReal 0 1

lemma f_pos (t : ℝ) : 0 < f t := gaussianPDFReal_pos 0 1 t one_ne_zero
lemma f_nonneg (t : ℝ) : 0 ≤ f t := (f_pos t).le

lemma lintegral_f : ∫⁻ t, ENNReal.ofReal (f t) = 1 := by
  have h := lintegral_gaussianPDF_eq_one (0 : ℝ) (v := 1) one_ne_zero
  rw [gaussianPDF_def] at h
  exact h

lemma measurable_f : Measurable (fun t => ENNReal.ofReal (f t)) :=
  ENNReal.measurable_ofReal.comp (measurable_gaussianPDFReal 0 1)

noncomputable def p₀ (x : Fin 2 → ℝ) : ℝ := f (x 0) * f (x 1)

lemma p₀_pos (x : Fin 2 → ℝ) : 0 < p₀ x := mul_pos (f_pos _) (f_pos _)

noncomputable def P : Measure (Fin 2 → ℝ) :=
  (volume : Measure (Fin 2 → ℝ)).withDensity (fun x => ENNReal.ofReal (p₀ x))

lemma P_univ : P Set.univ = 1 := by
  rw [P, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h_mul (x : Fin 2 → ℝ) : ENNReal.ofReal (p₀ x) =
      (fun p : ℝ × ℝ => ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2))
        ((MeasurableEquiv.piFinTwo (fun _ => ℝ)) x) := by
    simp [p₀, ENNReal.ofReal_mul (f_nonneg _)]
  simp_rw [h_mul]
  have h_mp := MeasureTheory.volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  have h_emb := (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding
  have h_lint := h_mp.lintegral_comp_emb h_emb
    (fun p : ℝ × ℝ => ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2))
  rw [h_lint]
  change ∫⁻ (b : ℝ × ℝ), ENNReal.ofReal (f b.1) * ENNReal.ofReal (f b.2) ∂(volume.prod volume) = 1
  rw [lintegral_prod_mul measurable_f.aemeasurable measurable_f.aemeasurable]
  rw [lintegral_f, mul_one]

instance : IsProbabilityMeasure P := ⟨P_univ⟩

lemma hFact₀ : Factorizes (⊥ : SimpleGraph (Fin 2)) p₀ := by
  let c0 : Finset (Fin 2) := {0}
  let c1 : Finset (Fin 2) := {1}
  have hc01 : c0 ≠ c1 := by
    intro h
    have : (0 : Fin 2) ∈ c1 := by
      rw [← h]
      exact Finset.mem_singleton_self 0
    simp [c1] at this
  let cliques : Finset (Finset (Fin 2)) := {c0, c1}
  let ψ : Finset (Fin 2) → (Fin 2 → ℝ) → ℝ := fun C x =>
    if C = c0 then f (x 0) else if C = c1 then f (x 1) else 1
  refine ⟨cliques, ψ, 1, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro C hC
    simp only [cliques, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · intro a ha b hb _
      simp only [c0, Finset.mem_coe, Finset.mem_singleton] at ha hb
      subst ha hb
      contradiction
    · intro a ha b hb _
      simp only [c1, Finset.mem_coe, Finset.mem_singleton] at ha hb
      subst ha hb
      contradiction
  · intro C hC x
    simp only [cliques, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · simp only [ψ, if_pos rfl]
      exact f_nonneg _
    · simp only [ψ, if_neg hc01.symm]
      exact f_nonneg _
  · intro C hC x y hxy
    simp only [cliques, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · simp only [ψ, if_pos rfl]
      have : x 0 = y 0 := hxy 0 (Finset.mem_singleton_self 0)
      rw [this]
    · simp only [ψ, if_neg hc01.symm]
      have : x 1 = y 1 := hxy 1 (Finset.mem_singleton_self 1)
      rw [this]
  · intro x
    rw [one_mul]
    have hprod : ∏ C ∈ cliques, ψ C x = ψ c0 x * ψ c1 x := Finset.prod_pair hc01
    rw [hprod]
    simp only [ψ, if_pos rfl, if_neg hc01.symm]
    rfl

noncomputable def p₁ (x : Fin 2 → ℝ) : ℝ := if x = 0 then 2 * p₀ x else p₀ x

lemma p₁_pos (x : Fin 2 → ℝ) : 0 < p₁ x := by
  dsimp [p₁]
  split_ifs
  · exact mul_pos (by norm_num) (p₀_pos x)
  · exact p₀_pos x

lemma p₁_ae_eq_p₀ : (fun x => ENNReal.ofReal (p₁ x)) =ᵐ[volume] (fun x => ENNReal.ofReal (p₀ x)) := by
  rw [Filter.EventuallyEq, ae_iff]
  apply measure_mono_null (s := {x | ¬ ENNReal.ofReal (p₁ x) = ENNReal.ofReal (p₀ x)})
  · intro x hx
    by_contra hx0
    have : p₁ x = p₀ x := if_neg hx0
    exact hx (congrArg ENNReal.ofReal this)
  · exact measure_singleton (0 : Fin 2 → ℝ)

lemma p₁_density :
    Measure.map id P = (volume : Measure (Fin 2 → ℝ)).withDensity (fun x => ENNReal.ofReal (p₁ x)) := by
  rw [Measure.map_id, P]
  exact withDensity_congr_ae p₁_ae_eq_p₀.symm

def x00 : Fin 2 → ℝ := 0
def x11 : Fin 2 → ℝ := fun _ => 1
def x01 : Fin 2 → ℝ := ![0, 1]
def x10 : Fin 2 → ℝ := ![1, 0]

lemma clique_not_both {C : Finset (Fin 2)} (hC : (⊥ : SimpleGraph (Fin 2)).IsClique (↑C : Set (Fin 2))) :
    ¬ (0 ∈ C ∧ 1 ∈ C) := by
  rintro ⟨h0, h1⟩
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have := hC h0 h1 hne
  exact this

lemma psi_mul_eq {C : Finset (Fin 2)} (hC : (⊥ : SimpleGraph (Fin 2)).IsClique (↑C : Set (Fin 2)))
    {ψ : Finset (Fin 2) → (Fin 2 → ℝ) → ℝ}
    (hcoord : ∀ x y : Fin 2 → ℝ, (∀ j ∈ C, x j = y j) → ψ C x = ψ C y) :
    ψ C x00 * ψ C x11 = ψ C x01 * ψ C x10 := by
  have hcases : 0 ∉ C ∨ 1 ∉ C := by
    have h_not := clique_not_both hC
    tauto
  rcases hcases with h0 | h1
  · have h0_eq : ∀ j ∈ C, x00 j = x10 j := by
      intro j hj
      fin_cases j
      · contradiction
      · rfl
    have h1_eq : ∀ j ∈ C, x11 j = x01 j := by
      intro j hj
      fin_cases j
      · contradiction
      · rfl
    rw [hcoord x00 x10 h0_eq, hcoord x11 x01 h1_eq, mul_comm]
  · have h0_eq : ∀ j ∈ C, x00 j = x01 j := by
      intro j hj
      fin_cases j
      · rfl
      · contradiction
    have h1_eq : ∀ j ∈ C, x11 j = x10 j := by
      intro j hj
      fin_cases j
      · rfl
      · contradiction
    rw [hcoord x00 x01 h0_eq, hcoord x11 x10 h1_eq]

lemma factorizes_p1_eq {p : (Fin 2 → ℝ) → ℝ} (hFact : Factorizes (⊥ : SimpleGraph (Fin 2)) p) :
    p x00 * p x11 = p x01 * p x10 := by
  rcases hFact with ⟨cliques, ψ, c, _, hclique, _, hcoord, hp⟩
  rw [hp x00, hp x11, hp x01, hp x10]
  have hprod : (∏ C ∈ cliques, ψ C x00) * (∏ C ∈ cliques, ψ C x11) =
      (∏ C ∈ cliques, ψ C x01) * (∏ C ∈ cliques, ψ C x10) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro C hC
    exact psi_mul_eq (hclique C hC) (hcoord C hC)
  calc (c * ∏ C ∈ cliques, ψ C x00) * (c * ∏ C ∈ cliques, ψ C x11)
    _ = (c * c) * ((∏ C ∈ cliques, ψ C x00) * (∏ C ∈ cliques, ψ C x11)) := by ring
    _ = (c * c) * ((∏ C ∈ cliques, ψ C x01) * (∏ C ∈ cliques, ψ C x10)) := by rw [hprod]
    _ = (c * ∏ C ∈ cliques, ψ C x01) * (c * ∏ C ∈ cliques, ψ C x10) := by ring

lemma x00_eq_zero : x00 = 0 := rfl

lemma x11_ne_zero : x11 ≠ 0 := by
  intro h
  have := congr_fun h 0
  norm_num [x11] at this

lemma x01_ne_zero : x01 ≠ 0 := by
  intro h
  have := congr_fun h 1
  norm_num [x01] at this

lemma x10_ne_zero : x10 ≠ 0 := by
  intro h
  have := congr_fun h 0
  norm_num [x10] at this

lemma p1_eq_zero : p₁ x00 = 2 * (f 0 * f 0) := by
  change (if (0 : Fin 2 → ℝ) = 0 then 2 * p₀ 0 else p₀ 0) = 2 * (f 0 * f 0)
  rw [if_pos rfl]
  rfl

lemma p1_eq_11 : p₁ x11 = f 1 * f 1 := by
  dsimp [p₁]
  rw [if_neg x11_ne_zero]
  rfl

lemma p1_eq_01 : p₁ x01 = f 0 * f 1 := by
  dsimp [p₁]
  rw [if_neg x01_ne_zero]
  rfl

lemma p1_eq_10 : p₁ x10 = f 1 * f 0 := by
  dsimp [p₁]
  rw [if_neg x10_ne_zero]
  rfl

lemma p1_not_factorizes : ¬ Factorizes (⊥ : SimpleGraph (Fin 2)) p₁ := by
  intro hFact
  have h_eq := factorizes_p1_eq hFact
  rw [p1_eq_zero, p1_eq_11, p1_eq_01, p1_eq_10] at h_eq
  have hpos : 0 < f 0 * f 0 * f 1 * f 1 := by
    apply mul_pos
    · apply mul_pos
      · exact mul_pos (f_pos 0) (f_pos 0)
      · exact f_pos 1
    · exact f_pos 1
  linarith

theorem solution : ¬ (∀ {V Ω : Type} [Fintype V] [DecidableEq V]
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (G : SimpleGraph V) (X : Ω → V → ℝ)
    (hX : Measurable X) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : (V → ℝ) → ℝ) (_hp : ∀ x, 0 < p x)
    (_hpdensity : Measure.map X P =
        (MeasureTheory.volume : Measure (V → ℝ)).withDensity (fun x => ENNReal.ofReal (p x))),
    Factorizes G p ↔ IsMarkov G X hX P) := by
  intro H
  have hp₀_dens : Measure.map id P =
      (MeasureTheory.volume : Measure (Fin 2 → ℝ)).withDensity (fun x => ENNReal.ofReal (p₀ x)) := by
    rw [Measure.map_id, P]
  have h0 := H (⊥ : SimpleGraph (Fin 2)) id measurable_id P p₀ p₀_pos hp₀_dens
  have hMarkov : IsMarkov (⊥ : SimpleGraph (Fin 2)) id measurable_id P := h0.mp hFact₀
  have h1 := H (⊥ : SimpleGraph (Fin 2)) id measurable_id P p₁ p₁_pos p₁_density
  have hFact₁ : Factorizes (⊥ : SimpleGraph (Fin 2)) p₁ := h1.mpr hMarkov
  exact p1_not_factorizes hFact₁
