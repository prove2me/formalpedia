-- Prove2me | solution 1 for GraphLQGame.Equilibrium.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:40:38.220179+00:00
-- url     : https://prove2.me/submissions/4852a51c-d7ed-4bcc-ade5-ffcb98ef2663

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph

set_option autoImplicit false
open GraphLQGame.Equilibrium

lemma gle_deg_iso {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : G ≃g G) (v : Fin n) :
    G.degree (φ v) = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_equiv φ.symm.toEquiv
  intro i
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    have := φ.symm.map_adj_iff.mpr h
    simpa using this
  · intro h
    simpa using (φ.map_adj_iff.mpr h)

lemma gle_R_mul {n : ℕ} {G : SimpleGraph (Fin n)} (φ : G ≃g G) (Y : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n) : (autMatrix φ * Y) a b = Y (φ.symm a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (φ.symm a)]
  · simp [autMatrix]
  · intro c _ hc
    have : a ≠ φ c := by
      intro h; apply hc; rw [h]; simp
    simp [autMatrix, this]
  · simp

lemma gle_mul_R {n : ℕ} {G : SimpleGraph (Fin n)} (φ : G ≃g G) (Y : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n) : (Y * autMatrix φ) a b = Y a (φ b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (φ b)]
  · simp [autMatrix]
  · intro c _ hc
    simp [autMatrix, hc]
  · simp

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) :
    (∀ φ : G ≃g G, lap G * autMatrix φ = autMatrix φ * lap G) ∧
      (∀ Y : Matrix (Fin n) (Fin n) ℝ, (∀ φ : G ≃g G, Y * autMatrix φ = autMatrix φ * Y) →
        ∀ i, Y i i = (n : ℝ)⁻¹ * Y.trace) ∧
      (∀ Y : Fin n → Matrix (Fin n) (Fin n) ℝ,
        (∀ (φ : G ≃g G) (i : Fin n), autMatrix φ * Y i = Y (φ i) * autMatrix φ) →
        ∀ i j, Y i i i = Y j j j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    ext a b
    rw [gle_mul_R, gle_R_mul]
    -- L (φ.symm a) b = L a (φ b)
    have hinv : ∀ u v : Fin n, lap G (φ u) (φ v) = lap G u v := by
      intro u v
      simp only [lap, gle_deg_iso]
      have h1 : G.Adj (φ u) (φ v) ↔ G.Adj u v := φ.map_adj_iff
      have h2 : (φ u = φ v) ↔ (u = v) := φ.toEquiv.apply_eq_iff_eq
      simp only [h1, h2]
    have := hinv (φ.symm a) b
    simpa using this
  · intro Y hY
    have hinv : ∀ (φ : G ≃g G) (u v : Fin n), Y (φ u) (φ v) = Y u v := by
      intro φ u v
      have := congrFun (congrFun (hY φ) (φ u)) v
      rw [gle_mul_R, gle_R_mul] at this
      simpa using this
    have hdiag : ∀ i j : Fin n, Y j j = Y i i := by
      intro i j
      obtain ⟨φ, hφ⟩ := hT i j
      rw [← hφ, hinv]
    intro i
    have htr : Y.trace = (n : ℝ) * Y i i := by
      simp only [Matrix.trace, Matrix.diag]
      rw [Finset.sum_congr rfl (fun j _ => hdiag i j)]
      simp
    have hn : (n : ℝ) ≠ 0 := by
      have : 0 < n := Fin.pos i
      exact_mod_cast this.ne'
    rw [htr]
    field_simp
  · intro Y hY i j
    obtain ⟨φ, hφ⟩ := hT i j
    have := congrFun (congrFun (hY φ i) (φ i)) i
    rw [gle_R_mul, gle_mul_R] at this
    simp only [RelIso.symm_apply_apply] at this
    rw [← hφ]
    exact this
