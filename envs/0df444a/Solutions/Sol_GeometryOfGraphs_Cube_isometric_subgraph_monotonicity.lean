-- Prove2me | solution 1 for GeometryOfGraphs.Cube.isometric_subgraph_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:22:46.167741+00:00
-- url     : https://prove2.me/submissions/5e7810bf-c0de-4ec5-b911-5d1722504332

import Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension
open GeometryOfGraphs.Cube

private lemma finite_embedding {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) : ∃ d, EmbedsIsometrically G d := by
  classical
  let e := Fintype.equivFin V
  let φ : V → Fin (Fintype.card V) → ℝ := fun x i => G.dist x (e.symm i)
  refine ⟨Fintype.card V, (fun x => ‖x‖), ?_, φ, ?_⟩
  · exact ⟨norm_nonneg, fun x hx => norm_eq_zero.mp hx,
      fun a x => by simp [norm_smul, Real.norm_eq_abs], norm_add_le⟩
  · intro x y
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      change |(G.dist x (e.symm i) : ℝ) - G.dist y (e.symm i)| ≤ (G.dist x y : ℝ)
      apply abs_le.mpr
      have h1 := hG.dist_triangle (u := x) (v := y) (w := e.symm i)
      have h2 := hG.dist_triangle (u := y) (v := x) (w := e.symm i)
      rw [G.dist_comm (u := y) (v := x)] at h2
      have h1' : (G.dist x (e.symm i) : ℝ) ≤ G.dist x y + G.dist y (e.symm i) := by exact_mod_cast h1
      have h2' : (G.dist y (e.symm i) : ℝ) ≤ G.dist x y + G.dist x (e.symm i) := by exact_mod_cast h2
      constructor <;> linarith
    · have hh := norm_le_pi_norm (φ x - φ y) (e x)
      simpa [φ, Real.norm_eq_abs, G.dist_comm (u := y) (v := x)] using hh

theorem solution {V W : Type*}
    [Fintype V] [Fintype W] (G : SimpleGraph V) (J : SimpleGraph W)
    (hG : G.Connected) (hJ : J.Connected) (f : W → V)
    (hf : ∀ x y, G.dist (f x) (f y) = J.dist x y) :
    isoDim J ≤ isoDim G := by
  obtain ⟨d, hd⟩ := finite_embedding G hG
  have hne : {d : ℕ | EmbedsIsometrically G d}.Nonempty := ⟨d, hd⟩
  have hm : EmbedsIsometrically G (isoDim G) := Nat.sInf_mem hne
  obtain ⟨N, hN, φ, hφ⟩ := hm
  apply Nat.sInf_le
  refine ⟨N, hN, φ ∘ f, ?_⟩
  intro x y
  simpa only [Function.comp_apply, hf] using hφ (f x) (f y)

#print axioms solution
