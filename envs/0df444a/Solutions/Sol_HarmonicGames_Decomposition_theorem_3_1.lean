-- Prove2me | solution 1 for HarmonicGames.Decomposition.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T04:11:48.066221+00:00
-- url     : https://prove2.me/submissions/c66d174a-c326-4ea6-93d3-d9165e72f852

import Definitions.Def_HarmonicGames_Decomposition_Flows

open HarmonicGames.Decomposition
open scoped InnerProductSpace

private lemma curl_grad {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : C0 V) :
    delta1 G (delta0 G x) = 0 := by
  ext p q r
  change (if IsTriangle G p q r then
    (delta0 G x) p q + (delta0 G x) q r + (delta0 G x) r p else 0) = 0
  by_cases h : IsTriangle G p q r
  · obtain ⟨hpq, hqr, hpr⟩ := h
    simp only [if_pos (show IsTriangle G p q r from ⟨hpq, hqr, hpr⟩)]
    change (if G.Adj p q then 1 else 0) * (x q - x p) +
      (if G.Adj q r then 1 else 0) * (x r - x q) +
      (if G.Adj r p then 1 else 0) * (x p - x r) = 0
    simp only [if_pos hpq, if_pos hqr, if_pos hpr.symm, one_mul]
    ring
  · simp only [if_neg h]

private lemma harmonic_kernel {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    LinearMap.ker (Delta1 G) =
      LinearMap.ker (delta1 G) ⊓ LinearMap.ker (LinearMap.adjoint (delta0 G)) := by
  ext x
  change Delta1 G x = 0 ↔ delta1 G x = 0 ∧ (delta0 G).adjoint x = 0
  constructor
  · intro hx
    have he := congrArg (fun y => inner ℝ y x) hx
    simp only [Delta1, LinearMap.add_apply, LinearMap.comp_apply, inner_add_left,
      inner_zero_left] at he
    rw [LinearMap.adjoint_inner_left,
      ← LinearMap.adjoint_inner_right (delta0 G)] at he
    have ha := inner_self_nonneg (𝕜 := ℝ) (x := delta1 G x)
    have hb := inner_self_nonneg (𝕜 := ℝ) (x := (delta0 G).adjoint x)
    simp only [RCLike.re_to_real] at ha hb
    exact ⟨(inner_self_eq_zero (𝕜 := ℝ)).mp (by linarith),
      (inner_self_eq_zero (𝕜 := ℝ)).mp (by linarith)⟩
  · rintro ⟨ha, hb⟩
    simp [Delta1, ha, hb]

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (LinearMap.range (delta0 G)).IsOrtho (LinearMap.ker (Delta1 G)) ∧
    (LinearMap.range (delta0 G)).IsOrtho (LinearMap.range (LinearMap.adjoint (delta1 G))) ∧
    (LinearMap.ker (Delta1 G)).IsOrtho (LinearMap.range (LinearMap.adjoint (delta1 G))) ∧
    LinearMap.range (delta0 G) ⊔ LinearMap.ker (Delta1 G) ⊔
        LinearMap.range (LinearMap.adjoint (delta1 G)) = ⊤ ∧
    LinearMap.ker (Delta1 G) =
      LinearMap.ker (delta1 G) ⊓ LinearMap.ker (LinearMap.adjoint (delta0 G)) := by
  have hsub : LinearMap.range (delta0 G) ≤ LinearMap.ker (delta1 G) := by
    rintro _ ⟨x, rfl⟩
    exact curl_grad G x
  refine ⟨?_, ?_, ?_, ?_, harmonic_kernel G⟩
  · rw [harmonic_kernel, inf_comm, ← LinearMap.orthogonal_range]
    exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left
  · rw [Submodule.isOrtho_iff_le, LinearMap.orthogonal_range,
      LinearMap.adjoint_adjoint]
    exact hsub
  · rw [Submodule.isOrtho_iff_le, LinearMap.orthogonal_range,
      LinearMap.adjoint_adjoint, harmonic_kernel]
    exact inf_le_left
  · rw [harmonic_kernel, inf_comm, ← LinearMap.orthogonal_range,
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hsub,
      ← LinearMap.orthogonal_ker]
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

#print axioms solution
