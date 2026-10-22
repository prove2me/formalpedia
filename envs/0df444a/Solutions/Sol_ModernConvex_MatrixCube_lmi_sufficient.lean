-- Prove2me | solution 1 for ModernConvex.MatrixCube.lmi_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:22:16.538734+00:00
-- url     : https://prove2.me/submissions/98818362-77d8-4f93-9655-560690430be3

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix
open ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Proposition 4.4.5, p. 190: for matrices `A₀, A₁, …, A_m ∈ Sⁿ` with
`A₀ ⪰ 0` and a level `ρ ≥ 0` (the data of the problem Matrix Cube), if the system of LMIs
`(S_ρ)`: `Xⁱ ⪰ ρAᵢ, Xⁱ ⪰ −ρAᵢ (i = 1, …, m), ∑ᵢ Xⁱ ⪯ A₀` is solvable in `X¹, …, Xᵐ ∈ Sⁿ`, then
`𝒜_ρ ⊂ Sⁿ₊`. -/
theorem solution {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA₀ : A₀.PosSemidef) (hA : ∀ i, (A i).IsHermitian)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hS : SystemSolvable A₀ A ρ) :
    CubeInPSD A₀ A ρ := by
  obtain ⟨X, hXh, hX, hsum⟩ := hS
  intro B hB
  obtain ⟨z, hz, rfl⟩ := hB
  have hherm : (A₀ + ∑ i, z i • A i).IsHermitian := by
    refine hA₀.1.add ?_
    refine (isSelfAdjoint_sum (Finset.univ : Finset (Fin m)) (fun i _ => ?_) : IsSelfAdjoint (∑ i, z i • A i))
    exact IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (hA i)
  refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  simp only [star_trivial]
  have h0 := hsum.dotProduct_mulVec_nonneg x
  simp only [star_trivial, sub_mulVec, dotProduct_sub, sum_mulVec, dotProduct_sum] at h0
  have hi : ∀ i, 0 ≤ x ⬝ᵥ (X i *ᵥ x) + z i * (x ⬝ᵥ (A i *ᵥ x)) := by
    intro i
    have h1 := (hX i).1.dotProduct_mulVec_nonneg x
    have h2 := (hX i).2.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul] at h1 h2
    have hzi := hz i
    rw [abs_le] at hzi
    rcases le_total 0 (x ⬝ᵥ (A i *ᵥ x)) with ha | ha
    · nlinarith
    · nlinarith
  rw [add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum]
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib] at this
  linarith

