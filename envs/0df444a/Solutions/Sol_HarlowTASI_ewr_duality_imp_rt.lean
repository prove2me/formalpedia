-- Prove2me | solution 1 for HarlowTASI.ewr_duality_imp_rt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-26T20:29:59.695304+00:00
-- url     : https://prove2.me/submissions/fc2dd1eb-99e7-4f9a-8f77-b36409640dfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
import Theorems.Thm_HarlowTASI_ewr_duality_imp_factorization
import Theorems.Thm_HarlowTASI_factorizedCode_entropy
import Theorems.Thm_HarlowTASI_vonNeumannEntropy_mul_conjTranspose_comm
import Theorems.Thm_HarlowTASI_blockAlgebraLeft_inter_right
import Theorems.Thm_HarlowTASI_centralizer_blockAlgebraLeft

open Matrix
open scoped Kronecker
open HarlowTASI

/-- (1) ⇒ (2) of Theorem 5.2: subregion duality factorizes the code (Harlow's structure
theorem), and in a factorized code the RT formula holds with the central area operator
`L = U† (⊕_α S(χ_α,R₂) I_α) U`. -/
theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U)
    (h : ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
          (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
          (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ) :
    ∃ L ∈ M ⊓ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∀ ρ : Matrix C C ℂ, IsDensityMatrix ρ →
          ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
              (ρ * L).trace + ((algebraicEntropyLeft U ρ : ℝ) : ℂ) ∧
          ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
              (ρ * L).trace + ((algebraicEntropyRight U ρ : ℝ) : ℂ) := by
  obtain ⟨m, mb, χ, WR, WRb, hWR, hWRb, hχ, hVU⟩ :=
    ewr_duality_imp_factorization V hV M N dr drb U hU hMU h
  have hcomm : ∀ a, vonNeumannEntropy ((χ a)ᴴ * χ a) = vonNeumannEntropy (χ a * (χ a)ᴴ) :=
    fun a => (vonNeumannEntropy_mul_conjTranspose_comm (χ a)).symm
  set c : Fin N → ℂ := fun a => ((vonNeumannEntropy (χ a * (χ a)ᴴ) : ℝ) : ℂ) with hc
  have hcen : Uᴴ * blockScalarOp (dr := dr) (drb := drb) c * U ∈
      blockAlgebraLeft U ∩ blockAlgebraRight U := by
    rw [blockAlgebraLeft_inter_right U hU]; exact ⟨c, rfl⟩
  refine ⟨Uᴴ * blockScalarOp (dr := dr) (drb := drb) c * U, ?_, fun ρ hρ => ?_⟩
  · refine StarSubalgebra.mem_inf.2 ⟨?_, ?_⟩
    · show _ ∈ (M : Set (Matrix C C ℂ))
      rw [hMU]; exact hcen.1
    · rw [StarSubalgebra.mem_centralizer_iff]
      have hz : Uᴴ * blockScalarOp (dr := dr) (drb := drb) c * U ∈
          Set.centralizer (blockAlgebraLeft U) := by
        rw [centralizer_blockAlgebraLeft U hU]; exact hcen.2
      rw [Set.mem_centralizer_iff] at hz
      intro g hg
      have hg' : g ∈ blockAlgebraLeft U := by rw [← hMU]; exact hg
      have hsg : star g ∈ blockAlgebraLeft U := by
        rw [← hMU]; exact star_mem (show g ∈ M from hg)
      exact ⟨hz g hg', hz (star g) hsg⟩
  · obtain ⟨h1, h2⟩ :=
      factorizedCode_entropy V N dr drb U hU m mb χ WR WRb hWR hWRb hχ hVU ρ hρ
    refine ⟨h1, ?_⟩
    simpa only [hcomm] using h2
