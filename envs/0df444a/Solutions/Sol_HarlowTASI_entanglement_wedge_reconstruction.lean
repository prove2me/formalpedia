-- Prove2me | solution 1 for HarlowTASI.entanglement_wedge_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-20T21:07:06.024957+00:00
-- url     : https://prove2.me/submissions/11c60e41-a950-45e2-9989-fe5bb9de0f58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
import Theorems.Thm_HarlowTASI_ewr_duality_imp_rt
import Theorems.Thm_HarlowTASI_ewr_rt_imp_jlms
import Theorems.Thm_HarlowTASI_ewr_jlms_imp_duality

open Matrix
open scoped Kronecker
open HarlowTASI

/-- Theorem 5.2 via the cycle of implications (1) ⇒ (2) ⇒ (3) ⇒ (1). -/
theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U) :
    List.TFAE
      [ ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
          ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
            (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
            (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
            ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
            ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ,
        ∃ L ∈ M ⊓ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
          ∀ ρ : Matrix C C ℂ, IsDensityMatrix ρ →
            ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
                (ρ * L).trace + ((algebraicEntropyLeft U ρ : ℝ) : ℂ) ∧
            ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
                (ρ * L).trace + ((algebraicEntropyRight U ρ : ℝ) : ℂ),
        ∀ ρ σ : Matrix C C ℂ, IsDensityMatrix ρ → IsDensityMatrix σ →
          relativeEntropy (traceRight (V * ρ * Vᴴ)) (traceRight (V * σ * Vᴴ)) =
              algebraicRelEntropyLeft U ρ σ ∧
          relativeEntropy (traceLeft (V * ρ * Vᴴ)) (traceLeft (V * σ * Vᴴ)) =
              algebraicRelEntropyRight U ρ σ ] := by
  tfae_have 1 → 2 := ewr_duality_imp_rt V hV M N dr drb U hU hMU
  tfae_have 2 → 3 := ewr_rt_imp_jlms V hV M N dr drb U hU hMU
  tfae_have 3 → 1 := ewr_jlms_imp_duality V hV M N dr drb U hU hMU
  tfae_finish
