-- Prove2me | solution 1 for GlobalTheory.SortedCartan.conj_torusElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:06.530648+00:00
-- url     : https://prove2.me/submissions/5b4f8be4-f901-4e92-88d9-a77356e214b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
import Theorems.Thm_GlobalTheory_SortedCartan_permUnit_val
import Theorems.Thm_GlobalTheory_SmGL_val_diagT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
noncomputable section
open GlobalTheory GlobalTheory.SortedCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SortedCartan
theorem _root_.solution {N : ℕ} (ϖ : kˣ) (m : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    permUnit σ * torusElt k (Fin N) ϖ m * (permUnit σ)⁻¹ = torusElt k (Fin N) ϖ (m ∘ σ) := by
  apply Units.ext
  have hinv : (((permUnit σ : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      σ.symm.toPEquiv.toMatrix := by
    show (σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) = _
    exact PEquiv.map_toMatrix _ _
  rw [Units.val_mul, Units.val_mul, hinv, permUnit_val, torusElt, torusElt, val_diagT, val_diagT,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm,
    Matrix.submatrix_submatrix]
  exact Matrix.submatrix_diagonal_equiv _ σ
end GlobalTheory.SortedCartan
