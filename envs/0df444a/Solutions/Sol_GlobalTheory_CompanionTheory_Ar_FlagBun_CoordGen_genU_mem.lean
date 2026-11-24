-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.genU_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:08.308405+00:00
-- url     : https://prove2.me/submissions/6ef994e5-3f10-4598-857b-b3ece7360bda

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_genU_self
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_det_genU_rows
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_det_genU_submatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}
variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) (k l : Fin (r s)) (hkl : k ≤ l)
    (ρ : Fin ((k : ℕ) + 1) → Fin (n s)) (hρ : ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ≠ 0)
    (hminor : ∀ f : Fin ((k : ℕ) + 1) → Fin (n s), ((flagMat φ c s).submatrix f (Fin.castLE k.2)).det /
        ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ∈ L) :
    genU Ω r s l k ∈ L := by
  have hrows : ∀ R : Fin ((k : ℕ) + 1) → Fin (r s),
      ((genU Ω r s).submatrix R (Fin.castLE k.2)).det /
        ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ∈ L := by
    intro R
    rw [det_genU_submatrix φ c s B hB k.2 R, Finset.sum_div]
    refine sum_mem fun f _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (prod_mem fun i _ => hbase _) (hminor f)
  have h1 := hrows (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i)
  rw [det_genU_rows s k l hkl] at h1
  have h0 := hrows (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then k else Fin.castLE k.2 i)
  rw [det_genU_rows s k k le_rfl, genU_self] at h0
  have := div_mem h1 h0
  rwa [div_div_div_cancel_right₀ hρ, div_one] at this
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
