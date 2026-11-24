-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.mem_of_ratio_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:27.63306+00:00
-- url     : https://prove2.me/submissions/6c97a99f-842e-41d7-a0f2-eff6a1a2453e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_ratio_update
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_genU_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_mem_of_genU_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_base_mem

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
theorem _root_.solution [Fintype S] (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) (c₀ : κ) (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (B : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : ∀ s, B s * Matrix.of (fun j l => φ s j (c s l)) = 1)
    (ρ : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
    (hρ : ∀ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det ≠ 0)
    (L : Subfield (GenField Ω r))
    (hratio : ∀ j : FlagIx κ n r, flagCoord κ x φ c j / flagCoord κ x φ c (c₀, ρ) ∈ L)
    (a : GenField Ω r) : a ∈ L := by
  classical
  have hxK : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 :=
    (map_ne_zero (algebraMap Ω (GenField Ω r))).2 hx0
  have hP : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => hρ q
  have hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L := by
    refine base_mem L x c₀ hΩ fun j => ?_
    have h := hratio (j, ρ)
    have e : flagCoord κ x φ c (j, ρ) / flagCoord κ x φ c (c₀, ρ) =
        algebraMap Ω (GenField Ω r) (x j / x c₀) := by
      rw [map_div₀]
      exact mul_div_mul_right _ _ hP
    rwa [e] at h
  have hminor : ∀ (q : Σ s, Fin (r s)) (f : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      ((flagMat φ c q.1).submatrix f (Fin.castLE q.2.2)).det /
        ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det ∈ L := by
    intro q f
    have h := hratio (c₀, Function.update ρ q f)
    have e := ratio_update (fun (q : Σ s, Fin (r s)) (g : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) =>
      ((flagMat φ c q.1).submatrix g (Fin.castLE q.2.2)).det) ρ hρ q f _ hxK
    exact e ▸ h
  exact mem_of_genU_mem L hbase (fun s k l hkl => genU_mem L hbase φ c s (B s) (hB s) k l hkl (ρ ⟨s, k⟩)
    (hρ ⟨s, k⟩) (hminor ⟨s, k⟩)) a
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
