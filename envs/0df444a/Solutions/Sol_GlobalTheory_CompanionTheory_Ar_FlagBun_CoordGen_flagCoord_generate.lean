-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:47.80824+00:00
-- url     : https://prove2.me/submissions/77399b79-0dea-4a47-b145-daf0446736bb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_exists_div_of_mem_closure
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_exists_minor_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_mem_of_ratio_mem

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
theorem _root_.solution (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S]
    (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ)
    (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r,
      ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
        h ≠ 0 ∧ a = g / h := by
  classical
  choose B hB using hB
  have hne : ∀ q : (Σ s, Fin (r s)), ∃ f : Fin ((q.2 : ℕ) + 1) → Fin (n q.1),
      ((flagMat φ c q.1).submatrix f (Fin.castLE q.2.2)).det ≠ 0 :=
    fun q => exists_minor_ne_zero φ c q.1 (B q.1) (hB q.1) q.2
  choose ρ hρ using hne
  have hF0 : flagCoord κ x φ c (c₀, ρ) ≠ 0 :=
    mul_ne_zero ((map_ne_zero (algebraMap Ω (GenField Ω r))).2 hx0)
      (Finset.prod_ne_zero_iff.2 fun q _ => hρ q)
  refine ⟨(c₀, ρ), hF0, fun a => ?_⟩
  apply exists_div_of_mem_closure
  exact mem_of_ratio_mem κ x φ c c₀ hx0 hΩ B hB ρ hρ (Subfield.closure _)
    (fun j => Subfield.subset_closure (Set.mem_range_self j)) a
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
