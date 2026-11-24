-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.base_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:22.639911+00:00
-- url     : https://prove2.me/submissions/c1f30a23-c06f-4ac7-a361-b2abcb1851a7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_adjoin_int_mem

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
theorem _root_.solution (L : Subfield (GenField Ω r)) {κ : Type} (x : κ → Ω) (c₀ : κ)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hgen : ∀ j, algebraMap Ω (GenField Ω r) (x j / x c₀) ∈ L) (b : Ω) :
    algebraMap Ω (GenField Ω r) b ∈ L := by
  have hgen' : ∀ b ∈ (Set.range fun j => x j / x c₀), b ∈ L.comap (algebraMap Ω (GenField Ω r)) := by
    rintro _ ⟨j, rfl⟩
    exact hgen j
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hΩ b
  exact div_mem (adjoin_int_mem _ hgen' hg) (adjoin_int_mem _ hgen' hh)
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
