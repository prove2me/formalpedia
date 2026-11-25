-- Prove2me | solution 1 for GlobalTheory.CMLattice.exists_basis_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:43.712803+00:00
-- url     : https://prove2.me/submissions/bc2c680e-aa1a-472e-91de-fb4f44984289

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Theorems.Thm_GlobalTheory_CMLattice_exists_basis_of_cmType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMLattice
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) :
    ∃ b : Module.Basis (Fin (2 * (X.Ψ.card * r))) ℝ (X.Ψ → Fin r → ℂ),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔
        ∃ v ∈ X.Λ, (fun τ : X.Ψ => Data.emb τ.1 v) = y :=
  exists_basis_of_cmType X.Ψ X.cmType r X.Λ X.Λ_fg X.Λ_span
end GlobalTheory.CMLattice
