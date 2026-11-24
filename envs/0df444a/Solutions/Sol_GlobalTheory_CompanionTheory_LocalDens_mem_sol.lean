-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.mem_sol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:59.903531+00:00
-- url     : https://prove2.me/submissions/7ca5049a-3e50-43d6-8692-769edda11fd3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gb_red

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R) (k : ℕ) (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    y ∈ sol σ ϖ S T k ↔ gb σ ϖ S k y = red ϖ k T := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [gb_red hσ]
    exact hx
  · intro h
    exact ⟨_, h, Function.surjInv_eq _ _⟩
end GlobalTheory.CompanionTheory.LocalDens
