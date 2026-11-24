-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:37:39.580477+00:00
-- url     : https://prove2.me/submissions/eea14244-9107-4be1-a81a-cb09958f4d3d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.NuDiag
namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag
theorem _root_.solution {A : Type} [CommRing A] {n : ℕ} (e : Fin n → A) :
    Nat.card (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      ∏ i : Fin n, Nat.card (Set.range fun w : A => w * e i) := by
  have hset : (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      Set.pi Set.univ (fun i => Set.range fun w : A => w * e i) := by
    ext v
    simp only [Set.mem_range, Set.mem_univ_pi]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨z i, by rw [Matrix.vecMul_diagonal]⟩
    · intro hv
      choose z hz using hv
      exact ⟨z, funext fun i => by rw [Matrix.vecMul_diagonal, hz i]⟩
  rw [hset, Nat.card_congr (Equiv.Set.univPi _), Nat.card_pi]
end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
