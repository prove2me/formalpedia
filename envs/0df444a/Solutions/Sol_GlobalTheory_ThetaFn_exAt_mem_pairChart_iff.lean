-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exAt_mem_pairChart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:59.365715+00:00
-- url     : https://prove2.me/submissions/f97dab4e-4fb2-4869-93d8-f48ea41a69db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
namespace GlobalTheory.ThetaFn
theorem _root_.solution {m : T ⊗ A ⟶ A} {z w : Fin g → ℂ}
    (h : exAt u p z ≫ m.left = (u.ex w).left) (j : Fin 2 → L.ι) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j ↔
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U (j 1) := by
  refine (le_preimage_wchart (exAt u p z) L _ j).trans ?_
  rw [Fin.forall_fin_two, ← exAt_snd u p z, ← h]
  rfl
end GlobalTheory.ThetaFn
