-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exAt_mem_twist_chart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:01:23.694643+00:00
-- url     : https://prove2.me/submissions/58c80cfe-e105-4b80-a1a7-191e3e320c19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff

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
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
namespace GlobalTheory.ThetaFn
theorem _root_.solution {m : T ⊗ A ⟶ A} {z w : Fin g → ℂ}
    (hw : exAt u p z ≫ m.left = (u.ex w).left) (j : Fin 2 → L.ι) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j ↔
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U (j 1) := by
  have h0 : exAt u p z ≫ (snd T A).left = (u.ex z).left := by
    unfold exAt
    rw [← Over.comp_left, lift_snd]
  rw [← h0, ← hw]
  constructor
  · intro h
    refine ⟨fun a _ => ?_, fun a _ => ?_⟩
    · have ha := Set.mem_iInter.1 (h (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)) 0
      simpa using ha
    · have ha := Set.mem_iInter.1 (h (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)) 1
      simpa using ha
  · rintro ⟨h0', h1'⟩ a _
    refine Set.mem_iInter.2 (fun k => ?_)
    fin_cases k
    · simpa using h0' (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    · simpa using h1' (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)
end GlobalTheory.ThetaFn
