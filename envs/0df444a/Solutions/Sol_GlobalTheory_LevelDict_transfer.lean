-- Prove2me | solution 1 for GlobalTheory.LevelDict.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:36.568966+00:00
-- url     : https://prove2.me/submissions/28bd7737-02de-44cb-b6cc-e50286e16952

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict
namespace GlobalTheory.LevelDict
theorem _root_.solution {S S' T T' : Type*} (E : S ≃ S') (G : T ≃ T') {P : T → Prop} {P' : T' → Prop} {Q : S → T → Prop}
    {Q' : S' → T' → Prop} (hP : ∀ t, P' (G t) ↔ P t) (hQ : ∀ s t, Q' (E s) (G t) ↔ Q s t)
    (h : (∀ s, ∃! t, P t ∧ Q s t) ∧ ∀ t, P t → ∃! s, Q s t) :
    (∀ s, ∃! t, P' t ∧ Q' s t) ∧ ∀ t, P' t → ∃! s, Q' s t := by
  refine ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective s
    rw [← G.existsUnique_congr (p := fun t => P t ∧ Q s t) fun t => by rw [hP, hQ]]
    exact h.1 s
  · obtain ⟨t, rfl⟩ := G.surjective t
    rw [← E.existsUnique_congr (p := fun s => Q s t) fun s => by rw [hQ]]
    exact h.2 t ((hP t).1 ht)
end GlobalTheory.LevelDict
