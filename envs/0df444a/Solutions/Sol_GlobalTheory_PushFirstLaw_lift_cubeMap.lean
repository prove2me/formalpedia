-- Prove2me | solution 1 for GlobalTheory.PushFirstLaw.lift_cubeMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:46.624794+00:00
-- url     : https://prove2.me/submissions/2698fbbb-c460-49e7-857a-b5f0ffc2748e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.PushFirstLaw
namespace GlobalTheory.PushFirstLaw
theorem _root_.solution {S : Scheme.{0}} {G' G T : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m : CubeMap G' G) (a : Fin 3 → (T ⟶ G')) (b : Fin 3 → (T ⟶ G)) (h : ∀ i, (b i).left = (a i).left ≫ m.F) :
    (lift (b 0) (lift (b 1) (b 2))).left = (lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3 := by
  have k : ∀ i : Fin 3, (x3 G' i).left ≫ m.F = m.F3 ≫ (x3 G i).left := fun i => by
    have e := m.psum_comm {i}
    have p : psum G (x3 G) {i} = x3 G i * 1 := by fin_cases i <;> rfl
    have p' : psum G' (x3 G') {i} = x3 G' i * 1 := by fin_cases i <;> rfl
    rwa [p, p', _root_.mul_one, _root_.mul_one] at e
  have la : ∀ i : Fin 3, lift (a 0) (lift (a 1) (a 2)) ≫ x3 G' i = a i := fun i => by
    fin_cases i <;> simp [x3]
  have k' : ∀ i : Fin 3, ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) ≫ (x3 G i).left = (b i).left := fun i => by
    rw [Category.assoc, ← k, ← Category.assoc, ← Over.comp_left, la, h]
  let q : T ⟶ G3 G := Over.homMk ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) (by
    rw [← Over.w (x3 G 0), ← Category.assoc, k', Over.w])
  have hq : ∀ i : Fin 3, q ≫ x3 G i = b i := fun i => Over.OverMorphism.ext (k' i)
  have : lift (b 0) (lift (b 1) (b 2)) = q := by
    refine CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (hq 0).symm) ?_
    rw [lift_snd]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, Category.assoc]; exact (hq 1).symm
    · rw [lift_snd, Category.assoc]; exact (hq 2).symm
  rw [this]
  rfl
end GlobalTheory.PushFirstLaw
