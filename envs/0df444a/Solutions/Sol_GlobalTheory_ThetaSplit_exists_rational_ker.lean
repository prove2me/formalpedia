-- Prove2me | solution 1 for GlobalTheory.ThetaSplit.exists_rational_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:49.967966+00:00
-- url     : https://prove2.me/submissions/484d6b16-5bb7-44b4-ae6f-d7673d8aeb9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
import Theorems.Thm_GlobalTheory_ThetaSplit_exists_rational

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit
namespace GlobalTheory.ThetaSplit
theorem _root_.solution {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] {A B : Over (Sp k)} [GrpObj B]
    (ψ : A ⟶ B) [IsFinite ψ.left] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A) (hx : x ≫ ψ = 1) :
    ∃ c : 𝟙_ (Over (Sp k)) ⟶ A, c ≫ ψ = 1 ∧ x = toUnit _ ≫ c := by
  let o : Sp k ⟶ B.left := η[B].left
  have w : x.left ≫ ψ.left = t ≫ o := congrArg (fun q => q.left) hx
  obtain ⟨c, hc, hy⟩ := exists_rational (pullback.snd ψ.left o) (pullback.lift x.left t w)
  rw [pullback.lift_snd] at hy
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have h₁ : (c ≫ pullback.fst ψ.left o) ≫ ψ.left = o := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hc, Category.id_comp]
  refine ⟨Over.homMk (c ≫ pullback.fst ψ.left o) (by
    show (c ≫ pullback.fst ψ.left o) ≫ A.hom = 𝟙 _
    rw [← Over.w ψ, ← Category.assoc, h₁, ho]), Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_⟩
  · exact h₁.trans (Category.id_comp _).symm
  · show x.left = t ≫ c ≫ pullback.fst ψ.left o
    rw [← Category.assoc, hy, pullback.lift_fst]
end GlobalTheory.ThetaSplit
