-- Prove2me | solution 1 for GlobalTheory.SecondPartialLaw.prod_cube3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:38.31156+00:00
-- url     : https://prove2.me/submissions/d7567e33-316a-4865-9f80-8b7d3afab339

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
noncomputable section
open GlobalTheory GlobalTheory.SecondPartialLaw
namespace GlobalTheory.SecondPartialLaw
theorem _root_.solution {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 3 → (T ⟶ G)) :
    ∏ I : thK, h (psum G xs I.down) ^ thε I =
      (h 1)⁻¹ * h (xs 0 * 1) * h (xs 1 * 1) * h (xs 2 * 1) * (h (xs 0 * (xs 1 * 1)))⁻¹ * (h (xs 0 * (xs 2 * 1)))⁻¹ *
        (h (xs 1 * (xs 2 * 1)))⁻¹ * h (xs 0 * (xs 1 * (xs 2 * 1))) := by
  refine (Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _
    (fun I : Finset (Fin 3) => h (psum G xs I) ^ thε ⟨I⟩) (fun _ => rfl)).trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have c0 : thε (⟨∅⟩ : thK) = -1 := rfl
  have c1 : thε (⟨{0}⟩ : thK) = 1 := rfl
  have c2 : thε (⟨{1}⟩ : thK) = 1 := rfl
  have c3 : thε (⟨{2}⟩ : thK) = 1 := rfl
  have c4 : thε (⟨{0, 1}⟩ : thK) = -1 := rfl
  have c5 : thε (⟨{0, 2}⟩ : thK) = -1 := rfl
  have c6 : thε (⟨{1, 2}⟩ : thK) = -1 := rfl
  have c7 : thε (⟨{0, 1, 2}⟩ : thK) = 1 := rfl
  have p0 : psum G xs ∅ = 1 := rfl
  have p1 : psum G xs {0} = xs 0 * 1 := rfl
  have p2 : psum G xs {1} = xs 1 * 1 := rfl
  have p3 : psum G xs {2} = xs 2 * 1 := rfl
  have p4 : psum G xs {0, 1} = xs 0 * (xs 1 * 1) := rfl
  have p5 : psum G xs {0, 2} = xs 0 * (xs 2 * 1) := rfl
  have p6 : psum G xs {1, 2} = xs 1 * (xs 2 * 1) := rfl
  have p7 : psum G xs {0, 1, 2} = xs 0 * (xs 1 * (xs 2 * 1)) := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7, p0, p1, p2, p3, p4, p5, p6, p7]
  simp only [zpow_one, zpow_neg, _root_.mul_assoc]
end GlobalTheory.SecondPartialLaw
