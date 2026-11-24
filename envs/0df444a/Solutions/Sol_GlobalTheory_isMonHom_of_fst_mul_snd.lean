-- Prove2me | solution 1 for GlobalTheory.isMonHom_of_fst_mul_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:04:48.743802+00:00
-- url     : https://prove2.me/submissions/1175c444-46bb-4142-8c7a-564360d1e7fa

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GrpHomAlgebraisationOfReductions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (g : A ⟶ B)
    (h : (fst A A * snd A A) ≫ g = (fst A A ≫ g) * (snd A A ≫ g)) : IsMonHom g := by
  have hm : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ g = (x ≫ g) * (y ≫ g) := fun T x y => by
    have := congrArg (lift x y ≫ ·) h
    simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd] using this
  refine ⟨?_, ?_⟩
  · have h1 := hm (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S) ⟶ A) ≫ g = 1 := left_eq_mul.1 h1
    simpa [Hom.one_def] using h2
  · have e : (fst A A * snd A A) = μ[A] := by simp [Hom.mul_def]
    rw [e] at h
    rw [h, Hom.mul_def]
    congr 1
end GlobalTheory
