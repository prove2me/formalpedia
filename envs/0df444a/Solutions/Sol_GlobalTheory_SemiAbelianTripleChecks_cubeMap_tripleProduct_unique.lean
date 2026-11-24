-- Prove2me | solution 1 for GlobalTheory.SemiAbelianTripleChecks.cubeMap_tripleProduct_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:45.213317+00:00
-- url     : https://prove2.me/submissions/4fd8c7c3-4453-40cc-bd87-a33560bb0d97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_CubeMapTripleProductUnique
import Theorems.Thm_GlobalTheory_SemiAbelianTripleChecks_psum_singleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SemiAbelianTripleChecks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
namespace GlobalTheory.SemiAbelianTripleChecks
theorem _root_.solution {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m m' : CubeMap G' G) (h : m.F = m'.F) : m.F3 = m'.F3 := by
  have key : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = m'.F3 ≫ (x3 G i).left := fun i => by
    have h1 := m.psum_comm {i}
    have h2 := m'.psum_comm {i}
    rw [psum_singleton, psum_singleton] at h1 h2
    rw [← h1, ← h2, h]
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  apply pullback.hom_ext
  · exact k0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact k1
    · rw [Category.assoc, Category.assoc]; exact k2
end GlobalTheory.SemiAbelianTripleChecks
