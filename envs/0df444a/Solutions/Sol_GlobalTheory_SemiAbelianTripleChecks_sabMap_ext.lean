-- Prove2me | solution 1 for GlobalTheory.SemiAbelianTripleChecks.sabMap_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:41.677931+00:00
-- url     : https://prove2.me/submissions/d97745d0-a2d1-474a-835e-56a997d4de01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_CubeMapTripleProductUnique
import Theorems.Thm_GlobalTheory_SemiAbelianTripleChecks_cubeMap_tripleProduct_unique

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
theorem _root_.solution {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m m' : SABMap t' t f) (h : m.φ = m'.φ) :
    m = m' := by
  obtain ⟨⟨F, F3, e, he, hp⟩, c, b, a, l⟩ := m
  obtain ⟨⟨F', F3', e', he', hp'⟩, c', b', a', l'⟩ := m'
  have h3 : F3 = F3' := cubeMap_tripleProduct_unique ⟨F, F3, e, he, hp⟩ ⟨F', F3', e', he', hp'⟩ h
  have h1 : F = F' := h
  have h2 : e = e' := b.trans b'.symm
  subst h1 h2 h3
  rfl
end GlobalTheory.SemiAbelianTripleChecks
