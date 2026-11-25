-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Formal.IsoThick.isIso_restrict_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:17.059931+00:00
-- url     : https://prove2.me/submissions/2c00bbe7-6bb1-4518-97d6-c091c8f65a3a

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick
namespace GlobalTheory.CompanionTheory.Formal.IsoThick
theorem _root_.solution {S T : Scheme.{0}} (t : T ⟶ S) (X C : Over S) (p : C ⟶ X)
    (W : X.left.Opens) (g : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ Over.mk (W.ι ≫ X.hom))
    (hg : g.left = p.left ∣_ W) (h : IsIso ((Over.pullback t).map p).left) :
    IsIso ((Over.pullback t).map g).left := by
  let a : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ C := Over.homMk (p.left ⁻¹ᵁ W).ι rfl
  let b : Over.mk (W.ι ≫ X.hom) ⟶ X := Over.homMk W.ι rfl
  have hcomm : a ≫ p = g ≫ b := by
    ext1
    change (p.left ⁻¹ᵁ W).ι ≫ p.left = g.left ≫ W.ι
    rw [hg, morphismRestrict_ι]
  have hsq : IsPullback a g p b :=
    IsPullback.of_map (Over.forget S) hcomm (by
      have h1 := (isPullback_morphismRestrict p.left W).flip
      rw [← hg] at h1
      exact h1)
  have hsq' := hsq.map (Over.pullback t)
  haveI : IsIso ((Over.forget T).map ((Over.pullback t).map p)) := h
  haveI : IsIso ((Over.pullback t).map p) := isIso_of_reflects_iso _ (Over.forget _)
  haveI : IsIso ((Over.pullback t).map g) := hsq'.isIso_snd_of_isIso
  exact inferInstanceAs (IsIso ((Over.forget T).map ((Over.pullback t).map g)))
end GlobalTheory.CompanionTheory.Formal.IsoThick
