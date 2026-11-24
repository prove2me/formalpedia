-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FirstOrderNbhd.exists_mem_ideal_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:52.806901+00:00
-- url     : https://prove2.me/submissions/52fd811d-2544-4bdb-a412-bc07de8904a8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZero
import Theorems.Thm_GlobalTheory_CompanionTheory_FirstOrderNbhd_comp_app_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FirstOrderNbhd
namespace GlobalTheory.CompanionTheory.FirstOrderNbhd
theorem _root_.solution {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (W : U.affineOpens) (a : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) :
    ∃ a' ∈ e.ker.ideal W, (e.ker ^ 2).subschemeι.app W a' =
      (e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a := by
  obtain ⟨a', ha'⟩ := (e.ker ^ 2).subschemeι_app_surjective W
    ((e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a)
  refine ⟨a', ?_, ha'⟩
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have h0 := comp_app_eq_zero (e.ker ^ 2).subschemeι i' (W : U.Opens) a' a ha' ha
  rw [hi] at h0
  exact h0
end GlobalTheory.CompanionTheory.FirstOrderNbhd
