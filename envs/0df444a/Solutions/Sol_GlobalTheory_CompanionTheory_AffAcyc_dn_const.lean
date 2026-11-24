-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.dn_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:57.862062+00:00
-- url     : https://prove2.me/submissions/904939d2-226d-4b2f-b345-260691679b1e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_apply

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
variable (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (a₀ : P)
  (hb : ∀ T : Pᵒᵖ, Function.Bijective (mp F ((th a₀).app T)))
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (n : ℕ) (z : Cn F n) :
    dn F n z ((Functor.const (Fin (n + 2))).obj (op a₀)) =
      (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) • z ((Functor.const (Fin (n + 1))).obj (op a₀)) := by
  rw [dn_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact mp_id F (op a₀) _
end GlobalTheory.CompanionTheory.AffAcyc
