-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.dn_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:56.756544+00:00
-- url     : https://prove2.me/submissions/a13e0f80-497a-48db-a706-0885f27c64eb

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
theorem _root_.solution (n : ℕ) (t : F.obj (op a₀)) (c : Fin (n + 2) ⥤ Pᵒᵖ) :
    dn F n (E F a₀ hb n t) c = (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) • E F a₀ hb (n + 1) t c := by
  rw [dn_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  have := (m2 F a₀ hb).naturality (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) t
  refine this.symm.trans ?_
  change (m2 F a₀ hb).α _ (mp F (𝟙 (op a₀)) t) = _
  rw [mp_id]
  rfl
end GlobalTheory.CompanionTheory.AffAcyc
