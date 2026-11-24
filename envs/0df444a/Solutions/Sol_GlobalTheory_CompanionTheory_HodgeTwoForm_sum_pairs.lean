-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.sum_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:07.291964+00:00
-- url     : https://prove2.me/submissions/3bbc85ea-5d3c-476c-8b9b-94d284012682

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution {N : Type} [AddCommMonoid N] (g : Fin n → Fin n → N) (hd : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + g j i) := by
  have h1 : ∀ i, ∑ j, g i j = ∑ j ∈ Finset.Ioi i, g i j + ∑ j ∈ Finset.Iio i, g i j := by
    intro i
    have e : (Finset.univ : Finset (Fin n)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [e, Finset.sum_union, Finset.sum_union]
    · simp [hd]
    · simp
    · rw [Finset.disjoint_left]; intro j; simp only [Finset.mem_Ioi, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_Iio]; omega
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm' (by simp)
end GlobalTheory.CompanionTheory.HodgeTwoForm
