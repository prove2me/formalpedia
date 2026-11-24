-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.chr_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:42.188005+00:00
-- url     : https://prove2.me/submissions/80c7114f-0eb0-432c-a487-0ed7cf8f25f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_chr_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {X U ι : Type} [AddCommGroup X] [CommGroup U] [Fintype ι] (v : Module.Basis ι ℤ X)
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (u : ι → U) (i : ι) : chr v u (Multiplicative.ofAdd (v i)) = u i := by
  classical
  rw [chr_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj.symm]
  · simp
end GlobalTheory.Ex.QStr
