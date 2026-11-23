-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.chr_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:34.445292+00:00
-- url     : https://prove2.me/submissions/212de807-8011-4cba-b773-441baef8f609

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
theorem _root_.solution (t : Multiplicative X →* U) : chr v (fun i => t (Multiplicative.ofAdd (v i))) = t := by
  refine MonoidHom.ext fun χ => ?_
  rw [chr_apply]
  conv_rhs => rw [← ofAdd_toAdd χ, ← v.sum_repr χ.toAdd, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow]
end GlobalTheory.Ex.QStr
