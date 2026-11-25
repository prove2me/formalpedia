-- Prove2me | solution 1 for GlobalTheory.DetCompare.comb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:27:36.871869+00:00
-- url     : https://prove2.me/submissions/e114d692-5c0d-459a-a6f1-d6bac306b9b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
import Theorems.Thm_GlobalTheory_DetCompare_lieEquiv_comb
import Theorems.Thm_GlobalTheory_DetCompare_mem_eigenspace_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DetCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit
variable {S : Scheme.{0}} {k : Type} [Field k]
variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]
variable [IsCommMonObj G]
namespace GlobalTheory.DetCompare
theorem _root_.solution {act : OAct O G} {t : Sp k ⟶ S} {τ : O →+* k} {n : ℕ} {v : Fin n → Lie G t}
    (hv : ∀ i, v i ∈ eigenspace act t τ) (c : Fin n → k) : comb v c ∈ eigenspace act t τ := by
  rw [mem_eigenspace_iff, lieEquiv_comb]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((mem_eigenspace_iff act t τ _).1 (hv i))
end GlobalTheory.DetCompare
