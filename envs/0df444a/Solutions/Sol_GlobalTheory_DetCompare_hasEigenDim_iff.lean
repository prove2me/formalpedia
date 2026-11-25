-- Prove2me | solution 1 for GlobalTheory.DetCompare.hasEigenDim_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:49.318844+00:00
-- url     : https://prove2.me/submissions/09b0195a-49a1-4358-a017-a2731c456153

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
import Theorems.Thm_GlobalTheory_DetCompare_exists_bijOn_iff
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
theorem _root_.solution (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    HasEigenDim act t τ n ↔ Module.Finite k (eigenSub (TanSp.act t act) τ) ∧
      Module.finrank k (eigenSub (TanSp.act t act) τ) = n := by
  rw [← exists_bijOn_iff]
  refine (Equiv.piCongrRight fun _ => lieEquiv t).exists_congr fun v => and_congr
    (forall_congr' fun i => mem_eigenspace_iff act t τ _) ?_
  have h1 : (fun c : Fin n → k => ∑ i, c i • (Equiv.piCongrRight fun _ => lieEquiv t) v i) =
      lieEquiv t ∘ comb v := funext fun c => (lieEquiv_comb v c).symm
  have h2 : Set.BijOn (lieEquiv t) (eigenspace act t τ) (eigenSub (TanSp.act t act) τ) :=
    (lieEquiv t).bijOn (mem_eigenspace_iff act t τ · |>.symm)
  rw [h1]
  refine ⟨h2.comp, fun h => ?_⟩
  have := ((lieEquiv t).bijOn_symm.2 h2).comp h
  rwa [← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp] at this
end GlobalTheory.DetCompare
