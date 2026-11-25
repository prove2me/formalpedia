-- Prove2me | solution 1 for GlobalTheory.DetCompare.lieMult_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:52.795901+00:00
-- url     : https://prove2.me/submissions/009266ef-2ef7-4054-a919-5456a2e2c94b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
import Theorems.Thm_GlobalTheory_DetCompare_isLieEigen_iff
import Theorems.Thm_GlobalTheory_DetCompare_comb_iff
import Theorems.Thm_GlobalTheory_DetCompare_comb_mem

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
    LieMult act t τ n ↔ HasEigenDim act t τ n := by
  constructor
  · rintro ⟨v, hv, h⟩
    choose h1 h2 using fun i => (isLieEigen_iff act t τ _).1 (hv i)
    let v' : Fin n → Lie G t := fun i => ⟨v i, h1 i⟩
    have h' : ∀ w ∈ eigenspace act t τ, ∃! c, w = comb v' c := fun w hw => by
      have := h w.1 ((isLieEigen_iff act t τ _).2 ⟨w.2, hw⟩)
      exact (existsUnique_congr fun c => (comb_iff v' c w.1).trans Subtype.ext_iff.symm).1 this
    refine ⟨v', h2, fun c _ => comb_mem h2 c, fun c _ c' _ e => (h' _ (comb_mem h2 c)).unique rfl e,
      fun w hw => ?_⟩
    obtain ⟨c, hc, -⟩ := h' w hw
    exact ⟨c, trivial, hc.symm⟩
  · rintro ⟨v, hv, -, hi, hs⟩
    refine ⟨fun i => (v i).1, fun i => (isLieEigen_iff act t τ _).2 ⟨(v i).2, hv i⟩, fun w hw => ?_⟩
    obtain ⟨h1, h2⟩ := (isLieEigen_iff act t τ _).1 hw
    obtain ⟨c, -, hc⟩ := hs h2
    refine (existsUnique_congr fun c => comb_iff v c w).2 ⟨c, (congrArg Subtype.val hc).symm, fun c' hc' => ?_⟩
    exact hi trivial trivial ((Subtype.ext hc' : (⟨w, h1⟩ : Lie G t) = comb v c').symm.trans hc.symm)
end GlobalTheory.DetCompare
