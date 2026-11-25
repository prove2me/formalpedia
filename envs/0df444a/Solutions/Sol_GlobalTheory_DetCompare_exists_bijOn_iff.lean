-- Prove2me | solution 1 for GlobalTheory.DetCompare.exists_bijOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:20.461361+00:00
-- url     : https://prove2.me/submissions/bf986bbc-f3d6-4a4b-a42b-8a568a708d47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DetCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit
variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]
namespace GlobalTheory.DetCompare
theorem _root_.solution (W : Submodule k N) (n : ℕ) :
    (∃ v : Fin n → N, (∀ i, v i ∈ W) ∧ Set.BijOn (fun c : Fin n → k => ∑ i, c i • v i) Set.univ W) ↔
      Module.Finite k W ∧ Module.finrank k W = n := by
  constructor
  · rintro ⟨v, -, hm, hi, hs⟩
    let f : (Fin n → k) →ₗ[k] W := (Fintype.linearCombination k v).codRestrict W fun c => hm trivial
    have hf : Function.Bijective f := by
      refine ⟨fun c c' h => hi trivial trivial (congrArg Subtype.val h), fun w => ?_⟩
      obtain ⟨c, -, hc⟩ := hs w.2
      exact ⟨c, Subtype.ext hc⟩
    have e := LinearEquiv.ofBijective f hf
    exact ⟨Module.Finite.equiv e, by simpa using e.finrank_eq.symm⟩
  · rintro ⟨_, h⟩
    let b := Module.finBasisOfFinrankEq k W h
    have hb : ∀ c : Fin n → k, ∑ i, c i • (b i : N) = (b.equivFun.symm c : W) := fun c => by
      simp [Module.Basis.equivFun_symm_apply]
    refine ⟨fun i => b i, fun i => (b i).2, fun c _ => ?_, fun c _ c' _ h => ?_, fun w hw => ?_⟩
    · simp only [hb]; exact Subtype.property _
    · simp only [hb] at h; exact b.equivFun.symm.injective (Subtype.ext h)
    · exact ⟨b.equivFun ⟨w, hw⟩, trivial, by simp only [hb, LinearEquiv.symm_apply_apply]⟩
end GlobalTheory.DetCompare
