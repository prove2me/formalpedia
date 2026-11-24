-- Prove2me | solution 1 for GlobalTheory.PairOp.smul_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:48.861701+00:00
-- url     : https://prove2.me/submissions/09d17e13-8ab2-470b-a9ad-e1445a803dee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_LatPair_Pair_dia_hasVal_one
import Theorems.Thm_GlobalTheory_LatPair_Red_residue_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.PairOp
theorem _root_.solution (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (q : Unif k) (c : 𝓀[k]ˣ) (x : {x : Red L // x ≠ 0}) :
    c • up L q x = up L q ⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩ := by
  obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]))
  have hy : Red.mk L x.1.out = x.1 := Red.mk_out x.1
  have h1 : (up L q x).HasVal (q.inv • ((x.1.out : L) : n → k)) 1 := (up_hasVal_iff L q x _).mpr hy
  have h2 := Pair.dia_hasVal_one (c := c) h1 hs
  have h3 : (up L q ⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩).HasVal
      (q.inv • ((s • x.1.out : L) : n → k)) 1 := by
    rw [up_hasVal_iff, map_smul, hy]
    show s • x.1 = ((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1
    rw [← hs, Red.residue_smul]
  rw [Submodule.coe_smul, smul_comm] at h3
  exact Pair.ext_ker (by rw [Pair.dia_ker, up_ker, up_ker]) h2 h3
end GlobalTheory.PairOp
