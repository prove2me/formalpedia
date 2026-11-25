-- Prove2me | solution 1 for GlobalTheory.CechCmp.toCech_toPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:59:38.976393+00:00
-- url     : https://prove2.me/submissions/e01bbc4c-a5f4-4db1-9beb-8080395fd8cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetToCechCechToPosetCocycleEq
import Theorems.Thm_GlobalTheory_CechCmp_NE_pt_mem
import Theorems.Thm_GlobalTheory_CechCmp_NE_pt_single
import Theorems.Thm_GlobalTheory_CechCmp_NE_set_pair
import Theorems.Thm_GlobalTheory_CechCmp_cap_le
import Theorems.Thm_GlobalTheory_CechCmp_cap_pair
import Theorems.Thm_GlobalTheory_CechCmp_cv_toPos
import Theorems.Thm_GlobalTheory_CechCmp_toCech_apply
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_KS_rsT_add
import Theorems.Thm_GlobalTheory_KS_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_rsT_self
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option autoImplicit false
open GlobalTheory GlobalTheory.CechCmp
namespace GlobalTheory.CechCmp
theorem _root_.solution : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toCech s U hU hinf (toPos s U hU hinf c) = c := by
  intro I _ X R _ s U hU hinf c hc
  funext i j
  rw [toCech_apply, cv_toPos, cv_toPos]
  simp only [unop_op]
  rw [NE.pt_single, NE.pt_single]
  have hk : (NE.pair i j).pt = i ∨ (NE.pair i j).pt = j := by
    have := NE.pt_mem (NE.pair i j)
    rw [NE.set_pair] at this
    simpa using this
  have hi : i ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hj : j ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hcap : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  rw [GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hi) (cap_le U (NE.pt_mem _))) hcap,
    GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hj) (cap_le U (NE.pt_mem _))) hcap]
  generalize (NE.pair i j).pt = k at hk ⊢
  have hle : U i ⊓ U j ≤ U i ⊓ U j ⊓ U k := by
    refine le_inf le_rfl ?_
    rcases hk with h | h <;> subst h
    exacts [inf_le_left, inf_le_right]
  have h := congrArg (fun t => rsT t (U i ⊓ U j)) (hc i j k)
  simp only [GlobalTheory.KS.rsT_add] at h
  have e₁ : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := inf_le_inf_right _ inf_le_right
  have e₂ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := inf_le_inf_right _ inf_le_left
  rw [GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_self, GlobalTheory.KS.rsT_rsT e₁ hle, GlobalTheory.KS.rsT_rsT e₂ hle] at h
  rw [← h]
  abel
end GlobalTheory.CechCmp
