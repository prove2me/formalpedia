-- Prove2me | solution 1 for GlobalTheory.PDivGroup.conv_eq_one_of_forall_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:31:51.33632+00:00
-- url     : https://prove2.me/submissions/b7220d2b-f780-4157-898a-180dd61c4fed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_TateFree_eq_of_forall_pts
import Theorems.Thm_GlobalTheory_PDivGroup_tateLevel_apply
import Theorems.Thm_GlobalTheory_PDivGroup_pt_surjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT


attribute [local simp] GlobalTheory.PDivGroup.tateLevel_apply

set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (χ : G.dual.Tate) (n : ℕ)
    (h : ∀ t : G.Tate, muRoot (pairing G O t χ) n = 1) : χ.conv n = 1 := by
  have h1 : charElem χ n = charElem (0 : G.dual.Tate) n := eq_of_forall_pts O C _ fun x => by
    obtain ⟨t, rfl⟩ := G.pt_surjective C n x
    rw [charElem_zero, map_one, ← muRoot_pairing, h]
  exact ofConv_injective <| AlgHom.ext fun φ =>
    (apply_charElem χ n φ).symm.trans <| (congrArg φ.ofConv h1).trans (apply_charElem 0 n φ)
end GlobalTheory.PDivGroup
