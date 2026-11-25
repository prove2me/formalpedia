-- Prove2me | solution 1 for GlobalTheory.CechCmp.toCech_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:30:11.320627+00:00
-- url     : https://prove2.me/submissions/349e8f10-941a-4ef6-8b53-5446da81a0fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Theorems.Thm_GlobalTheory_CechCmp_cap_pair
import Theorems.Thm_GlobalTheory_CechCmp_cv_smul
import Theorems.Thm_GlobalTheory_CechCmp_toCech_apply
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_KS_rsT_constFn
import Theorems.Thm_GlobalTheory_KS_rsT_mul
import Theorems.Thm_GlobalTheory_KS_rsT_sum
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechCmp
variable {I : Type} {X : Scheme.{0}} {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
namespace GlobalTheory.CechCmp
theorem _root_.solution {n : ℕ} (cc : Fin n → R) (f : Fin n → CatCoh.C1 (capF s U hU hinf)) :
    toCech s U hU hinf (∑ a, cc a • f a) =
      fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * toCech s U hU hinf (f a) i j := by
  funext i j
  have hle : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  simp only [toCech_apply, Finset.sum_apply, Pi.smul_apply, map_sum, cv_smul, GlobalTheory.KS.rsT_sum, GlobalTheory.KS.rsT_mul,
    GlobalTheory.KS.rsT_constFn s hle, mul_sub, Finset.sum_sub_distrib]
  refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => ?_) (Finset.sum_congr rfl fun a _ => ?_) <;>
    rw [cv_smul, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn s hle]
end GlobalTheory.CechCmp
