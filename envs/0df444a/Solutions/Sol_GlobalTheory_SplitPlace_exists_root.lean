-- Prove2me | solution 1 for GlobalTheory.SplitPlace.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:19.836266+00:00
-- url     : https://prove2.me/submissions/1890b22f-76a6-4303-af4d-9cc5b45ef1f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplit
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial
open GlobalTheory GlobalTheory.SplitPlace
namespace GlobalTheory.SplitPlace
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (t n : 𝓞 F) (hn : n ∈ v.asIdeal) (ht : t ∉ v.asIdeal) :
    ∃ r : v.adicCompletion F, r ^ 2 + algebraMap F _ (t : F) * r + algebraMap F _ (n : F) = 0 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set O := v.adicCompletionIntegers F
  obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O)
    (X ^ 2 + C (algebraMap (𝓞 F) O t) * X + C (algebraMap (𝓞 F) O n)) (by monicity!) 0
    (by
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, mul_zero, add_zero]
      rw [zero_pow two_ne_zero, zero_add, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
      exact fun h => h hn)
    (by
      refine IsUnit.map _ ?_
      have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v t).2 ht
      simpa using this)
  refine ⟨r, ?_⟩
  have := congrArg (fun x : O => (x : v.adicCompletion F)) hr
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
  push_cast at this
  exact this
end GlobalTheory.SplitPlace
