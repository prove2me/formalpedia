-- Prove2me | solution 1 for GlobalTheory.ArcInTest.mem_of_pow_eq_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:46.566661+00:00
-- url     : https://prove2.me/submissions/0a9301e3-4236-4d44-98ce-d50db056e66a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfPowEqInt
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArcInTest
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
namespace GlobalTheory.ArcInTest
theorem _root_.solution {F : Type} [Field F] (V : ValuationSubring F) (x : F) (n : ℕ) (hn : 0 < n) (m : ℤ)
    (h : x ^ n = m) : x ∈ V := by
  have hi : IsIntegral V x := by
    refine IsIntegral.of_pow hn ?_
    rw [h]
    simpa using isIntegral_algebraMap (R := V) (A := F) (x := (m : V))
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 hi
  exact hy ▸ y.2
end GlobalTheory.ArcInTest
