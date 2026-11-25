-- Prove2me | solution 1 for GlobalTheory.DiagDifferent.trace_even_real_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:13.82281+00:00
-- url     : https://prove2.me/submissions/f3ece17e-cc25-4ff5-a779-b76be8cd196a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmFieldHostElementAddConjEqOne
import Theorems.Thm_GlobalTheory_DiagDifferent_trace_conj
import Theorems.Thm_GlobalTheory_DiagDifferent_cmField_host_element_add_conj_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.DiagDifferent
namespace GlobalTheory.DiagDifferent
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (∀ a ∈ I, cc a ∈ I) → cc x = x → ((∀ s ∈ I, cc s = s → ∃ n : ℤ, Algebra.trace ℚ E (x * s) = 2 * n) ↔ ∀ s ∈ I, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) := by
  intro E _ _ _ H I x hI hx
  have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => map_mul _ a b
  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => map_add _ a b
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro h s hs
    have hm : s + cc s ∈ I := Submodule.add_mem (I : Submodule (𝓞 E) E) hs (hI s hs)
    obtain ⟨n, hn⟩ := h (s + cc s) hm (by rw [hadd, hcc, add_comm])
    refine ⟨n, ?_⟩
    have e : x * cc s = cc (x * s) := by rw [hmul, hx]
    rw [mul_add, map_add, e, trace_conj] at hn
    linarith
  · intro h s hs hcs
    have hm : (H.w0 : E) * s ∈ I := Submodule.smul_mem (I : Submodule (𝓞 E) E) H.w0 hs
    obtain ⟨n, hn⟩ := h _ hm
    refine ⟨n, ?_⟩
    have e : x * s = x * ((H.w0 : E) * s) + cc (x * ((H.w0 : E) * s)) := by
      rw [hmul, hmul, hx, hcs]
      linear_combination (-(x * s)) * cmField_host_element_add_conj_eq_one H
    rw [e, map_add, trace_conj, hn]
    ring
end GlobalTheory.DiagDifferent
