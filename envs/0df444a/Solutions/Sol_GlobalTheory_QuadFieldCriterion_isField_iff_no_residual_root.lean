-- Prove2me | solution 1 for GlobalTheory.QuadFieldCriterion.isField_iff_no_residual_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:03:07.740882+00:00
-- url     : https://prove2.me/submissions/fc548d80-35ed-4786-85a2-cf058b0d5a1d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldIffNoResidualRoot
import Theorems.Thm_GlobalTheory_QuadFieldCriterion_exists_root_of_residual
import Theorems.Thm_GlobalTheory_QuadFieldCriterion_exists_root_of_fraction
import Theorems.Thm_GlobalTheory_QuadFieldCriterion_isField_iff_no_root
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
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
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.QuadFieldCriterion
open Polynomial IsLocalRing
namespace GlobalTheory.QuadFieldCriterion
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (A : Type) [CommRing A] [Algebra (Fv F v) A] (w : A) (t n : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → w ^ 2 - algebraMap (Fv F v) A t * w + algebraMap (Fv F v) A n = 0 → (∀ z : A, ∃ a b : Fv F v, z = algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w) → (∀ a b : Fv F v, algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w = 0 → a = 0 ∧ b = 0) → (IsField A ↔ ¬ ∃ r : IsLocalRing.ResidueField (v.adicCompletionIntegers F), r ^ 2 - IsLocalRing.residue (v.adicCompletionIntegers F) t * r + IsLocalRing.residue (v.adicCompletionIntegers F) n = 0) := by
  intro F _ _ v A _ _ w t n hd hw hspan hind
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  rw [isField_iff_no_root w _ _ hw hspan hind]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := exists_root_of_fraction (K := Fv F v) t n x hx
    exact ⟨residue _ s, by simpa using congrArg (residue _) hs⟩
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := exists_root_of_residual t n hd r hr
    exact ⟨(s : Fv F v), by
      simpa using congrArg (algebraMap (v.adicCompletionIntegers F) (Fv F v)) hs⟩
end GlobalTheory.QuadFieldCriterion
