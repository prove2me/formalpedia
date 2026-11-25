-- Prove2me | solution 1 for GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:51.995559+00:00
-- url     : https://prove2.me/submissions/183b1cc2-8d55-47f1-a0a0-b57be1b1923a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_exists_unitary_factors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_T_exists_norm_eq_X_mod_monic_of_adicComplete_involution
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_GLint_of_unitary
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
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
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitaryDoubleCoset
namespace GlobalTheory.UnitaryDoubleCoset
theorem _root_.solution (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (σ : v.adicCompletion K →+* v.adicCompletion K) (n : ℕ) (hσσ : ∀ x, σ (σ x) = x)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ h ∈ GLint (Fin n) (Ov K v), ∀ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
        g' = k₁ * g * k₂ := by
  rintro g hg g' hg' _ ⟨h, rfl⟩ _ ⟨k, rfl⟩ e
  have := isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
    finite_residueField_adicCompletionIntegers v
  let c : v.adicCompletionIntegers K →+* v.adicCompletionIntegers K :=
    (σ.comp (v.adicCompletionIntegers K).subtype).codRestrict (v.adicCompletionIntegers K) fun x => by
      show Valued.v (σ x) ≤ 1
      rw [hσ]; exact x.2
  have hcv : ∀ x, ((c x : v.adicCompletionIntegers K) : v.adicCompletion K) = σ x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K),
      c x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    obtain ⟨x, hx1, hx2⟩ := hx
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M, hM⟩, e'⟩ :=
    exists_unitary_factors (O := Ov K v) (Ov K v).subtype (c := c) (σ := σ) (fun _ => rfl) hc
      (GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution (v.adicCompletionIntegers K) _ c hc hI hω) hg hg' h k e
  refine ⟨k₁, hk₁, k₂, ⟨hk₂, ?_⟩, e'⟩
  refine GlobalTheory.UnitarySwap.mem_GLint_of_unitary (J := 1) hσ (one_mem _) hk₂ fun i j => ?_
  rw [hM]
  exact (M i j).2
end GlobalTheory.UnitaryDoubleCoset
