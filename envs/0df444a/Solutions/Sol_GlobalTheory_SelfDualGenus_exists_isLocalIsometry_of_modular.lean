-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_isLocalIsometry_of_modular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:30.268268+00:00
-- url     : https://prove2.me/submissions/ac6f7bdd-9387-4ea7-9eda-fcf1cd17ecd9

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_generator
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_unit_locConj_mul_eq
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_orthogonal_frame
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {G G' : Matrix (Fin r) (Fin r) E} {L L' : Submodule (𝓞 E) (Fin r → E)}
variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {𝔟 : FractionalIdeal (𝓞 E)⁰ E}
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution (h𝔟 : 𝔟 ≠ 0) (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) (hmod' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G' x y ∈ 𝔟)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ∃ γ, IsLocalIsometry v G L G' L' γ := by
  obtain ⟨b, hb0, hb⟩ := exists_generator v h𝔟
  obtain ⟨ε, hε⟩ := exists_unit_locConj_mul_eq v hc hb0 hb
  obtain ⟨h, h₁, h₂⟩ := exists_orthogonal_frame v hG hd hL hmod hb0 hb ε hε
  obtain ⟨h', h₁', h₂'⟩ := exists_orthogonal_frame v hG' hd' hL' hmod' hb0 hb ε hε
  refine ⟨h * h'⁻¹, ?_, fun x => ?_⟩
  · rw [Units.val_mul, UnramifiedHermitian.congr_mul, h₁, ← h₁', ← UnramifiedHermitian.congr_mul,
      Units.mul_inv]
    simp
  · rw [h₂, h₂', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]
end GlobalTheory.SelfDualGenus
