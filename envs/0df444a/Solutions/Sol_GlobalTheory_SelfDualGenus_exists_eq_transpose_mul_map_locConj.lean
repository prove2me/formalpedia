-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_eq_transpose_mul_map_locConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:30:02.1296+00:00
-- url     : https://prove2.me/submissions/2c61c63a-b0b2-4e30-88ee-2815c25a6b09

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_isUnit_sub_locOrderConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_locOrderConj_locOrderConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_mem_range_of_locOrderConj_eq
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
variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution {M N : Matrix (Fin r) (Fin r) (LocAlg v)}
    (hM : ∀ i j, M i j ∈ locOrder v) (hN : ∀ i j, N i j ∈ locOrder v) (hMN : M * N = 1)
    (hh : ∀ i j, locConj v (M i j) = M j i) :
    ∃ P : GL (Fin r) (LocAlg v),
      (∀ i j, (P : Matrix (Fin r) (Fin r) (LocAlg v)) i j ∈ locOrder v) ∧
      (∀ i j, ((P⁻¹ : GL (Fin r) (LocAlg v)) : Matrix (Fin r) (Fin r) (LocAlg v)) i j ∈
        locOrder v) ∧
      M = (P : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ *
        (P : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) := by
  haveI := isAdicComplete_adicCompletionIntegers v
  haveI := finite_residueField_adicCompletionIntegers v
  let φ : locOrder v →+* LocAlg v := (locOrder v).val
  let M' : Matrix (Fin r) (Fin r) (locOrder v) := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix (Fin r) (Fin r) (locOrder v) := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have h1 : M' * N' = 1 := by
    apply Matrix.map_injective (f := φ) Subtype.val_injective
    change (M' * N').map φ = Matrix.map 1 φ
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hMN
  obtain ⟨P, hP, h⟩ := UnramifiedHermitian.exists_eq_transpose_mul_map_of_henselian
    (R₀ := v.adicCompletionIntegers (maximalRealSubfield E)) (locOrderConj v) (locOrderConj_locOrderConj v)
    (fun a => Subtype.ext (locConj_algebraMap' v a)) (mem_range_of_locOrderConj_eq v)
    (exists_isUnit_sub_locOrderConj v) (G := M') (fun i j => Subtype.ext (hh i j))
    (Matrix.isUnit_det_of_right_inverse h1)
  obtain ⟨P, rfl⟩ := (Matrix.isUnit_iff_isUnit_det P).2 hP
  refine ⟨Matrix.GeneralLinearGroup.map φ P, fun i j => (P.1 i j).2, fun i j => ?_, ?_⟩
  · rw [← map_inv]; exact ((P⁻¹).1 i j).2
  · have := congrArg (fun X => Matrix.map X φ) h
    simp only [Matrix.map_mul] at this
    exact this
end GlobalTheory.SelfDualGenus
