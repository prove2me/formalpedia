-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_orthogonal_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:05.480815+00:00
-- url     : https://prove2.me/submissions/2c08a007-54a4-44c7-bdc4-c28677afb730

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locEmb
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_mem_locOrder_iff
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_frame
import Theorems.Thm_GlobalTheory_SelfDualGenus_gram_mem_semiLoc
import Theorems.Thm_GlobalTheory_SelfDualGenus_gram_inv_mem_semiLoc
import Theorems.Thm_GlobalTheory_SelfDualGenus_mem_locLattice_iff_of_frame
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_eq_transpose_mul_map_locConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_mulVec_mem_locOrder
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_smul_mul
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_Published_cc_ne_zero
import Theorems.Thm_GlobalTheory_Published_det_map_cc
import Theorems.Thm_GlobalTheory_Published_herm_col
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_conj
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
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (hd : G.det ≠ 0) {L : Submodule (𝓞 E) (Fin r → E)} (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L)
    {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟)
    {b : E} (hb0 : b ≠ 0)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v)
    (ε : (locOrder v)ˣ) (hε : locConj v (((ε : locOrder v) : LocAlg v) * locEmb v b) =
      ((ε : locOrder v) : LocAlg v) * locEmb v b) :
    ∃ h : GL (Fin r) (LocAlg v),
      (h : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
        (h : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) =
          (((ε : locOrder v) : LocAlg v) * locEmb v b) • 1 ∧
      ∀ x, x ∈ locLattice v L ↔
        ∀ i, (((h⁻¹ : GL (Fin r) (LocAlg v)) : Matrix (Fin r) (Fin r) (LocAlg v)) *ᵥ x) i ∈
          locOrder v := by
  obtain ⟨g, hg⟩ := exists_frame v hL
  have h₁ := gram_mem_semiLoc v hmod hg hb
  have h₂ := gram_inv_mem_semiLoc v hd hL.1 hmod hg hb0 hb
  set H := (g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc with hH
  have hHd : IsUnit H.det := by
    have := g.det_ne_zero
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Published.det_map_cc]
    exact (mul_ne_zero (mul_ne_zero this hd) (Published.cc_ne_zero this)).isUnit
  have hHh : ∀ i j, cc (H i j) = H j i := fun i j => by
    rw [hH, ← Published.herm_col, ← Published.herm_col, HermitianTraceFormVanishing.herm_conj G hG]
  set t := ((ε : locOrder v) : LocAlg v) * locEmb v b with ht
  set t' := (((ε⁻¹ : (locOrder v)ˣ) : locOrder v) : LocAlg v) * locEmb v b⁻¹ with ht'
  have htt : t * t' = 1 := by
    have e : ((ε : locOrder v) : LocAlg v) * (((ε⁻¹ : (locOrder v)ˣ) : locOrder v) : LocAlg v) = 1 :=
      congrArg Subtype.val ε.mul_inv
    rw [ht, ht', mul_mul_mul_comm, e, ← map_mul, mul_inv_cancel₀ hb0, map_one, one_mul]
  have hct' : locConj v t' = t' := by
    have := congrArg (locConj v) htt
    rw [map_mul, hε, map_one] at this
    linear_combination t' * this - locConj v t' * htt
  obtain ⟨P, hP, hP', hPP⟩ := exists_eq_transpose_mul_map_locConj v
    (M := t' • H.map (locEmb v)) (N := t • H⁻¹.map (locEmb v))
    (fun i j => by
      have := mul_mem (ε⁻¹).1.2 ((locEmb_mem_locOrder_iff v _).2 (h₁ i j))
      rwa [map_mul, ← mul_assoc] at this)
    (fun i j => by
      have := mul_mem ε.1.2 ((locEmb_mem_locOrder_iff v _).2 (h₂ i j))
      rwa [map_mul, ← mul_assoc] at this)
    (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm t', htt, one_smul, ← Matrix.map_mul,
        Matrix.mul_nonsing_inv _ hHd, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun i j => by
      change locConj v (t' * locEmb v (H i j)) = t' * locEmb v (H j i)
      rw [map_mul, hct', locConj_locEmb, hHh])
  let g' : GL (Fin r) (LocAlg v) := Matrix.GeneralLinearGroup.map (locEmb v) g
  have hHg : (g' : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
      (g' : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) =
      (P : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * (t • 1) *
        (P : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hPP, smul_smul, htt, one_smul, hH,
      Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨g' * P⁻¹, ?_, fun x => ?_⟩
  · rw [Units.val_mul, UnramifiedHermitian.congr_mul, hHg, ← UnramifiedHermitian.congr_mul,
      Units.mul_inv]
    simp
  · rw [mem_locLattice_iff_of_frame v hg, mul_inv_rev, inv_inv, Units.val_mul,
      ← Matrix.mulVec_mulVec]
    refine ⟨fun h => mulVec_mem_locOrder v hP h, fun h i => ?_⟩
    have := mulVec_mem_locOrder v hP' h i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
end GlobalTheory.SelfDualGenus
