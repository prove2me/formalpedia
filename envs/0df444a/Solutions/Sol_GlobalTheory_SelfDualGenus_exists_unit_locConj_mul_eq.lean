-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_unit_locConj_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:30:03.411557+00:00
-- url     : https://prove2.me/submissions/8815aa4a-4a87-452f-b9e8-78cdef026f28

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locEmb
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_isUnit_sub_locOrderConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_cc_algebraMap
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_mem_locOrder_iff
import Theorems.Thm_GlobalTheory_SelfDualGenus_locOrderConj_locOrderConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_mem_range_of_locOrderConj_eq
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_Published_cc_ne_zero
import Theorems.Thm_GlobalTheory_QuadraticEtale_exists_isUnit_add_mul
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
theorem _root_.solution {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    {b : E} (hb0 : b ≠ 0)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v) :
    ∃ ε : (locOrder v)ˣ, locConj v (((ε : locOrder v) : LocAlg v) * locEmb v b) =
      ((ε : locOrder v) : LocAlg v) * locEmb v b := by
  have hu : b⁻¹ * cc b ∈ semiLoc v := by
    obtain ⟨s, hs, h⟩ := (hb b).2 (by rw [inv_mul_cancel₀ hb0]; exact one_mem _)
    refine (hb _).1 ⟨s, hs, ?_⟩
    have := hc _ h
    rwa [HermitianTraceFormVanishing.cc_mul, cc_algebraMap] at this
  have hcb := Published.cc_ne_zero hb0
  have hcu : cc (b⁻¹ * cc b) = (cc b)⁻¹ * b := by simp [cc]
  let u : locOrder v := ⟨_, (locEmb_mem_locOrder_iff v _).2 hu⟩
  have hu1 : u * locOrderConj v u = 1 := by
    apply Subtype.ext
    change locEmb v _ * locEmb v (cc _) = 1
    rw [← map_mul, hcu, ← map_one (locEmb v)]
    congr 1
    field_simp
  obtain ⟨a, ha⟩ := QuadraticEtale.exists_isUnit_add_mul (R := v.adicCompletionIntegers (maximalRealSubfield E))
    (locOrderConj v) (locOrderConj_locOrderConj v) (mem_range_of_locOrderConj_eq v)
    (exists_isUnit_sub_locOrderConj v) hu1
  refine ⟨ha.unit, ?_⟩
  have e0 : ((ha.unit : locOrder v) : LocAlg v) = a + locEmb v (b⁻¹ * cc b) * locConj v a := rfl
  have e1 : locEmb v (b⁻¹ * cc b) * locEmb v b = locEmb v (cc b) := by
    rw [← map_mul]; congr 1; field_simp
  have e2 : locEmb v (cc (b⁻¹ * cc b)) * locEmb v (cc b) = locEmb v b := by
    rw [← map_mul, hcu]; congr 1; field_simp
  rw [e0, map_mul, map_add, map_mul, locConj_locConj, locConj_locEmb, locConj_locEmb]
  linear_combination (a : LocAlg v) * e2 - locConj v a * e1
end GlobalTheory.SelfDualGenus
