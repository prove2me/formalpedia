-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.locEmb_mem_locOrder_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:37.501399+00:00
-- url     : https://prove2.me/submissions/c07b46a5-3f31-4620-8306-5c1617da775e

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locEmb
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_coe
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_algebraMap
import Theorems.Thm_GlobalTheory_SelfDualGenus_algebraMap_locAlg_injective
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_of_mem_locOrder_of_locConj_eq
import Theorems.Thm_GlobalTheory_SelfDualGenus_mem_semiLoc_iff
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalLattice_mem_localRing_iff
import Theorems.Thm_GlobalTheory_LocalLattice_mem_one_ringOfIntegers_iff
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
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution (z : E) : locEmb v z ∈ locOrder v ↔ z ∈ semiLoc v := by
  rw [mem_semiLoc_iff]
  constructor
  · intro hz
    have real : ∀ y : E, cc y = y → locEmb v y ∈ locOrder v →
        ∃ s ∉ v.asIdeal, IsIntegral ℤ ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * y) := by
      intro y hy hm
      obtain ⟨a, ha⟩ := exists_of_mem_locOrder_of_locConj_eq v hm (by rw [locConj_locEmb, hy])
      let y' : (maximalRealSubfield E) := ⟨y, (IsCMField.complexConj_eq_self_iff E y).1 hy⟩
      have h1 : algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) y' = a :=
        algebraMap_locAlg_injective v ((locEmb_coe v y').symm.trans ha.symm)
      obtain ⟨s, hs, h⟩ := (mem_localRing_iff v y').1
        ((algebraMap_mem_adicCompletionIntegers_iff v y').1 (h1 ▸ a.2))
      exact ⟨s, hs, ((mem_one_ringOfIntegers_iff _).1 h).map_of_comp_eq (RingHom.id ℤ)
        (algebraMap (maximalRealSubfield E) E) (RingHom.ext_int _ _)⟩
    have hc : locEmb v (cc z) ∈ locOrder v := locConj_mem v hz
    have h1 := (mem_semiLoc_iff v _).2 (real (z + cc z) (by simp [cc, add_comm])
      (by rw [map_add]; exact add_mem hz hc))
    have h2 := (mem_semiLoc_iff v _).2 (real (z * cc z) (by simp [cc, mul_comm])
      (by rw [map_mul]; exact mul_mem hz hc))
    have hi : IsIntegral (semiLoc v) z := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨_, h1⟩ * Polynomial.X + Polynomial.C ⟨_, h2⟩,
        by monicity!, ?_⟩
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      change z ^ 2 - (z + cc z) * z + z * cc z = 0
      ring
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact (mem_semiLoc_iff v z).1 (hb ▸ b.2)
  · rintro ⟨s, hs, h⟩
    obtain ⟨t, ht⟩ := ((isUnit_algebraMap_iff v s).2 hs).exists_left_inv
    have h1 : locEmb v z = algebraMap _ (LocAlg v) t *
        locEmb v ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z) := by
      rw [map_mul, locEmb_algebraMap, ← mul_assoc, ← map_mul, ht, map_one, one_mul]
    rw [h1]
    exact mul_mem (Subalgebra.algebraMap_mem _ t) (locEmb_mem_locOrder v ⟨_, h⟩)
end GlobalTheory.SelfDualGenus
