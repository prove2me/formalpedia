-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.congr_of_local_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:41:20.385805+00:00
-- url     : https://prove2.me/submissions/8b90c29d-a080-4c4c-86e8-4e50a057ed1f

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locEmb
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_coe
import Theorems.Thm_GlobalTheory_SelfDualGenus_algebraMap_locAlg_injective
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_coord
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_Published_Landherr_re_det_div_pos
import Theorems.Thm_GlobalTheory_Published_cc_det_of_herm
import Theorems.Thm_GlobalTheory_Published_exists_cc_eq_neg
import Theorems.Thm_GlobalTheory_Published_exists_sq_real
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
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution (H : Published.Landherr) (H' : Published.HasseNormSt)
    (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj)
    (hf : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : LocAlg v,
      locEmb v (G.det / G'.det) = z * locConj v z) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by
  have hm : G.det / G'.det ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
    exact congrArg₂ (· / ·) (Published.cc_det_of_herm hG) (Published.cc_det_of_herm hG')
  obtain ⟨θ, h0, hθ⟩ := Published.exists_cc_eq_neg E
  obtain ⟨d, hdθ⟩ := Published.exists_sq_real hθ
  obtain ⟨p, q, hpq⟩ := H' (maximalRealSubfield E) d ⟨_, hm⟩
    (fun h => mul_ne_zero h0 h0 (by rw [← hdθ, h]; rfl))
    (fun h => div_ne_zero hd hd' (congrArg Subtype.val h))
    (fun σ => by
      have h1 := Published.Landherr.re_det_div_pos hd _
        (hs (ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)))
      have h2 : ComplexEmbedding.lift E (Complex.ofRealHom.comp σ) (G.det / G'.det) =
          (σ ⟨_, hm⟩ : ℂ) :=
        ComplexEmbedding.lift_algebraMap_apply E (Complex.ofRealHom.comp σ) ⟨_, hm⟩
      rw [h2, Complex.ofReal_re] at h1
      exact ⟨Real.sqrt (σ ⟨_, hm⟩), 0, by rw [Real.sq_sqrt h1.le]; ring⟩)
    (fun v => by
      obtain ⟨z, hz⟩ := hf v
      obtain ⟨p, q, rfl⟩ := exists_coord v h0 hθ z
      refine ⟨p, q, algebraMap_locAlg_injective v ?_⟩
      rw [← locEmb_coe, map_sub, map_mul, ← locEmb_coe, hdθ, map_pow, map_pow, map_mul]
      rw [map_add, map_mul, locConj_algebraMap, locConj_algebraMap, locConj_locEmb, hθ,
        map_neg] at hz
      exact hz.trans (by ring))
  refine H E r G G' hG hG' hd hd' hs ⟨(p : E) + q * θ, ?_⟩
  have h1 : G.det / G'.det = (p : E) ^ 2 - (d : E) * (q : E) ^ 2 := by
    simpa using congrArg Subtype.val hpq
  have h2 : cc ((p : E) + q * θ) = p - q * θ := by
    change IsCMField.complexConj E _ = _
    rw [map_add, map_mul, IsCMField.complexConj_apply_eq_self, IsCMField.complexConj_apply_eq_self,
      show IsCMField.complexConj E θ = -θ from hθ]
    ring
  rw [h1, h2, hdθ]
  ring
end GlobalTheory.SelfDualGenus
