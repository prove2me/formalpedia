-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.exists_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:29.203147+00:00
-- url     : https://prove2.me/submissions/bb72bb5b-45b9-4e6b-96fe-593cbd8cd945

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Theorems.Thm_GlobalTheory_UnramSelfDual_cT_mul_of
import Theorems.Thm_GlobalTheory_UnramSelfDual_gram_one
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
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
variable {c J}
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution {e e' : Fin M → Fin M → A}
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0)
    (he' : ∀ i j, hform c J (e' i) (e' j) = if i = j then 1 else 0) :
    ∃ g ∈ UJ c J, ∀ i, (g : Matrix (Fin M) (Fin M) A) *ᵥ e i = e' i := by
  have h1 := gram_one he
  have h2 := mul_eq_one_comm.1 h1
  have h1' := gram_one he'
  have h2' := mul_eq_one_comm.1 h1'
  set P := (Matrix.of e)ᵀ with hP
  set P' := (Matrix.of e')ᵀ with hP'
  set Q := cT c P * J with hQ
  set Q' := cT c P' * J with hQ'
  refine ⟨⟨P' * Q, P * Q', ?_, ?_⟩, ?_, fun i => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h1, Matrix.one_mul, h2']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q', h1', Matrix.one_mul, h2]
  · show cT c (P' * Q) * J * (P' * Q) = J
    have h3 : cT c Q * cT c P = 1 := by rw [← cT_mul, h2, cT_one]
    calc cT c (P' * Q) * J * (P' * Q) = cT c Q * (Q' * P') * Q := by
          rw [cT_mul, hQ']; simp only [Matrix.mul_assoc]
      _ = (cT c Q * cT c P) * J := by rw [h1', Matrix.mul_one, Matrix.mul_assoc]
      _ = J := by rw [h3, Matrix.one_mul]
  · show (P' * Q) *ᵥ e i = e' i
    rw [← Matrix.mulVec_mulVec]
    have : Q *ᵥ e i = Pi.single i 1 := by
      ext k
      rw [hQ, hP, cT_mul_of, he, Pi.single_apply]
    rw [this]
    ext k
    simp [hP']
end GlobalTheory.UnramSelfDual
