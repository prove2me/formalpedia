-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodIso.exists_gl_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:47.221041+00:00
-- url     : https://prove2.me/submissions/13438836-ba27-49f4-b906-54810d78fea5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnitStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormsIntegrallyEquivalentAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodIso_exists_gl_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
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
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodIso
namespace GlobalTheory.CompanionTheory.SW.GoodIso
theorem _root_.solution {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ y, s (s y) = y) (O : Subring R)
    (hO : ∀ y ∈ O, s y ∈ O) [Finite (MaximalSpectrum O)] (h2 : IsUnit (2 : O))
    (hδ : ∃ δ : O, IsUnit δ ∧ s (δ : R) = -(δ : R))
    (hN : ∀ β : O, IsUnit β → s (β : R) = β → ∃ a : O, (a : R) * s a = β)
    (m : ℕ) (K K' : Matrix (Fin m) (Fin m) R)
    (hK : ∀ i j, s (K j i) = K i j) (hK' : ∀ i j, s (K' j i) = K' i j)
    (iK : ∀ i j, K i j ∈ O) (iK' : ∀ i j, K' i j ∈ O)
    (wK : ∃ w ∈ O, K.det * w = 1) (wK' : ∃ w ∈ O, K'.det * w = 1) :
    ∃ g : GL (Fin m) R, K' = cT s (g : Matrix (Fin m) (Fin m) R) * K * (g : Matrix (Fin m) (Fin m) R) ∧
      (∀ i j, (g : Matrix (Fin m) (Fin m) R) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  let σO : O →+* O := (s.comp O.subtype).codRestrict O (fun y => hO y y.2)
  have hσO : ∀ y : O, ((σO y : O) : R) = s (y : R) := fun y => rfl
  have lift : ∀ (P : Matrix (Fin m) (Fin m) R) (iP : ∀ i j, P i j ∈ O), (∃ w ∈ O, P.det * w = 1) →
      ∃ Q : Matrix (Fin m) (Fin m) O, Q.map O.subtype = P ∧ IsUnit Q.det := by
    intro P iP ⟨w, hw, hPw⟩
    refine ⟨Matrix.of fun i j => ⟨P i j, iP i j⟩, by ext i j; rfl, ?_⟩
    have hdet : ((Matrix.of fun i j => (⟨P i j, iP i j⟩ : O)).det : O).1 = P.det := by
      have := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨P i j, iP i j⟩ : O))
      exact this
    refine IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext ?_)
    simpa [hdet] using hPw
  obtain ⟨Q, rfl, uQ⟩ := lift K iK wK
  obtain ⟨Q', rfl, uQ'⟩ := lift K' iK' wK'
  have herm : ∀ (Q : Matrix (Fin m) (Fin m) O), (∀ i j, s ((Q.map O.subtype) j i) = (Q.map O.subtype) i j) →
      ∀ i j, σO (Q j i) = Q i j := fun Q h i j => Subtype.ext (h i j)
  obtain ⟨G, hG⟩ := exists_gl_equiv O σO (fun y => Subtype.ext (hs _)) h2
    (by obtain ⟨δ, h1, h3⟩ := hδ; exact ⟨δ, h1, Subtype.ext h3⟩)
    (fun β hβ hβ' => by
      obtain ⟨a, ha⟩ := hN β hβ (congrArg Subtype.val hβ')
      exact ⟨a, Subtype.ext ha⟩)
    m Q Q' (herm Q hK) uQ (herm Q' hK') uQ'
  have hcT : ∀ P : Matrix (Fin m) (Fin m) O,
      cT s (P.map O.subtype) = (cT σO P).map O.subtype := fun P => by ext i j; rfl
  refine ⟨bc O.subtype G, ?_, ?_, ?_⟩
  · have hv : ((bc O.subtype G : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) =
        (G : Matrix (Fin m) (Fin m) O).map O.subtype := rfl
    rw [hv, hcT, hG, Matrix.map_mul, Matrix.map_mul]
  · intro i j
    exact (G.val i j).2
  · intro i j
    rw [← map_inv]
    exact ((G⁻¹).val i j).2
end GlobalTheory.CompanionTheory.SW.GoodIso
