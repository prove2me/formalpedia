-- Prove2me | solution 1 for GlobalTheory.HilbertRecip.relIndex_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:17:54.853555+00:00
-- url     : https://prove2.me/submissions/60128011-5340-439a-8b12-4860f59b9e5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquares
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitMemGlobalNormOfMemLocalNorms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_index_eq_relIndex_mul_index_sup
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_sq
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm
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
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.HilbertRecip
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbertRecip
theorem _root_.solution {G : Type} [CommGroup G] (B : G →* G →* ℤˣ) (W U : Subgroup G)
    (hW0 : W.index ≠ 0) (hW : ∀ x, ∀ w ∈ W, B x w = 1) (hker : ∀ x, (∀ y, B x y = 1) → x ∈ W)
    (hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 1) : W.relIndex U ^ 2 ≤ W.index := by
  classical
  set H := U ⊔ W with hH
  have hsplit : W.index = W.relIndex U * H.index := index_eq_relIndex_mul_index_sup U W
  have hH0 : H.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsplit
    exact hW0 hsplit
  haveI : H.FiniteIndex := ⟨hH0⟩
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _

  have hkill : ∀ f ∈ U.map B, H ≤ f.ker := by
    rintro f ⟨x, hx, rfl⟩
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact MonoidHom.mem_ker.mpr (hU x hx y hy)
    · exact MonoidHom.mem_ker.mpr (hW x y hy)
  let ψ : ℤˣ →* ℚ := (Int.castRingHom ℚ).toMonoidHom.comp (Units.coeHom ℤ)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h' : ((a : ℤ) : ℚ) = ((b : ℤ) : ℚ) := hab
    exact Units.ext (by exact_mod_cast h')
  let g : (U.map B) → ((G ⧸ H) →* ℚ) := fun f =>
    QuotientGroup.lift H (ψ.comp f.1) (fun y hy => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (hkill f.1 f.2 hy), map_one])
  have hg : Function.Injective g := by
    intro f1 f2 h
    apply Subtype.ext
    apply MonoidHom.ext
    intro y
    have h' := congrArg (fun φ : (G ⧸ H) →* ℚ => φ (y : G ⧸ H)) h
    simp only [g, QuotientGroup.lift_mk, MonoidHom.comp_apply] at h'
    exact hψ h'
  have hli : LinearIndependent ℚ (fun f : U.map B => ((g f : (G ⧸ H) →* ℚ) : G ⧸ H → ℚ)) :=
    (linearIndependent_monoidHom (G ⧸ H) ℚ).comp g hg
  haveI : Finite (U.map B) := hli.finite_of_isNoetherian
  letI : Fintype (U.map B) := Fintype.ofFinite _
  have hcard : Fintype.card (U.map B) ≤ Fintype.card (G ⧸ H) := by
    have h' := hli.fintype_card_le_finrank
    rwa [Module.finrank_fintype_fun_eq_card] at h'
  have hcardN : Nat.card (U.map B) ≤ H.index := by
    rw [Nat.card_eq_fintype_card, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact hcard
  have hkerW : B.ker ≤ W := by
    intro x hx
    refine hker x (fun y => ?_)
    have h1 : B x = 1 := hx
    exact DFunLike.congr_fun h1 y
  have hrk : B.ker.relIndex U = Nat.card (U.map B) := Subgroup.relIndex_ker (K := U) B
  have hpos : 0 < Nat.card (U.map B) := Nat.card_pos
  have hm : W.relIndex U ≤ H.index :=
    (Subgroup.relIndex_le_of_le_left hkerW (by rw [hrk]; exact hpos.ne')).trans (by rw [hrk]; exact hcardN)
  calc W.relIndex U ^ 2 = W.relIndex U * W.relIndex U := sq _
    _ ≤ W.relIndex U * H.index := Nat.mul_le_mul_left _ hm
    _ = W.index := hsplit.symm
end GlobalTheory.HilbertRecip
