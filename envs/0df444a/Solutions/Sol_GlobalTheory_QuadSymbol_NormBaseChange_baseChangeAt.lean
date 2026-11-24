-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.baseChangeAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:22.725902+00:00
-- url     : https://prove2.me/submissions/1da37f66-7755-45f1-952f-1074a80fa0ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_nm_iff
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_exists_sqrt_basis
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_normsEscape
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff_form
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
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution (F E K L A : Type) [Field F] [CharZero F] [Field E] [Field K] [Field L]
    [Field A] [Algebra F E] [Algebra F K] [Algebra K L] [Algebra E L] [Algebra F L] [Algebra F A]
    [IsScalarTower F K L] [IsScalarTower F E L] (hE : Module.finrank F E = 2)
    (hL : Module.finrank K L = 2) (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B) :
    BaseChangeAt F E K L A := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap F A).injective
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_sqrt_basis F E hE
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hli : LinearIndependent K ![(1 : L), algebraMap E L (e 1)] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    have hbot : (⊤ : Subalgebra K L) ≤ ⊥ := by
      rw [← hgen, Algebra.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      rw [← e.sum_repr y, Fin.sum_univ_two, h0, map_add, Algebra.smul_def, Algebra.smul_def,
        map_mul, map_mul, map_one, ← hc, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F K L,
        IsScalarTower.algebraMap_apply F K L]
      exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (one_mem _))
        (mul_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ (one_mem _) _))
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 (top_le_iff.1 hbot)
    omega
  let e' : Module.Basis (Fin 2) K L := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hL])
  have h0' : e' 0 = 1 := by simp [e']
  have h1' : e' 1 * e' 1 = algebraMap K L (algebraMap F K δ) := by
    have : e' 1 = algebraMap E L (e 1) := by simp [e']
    rw [this, ← map_mul, h1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  intro B _ _ _ _ _ _ _ x
  have key : x ∈ normGroup K L B ↔
      Units.map (Algebra.norm A : B →* A) x ∈ normGroup F E A := by
    rw [mem_normGroup_iff_form e' h0' h1', mem_normGroup_iff_form e h0 h1,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A B]
    exact nm_iff (hA B) (normsEscape hA B) ((map_ne_zero _).2 hδ0) x.ne_zero
  unfold eta
  rw [key]
end GlobalTheory.QuadSymbol.NormBaseChange
