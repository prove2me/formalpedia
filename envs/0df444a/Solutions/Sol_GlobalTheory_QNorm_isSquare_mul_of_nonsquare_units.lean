-- Prove2me | solution 1 for GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:37.938804+00:00
-- url     : https://prove2.me/submissions/6a1c673b-8ac9-4fef-a6c3-613f3587c856

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Theorems.Thm_GlobalTheory_QNorm_isSquare_of_isSquare_residue_odd
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers
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
open NumberField IsDedekindDomain GlobalTheory.QNorm IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 → ∀ x y : v.adicCompletion F, Valued.v x = 1 → Valued.v y = 1 → ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
  intro F _ _ v h2 x y hx hy hnx hny
  classical
  haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) :=
    @Fintype.ofFinite _ (_root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v)
  let x' : v.adicCompletionIntegers F :=
    ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hx.le⟩
  let y' : v.adicCompletionIntegers F :=
    ⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hy.le⟩
  have hrx : ¬ IsSquare (residue (v.adicCompletionIntegers F) x') :=
    fun h => hnx (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 x' hx h)
  have hry : ¬ IsSquare (residue (v.adicCompletionIntegers F) y') :=
    fun h => hny (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 y' hy h)
  have hx0 : residue (v.adicCompletionIntegers F) x' ≠ 0 := fun h => hrx (h ▸ ⟨0, by simp⟩)
  have hy0 : residue (v.adicCompletionIntegers F) y' ≠ 0 := fun h => hry (h ▸ ⟨0, by simp⟩)
  have hres : IsSquare (residue (v.adicCompletionIntegers F) (x' * y')) := by
    rw [map_mul, ← quadraticChar_one_iff_isSquare (mul_ne_zero hx0 hy0), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.2 hrx, quadraticChar_neg_one_iff_not_isSquare.2 hry]
    norm_num
  have hxy : Valued.v (((x' * y' : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    push_cast
    rw [map_mul]
    simp [x', y', hx, hy]
  simpa [x', y'] using _root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 (x' * y') hxy hres
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
