-- Prove2me | solution 1 for GlobalTheory.GLDoubling.sphSection_torusElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:07.921373+00:00
-- url     : https://prove2.me/submissions/99ba14c0-5269-46cd-bf89-214b8cdf0121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_coe_absRatio
import Theorems.Thm_GlobalTheory_GLDoubling_shear_mem
import Theorems.Thm_GlobalTheory_GLDoubling_isIwasawa
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_right
import Theorems.Thm_GlobalTheory_GLDoubling_val_torusElt
import Theorems.Thm_GlobalTheory_GLDoubling_nabs_det_torusElt
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_coe
import Theorems.Thm_GlobalTheory_Doubling_det_blkMat
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : ℂ) (e : n → ℤ) :
    sphSection k n s (io k n (torusElt k n ϖ e, 1)) =
      (resCard k : ℂ) ^ (-((Fintype.card n : ℂ) / 2 + s) * ((∑ i, |e i| : ℤ) : ℂ)) := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let B : Matrix n n k := diagonal fun i => (ϖ : k) ^ max (-e i) 0 - 1
  let C : Matrix n n k := diagonal fun i => (ϖ : k) ^ max (e i) 0 - 1
  have hBC : ∀ i, ((ϖ : k) ^ max (-e i) 0 - 1) * ((ϖ : k) ^ max (e i) 0 - 1) = 0 := fun i => by
    rcases le_total (e i) 0 with h | h <;> simp [h]
  have h : B * C = 0 := by simp only [B, C, diagonal_mul_diagonal, hBC, diagonal_zero]
  have h' : C * B = 0 := by simp only [B, C, diagonal_mul_diagonal, mul_comm ((ϖ : k) ^ max (e _) 0 - 1), hBC, diagonal_zero]
  have hint : ∀ f : n → ℤ, ∀ i j, (diagonal fun i => (ϖ : k) ^ max (f i) 0 - 1) i j ∈ 𝒪[k] := fun f i j => by
    rw [diagonal_apply]; split_ifs
    · refine sub_mem ?_ (one_mem _)
      show valuation k _ ≤ 1
      rw [map_zpow₀]
      exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (le_max_right _ _)
    · exact zero_mem _
  have hκ : shear B C h h' ∈ KO k (n ⊕ n) := shear_mem h h' (hint fun i => -e i) (hint e)
  have hv : (io k n (torusElt k n ϖ e, 1) * shear B C h h').1 =
      fromBlocks (torusElt k n ϖ e).1 ((torusElt k n ϖ e).1 * B) C 1 := by
    show fromBlocks (torusElt k n ϖ e).1 0 0 1 * fromBlocks 1 B C 1 = _
    simp [fromBlocks_multiply]
  have hL : (torusElt k n ϖ e).1 + (torusElt k n ϖ e).1 * B = (torusElt k n ϖ fun i => max (e i) 0).1 := by
    simp only [val_torusElt, B, diagonal_mul_diagonal, diagonal_add]
    congr 1
    funext i
    rw [mul_sub, mul_one, add_sub_cancel, ← zpow_add₀ ϖ.ne_zero]
    congr 1
    omega
  let p : siegel k n := ⟨io k n (torusElt k n ϖ e, 1) * shear B C h h', mem_stabGL_diagSub.2 (by
    rw [hv]
    simp only [KeepsDiag, leviMat, Equiv.coe_refl, submatrix_id_id, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
      toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hL]
    simp only [val_torusElt, C, ← diagonal_one, diagonal_add, sub_add_cancel])⟩
  have h1 : leviGL (Equiv.refl (n ⊕ n)) p = torusElt k n ϖ fun i => max (e i) 0 := by
    ext1
    rw [val_leviGL, ← hL]
    show leviMat _ (io k n (torusElt k n ϖ e, 1) * shear B C h h').1 = _
    rw [hv]
    simp [leviMat]
  have h2 : nabs k (GeneralLinearGroup.det (p : GL (n ⊕ n) k)) =
      nabs k (GeneralLinearGroup.det (torusElt k n ϖ e)) := by
    show nabs k (GeneralLinearGroup.det (io k n (torusElt k n ϖ e, 1) * shear B C h h')) = _
    rw [map_mul, nabs_mul', nabs_det_of_mem_KO hκ, mul_one]
    congr 1
    ext
    exact (det_blkMat _ _ _).trans (by simp)
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have h3 : (absRatio k n p : ℝ) = (resCard k : ℝ) ^ (-∑ i, |e i|) := by
    rw [coe_absRatio, h1, h2, nabs_det_torusElt hϖ, nabs_det_torusElt hϖ, sq, ← zpow_add₀ hq.ne', ← zpow_sub₀ hq.ne']
    congr 1
    simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_neg]
    omega
  rw [← sphSection_right s _ hκ, sphSection, show io k n (torusElt k n ϖ e, 1) * shear B C h h' = p from rfl,
    isIwasawa.iwAbs_coe, npow, h3, ← Real.rpow_intCast, ← Complex.cpow_mul_ofReal_nonneg hq.le]
  rw [Complex.ofReal_intCast, Complex.ofReal_natCast, Int.cast_neg]
  congr 1
  ring
end GlobalTheory.GLDoubling
