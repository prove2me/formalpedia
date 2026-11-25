-- Prove2me | solution 1 for GlobalTheory.LatticePair.hasSum_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:48.722427+00:00
-- url     : https://prove2.me/submissions/c5a34b72-9f56-4fa2-ac2a-f08540306ad5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSum
import Theorems.Thm_GlobalTheory_LatticePair_isInt_mul_KO_iff
import Theorems.Thm_GlobalTheory_LatticePair_isInt_KO_mul_iff
import Theorems.Thm_GlobalTheory_LatticePair_ord_det_of_mem_KO
import Theorems.Thm_GlobalTheory_LatticePair_ord_det_mul
import Theorems.Thm_GlobalTheory_LatticePair_ord_det_inv
import Theorems.Thm_GlobalTheory_LatticePair_valuation_det_le_one
import Theorems.Thm_GlobalTheory_LatticePair_ord_nonneg_of_le_one
import Theorems.Thm_GlobalTheory_LatticePair_ord_det_torusElt
import Theorems.Thm_GlobalTheory_LatticePair_isInt_and_mul_torus_iff
import Theorems.Thm_GlobalTheory_LatticePair_smul_out
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_HeckeSeries_ord_det_of_mem_KO
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SatakeBound_isBorelSph_one
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_T_hasSum_hecke_series_spherical_integral_inverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.LatticePair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.LatticePair
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) (g : GL (Fin n) k)
    (hg : g ∈ cell k (Fin n) ϖ e) (X : ℂ) (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) :
    HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat +
        (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat))
      (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  obtain ⟨x, hx, y, hy, hgxy⟩ := DoubleCoset.mem_doubleCoset.1 hg
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = x * torusElt k (Fin n) ϖ fun i => min (e i) 0 := ⟨_, rfl⟩
  have hP : ∀ h : GL (Fin n) k, (IsInt h⁻¹ ∧ IsInt (h⁻¹ * g)) ↔ IsInt (h⁻¹ * u) := fun h => by
    rw [hgxy, hu, ← mul_assoc, ← mul_assoc, ← mul_assoc, isInt_mul_KO_iff hy, ← isInt_and_mul_torus_iff hϖ,
      isInt_mul_KO_iff hx]
  let E : {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]} ≃
      {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    (MulAction.toPerm u).subtypeEquiv fun c => by
      obtain ⟨κ, hκ, h⟩ := smul_out u c
      refine Iff.trans ?_ (hP (u • c).out).symm
      have : (u * c.out * κ)⁻¹ * u = κ⁻¹ * c.out⁻¹ := by group
      rw [h, this, isInt_KO_mul_iff (inv_mem hκ)]
      rfl
  have hN := (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n (fun _ => 1) (fun _ => 1) (isBorelSph_one k) (fun _ => one_ne_zero) (X ^ 2)
    fun i => by simpa only [inv_one, mul_one] using hX i).mul_left (X ^ (∑ i, |e i|).toNat)
  simp only [inv_one, mul_one] at hN
  rw [← E.hasSum_iff]
  refine (congrArg (HasSum · _) (funext fun c => ?_)).mpr hN
  obtain ⟨κ, hκ, h⟩ := smul_out u c.1
  have hE : (E c).1.out = u * c.1.out * κ := h
  have hj := ord_nonneg_of_le_one (valuation_det_le_one (A := c.1.out⁻¹) c.2)
  have habs : ∑ i, |e i| = ∑ i, e i - 2 * ∑ i, min (e i) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_neg]
    omega
  have h1 : ∑ i, min (e i) 0 ≤ 0 := Finset.sum_nonpos fun i _ => min_le_right _ _
  have h2 : ∑ i, min (e i) 0 ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => min_le_left _ _
  have hou : ord k (Matrix.GeneralLinearGroup.det u) = ∑ i, min (e i) 0 := by
    rw [hu, ord_det_mul, ord_det_of_mem_KO hx, ord_det_torusElt hϖ, zero_add]
  have hog : ord k (Matrix.GeneralLinearGroup.det g) = ∑ i, e i := by
    rw [hgxy, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hx, ord_det_of_mem_KO hy, ord_det_torusElt hϖ,
      zero_add, add_zero]
  rw [ord_det_inv] at hj
  simp only [Function.comp_apply]
  rw [ord_det_mul, ord_det_inv, hE, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hκ, hou, hog,
    ← pow_mul, ← pow_add, habs]
  congr 1
  omega
end GlobalTheory.LatticePair
