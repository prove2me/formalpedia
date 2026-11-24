-- Prove2me | solution 1 for GlobalTheory.PairOp.FFStar_eq_U_GsStar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:38.093577+00:00
-- url     : https://prove2.me/submissions/0beea592-5bf5-498a-b2b9-6a505d27b683

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_LatPair_FFStar_apply
import Theorems.Thm_GlobalTheory_LatPair_GsStar_apply
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero
import Theorems.Thm_GlobalTheory_LatPair_U_apply
import Theorems.Thm_GlobalTheory_LatPair_cross_dia_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable (χ)
namespace GlobalTheory.PairOp
theorem _root_.solution {φ : Form k n M} (h : φ ∈ Mram k n M) : FFStar q χ φ = U q (GsStar χ φ) := by
  classical
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  funext P
  rw [FFStar_apply, U_apply]
  simp only [GsStar_apply]

  have h0 : ∑ P₁ ∈ withKer P.lat with cross q P₁ P = 0, χ (-cross q P₁ P) • φ P₁ = 0 := by
    rw [Finset.sum_congr rfl fun P₁ hP₁ => by
      rw [(Finset.mem_filter.mp hP₁).2, neg_zero, AddChar.map_zero_eq_one, one_smul]]
    refine Model.sum_stable_eq_zero h _ fun c P₁ => ?_
    simp only [Finset.mem_filter, mem_withKer, Pair.dia_ker]
    constructor
    · rintro ⟨hk, hc⟩
      refine ⟨hk, ?_⟩
      rwa [cross_dia_left q hk.symm, mul_eq_zero, or_iff_right (Units.ne_zero _)] at hc
    · rintro ⟨hk, hc⟩
      exact ⟨hk, by rw [cross_dia_left q hk.symm, hc, mul_zero]⟩
  rw [← Finset.sum_filter_add_sum_filter_not (withKer P.lat) (fun P₁ => cross q P₁ P = 0), h0, zero_add,
    ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun P₁ hP₁ => (Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2 • P₁,
      Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2))
    (fun x _ => x.2⁻¹ • x.1) (fun P₁ hP₁ => ?_) (fun x hx => ?_) (fun P₁ _ => inv_smul_smul _ _)
    (fun x hx => ?_) (fun P₁ _ => by simp)
  · obtain ⟨hk, hc⟩ := Finset.mem_filter.mp hP₁
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · rw [mem_withKer, Pair.dia_ker]
      exact mem_withKer.mp hk
    · rw [cross_dia_left q (mem_withKer.mp hk).symm]
      simp [hc]
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_withKer, Pair.dia_ker]
      exact mem_withKer.mp hk
    · rw [cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]
      exact x.2.ne_zero
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    have e : cross q (x.2⁻¹ • x.1) P = x.2 := by
      rw [cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]
    have eu : ∀ h', Units.mk0 (cross q (x.2⁻¹ • x.1) P) h' = x.2 := fun h' => Units.ext (by simpa using e)
    rw [eu]
    exact Prod.ext (smul_inv_smul _ _) rfl
end GlobalTheory.PairOp
