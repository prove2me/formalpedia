-- Prove2me | solution 1 for GlobalTheory.PairOp.D_U_ram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:47.841238+00:00
-- url     : https://prove2.me/submissions/d01e6666-c6c4-4a98-b84e-11a1850e34a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_U_dia
import Theorems.Thm_GlobalTheory_PairOp_FFStar_dia
import Theorems.Thm_GlobalTheory_PairOp_commute_sum
import Theorems.Thm_GlobalTheory_PairOp_mem_ram
import Theorems.Thm_GlobalTheory_PairOp_Gs_mul_GsStar
import Theorems.Thm_GlobalTheory_PairOp_FFStar_eq_U_GsStar
import Theorems.Thm_GlobalTheory_PairOp_FF_FFStar_ram
import Theorems.Thm_GlobalTheory_PairOp_eq_zpow_smul
import Theorems.Thm_GlobalTheory_LatPair_D_apply
import Theorems.Thm_GlobalTheory_LatPair_FF_apply
import Theorems.Thm_GlobalTheory_LatPair_Gs_apply
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero
import Theorems.Thm_GlobalTheory_LatPair_cross_dia_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
namespace GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
private theorem FF_eq_D_Gs_of_mem_Mram {φ : Form k n M} (h : φ ∈ Mram k n M) : FF q χ φ = D q (Gs χ φ) := by
  classical
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  funext P₁
  rw [FF_apply, D_apply]
  simp only [Gs_apply]
  have h0 : ∑ P ∈ withLat P₁.ker with cross q P₁ P = 0, χ (cross q P₁ P) • φ P = 0 := by
    rw [Finset.sum_congr rfl fun P hP => by
      rw [(Finset.mem_filter.mp hP).2, AddChar.map_zero_eq_one, one_smul]]
    refine Model.sum_stable_eq_zero h _ fun c P => ?_
    simp only [Finset.mem_filter, mem_withLat, Pair.dia_lat]
    constructor
    · rintro ⟨hk, hc⟩
      refine ⟨hk, ?_⟩
      rwa [cross_dia_right q hk, mul_eq_zero, or_iff_right (Units.ne_zero _)] at hc
    · rintro ⟨hk, hc⟩
      exact ⟨hk, by rw [cross_dia_right q hk, hc, mul_zero]⟩
  rw [← Finset.sum_filter_add_sum_filter_not (withLat P₁.ker) (fun P => cross q P₁ P = 0), h0, zero_add,
    ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun P hP => ((Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP).2)⁻¹ • P,
      Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP).2))
    (fun x _ => x.2 • x.1) (fun P hP => ?_) (fun x hx => ?_) (fun P _ => smul_inv_smul _ _)
    (fun x hx => ?_) (fun P _ => by simp)
  · obtain ⟨hk, hc⟩ := Finset.mem_filter.mp hP
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · rw [mem_withLat, Pair.dia_lat]
      exact mem_withLat.mp hk
    · rw [cross_dia_right q (mem_withLat.mp hk)]
      simp [hc]
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_withLat, Pair.dia_lat]
      exact mem_withLat.mp hk
    · rw [cross_dia_right q (mem_withLat.mp hk), hc, mul_one]
      exact x.2.ne_zero
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    have e : cross q P₁ (x.2 • x.1) = x.2 := by
      rw [cross_dia_right q (mem_withLat.mp hk), hc, mul_one]
    have eu : ∀ h', Units.mk0 (cross q P₁ (x.2 • x.1)) h' = x.2 := fun h' => Units.ext (by simpa using e)
    rw [eu]
    exact Prod.ext (inv_smul_smul _ _) rfl
section Adjoint
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
end Adjoint
end GlobalTheory.PairOp
end
end

set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
namespace GlobalTheory.PairOp
theorem _root_.solution [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    D q (U q φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ := by
  have hGsU : ∀ ψ : Form k n M, Gs χ (U q ψ) = U q (Gs χ ψ) := fun ψ => by
    have e : (Gs χ * U q : Module.End ℂ (Form k n M)) = U q * Gs χ := by
      unfold Gs
      exact (commute_sum (fun c => U_dia q c) _ (fun d : 𝓀[k]ˣ => χ d) fun d => d).symm
    exact LinearMap.congr_fun e ψ
  have hN : Nm φ = 0 := h
  have h2 : FFStar q χ φ ∈ Mram k n M := mem_ram (fun c => FFStar_dia q χ c) h
  have h3 := FF_FFStar_ram q hχ h
  rw [FF_eq_D_Gs_of_mem_Mram q h2, FFStar_eq_U_GsStar q χ h, hGsU, ← Module.End.mul_apply (Gs χ),
    Gs_mul_GsStar hχ] at h3
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hN, sub_zero, map_smul] at h3
  exact eq_zpow_smul h3
end GlobalTheory.PairOp
