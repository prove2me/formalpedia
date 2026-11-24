-- Prove2me | solution 1 for GlobalTheory.PairOp.operatorIdentities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:27:16.88582+00:00
-- url     : https://prove2.me/submissions/e0a5d6a4-864e-4150-9d15-71c84b321aa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_smul_ofDual
import Theorems.Thm_GlobalTheory_PairOp_D_dia
import Theorems.Thm_GlobalTheory_PairOp_U_dia
import Theorems.Thm_GlobalTheory_PairOp_FF_dia
import Theorems.Thm_GlobalTheory_PairOp_FFStar_dia
import Theorems.Thm_GlobalTheory_PairOp_dia_dia
import Theorems.Thm_GlobalTheory_PairOp_mem_ram
import Theorems.Thm_GlobalTheory_PairOp_Gs_mul_GsStar
import Theorems.Thm_GlobalTheory_PairOp_FF_FFStar
import Theorems.Thm_GlobalTheory_PairOp_FFStar_FF_ram
import Theorems.Thm_GlobalTheory_PairOp_FF_FFStar_ram
import Theorems.Thm_GlobalTheory_PairOp_D_U_ram
import Theorems.Thm_GlobalTheory_PairOp_U_D_ram
import Theorems.Thm_GlobalTheory_PairOp_unit_FFStar_FF
import Theorems.Thm_GlobalTheory_LatPair_D_apply
import Theorems.Thm_GlobalTheory_LatPair_FFStar_apply
import Theorems.Thm_GlobalTheory_LatPair_FFStar_ofDual
import Theorems.Thm_GlobalTheory_LatPair_FF_apply
import Theorems.Thm_GlobalTheory_LatPair_Gs_apply
import Theorems.Thm_GlobalTheory_LatPair_Model_FFStar_FF
import Theorems.Thm_GlobalTheory_LatPair_Model_FF_dia
import Theorems.Thm_GlobalTheory_LatPair_Model_FF_eq_D_Gs
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero
import Theorems.Thm_GlobalTheory_LatPair_cross_dia_right
import Theorems.Thm_GlobalTheory_LatPair_cross_up_ofDual
import Theorems.Thm_GlobalTheory_LatPair_maps_dia
import Theorems.Thm_GlobalTheory_LatPair_phiOne_dia
import Theorems.Thm_GlobalTheory_LatPair_sum_withKer

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
theorem _root_.solution [Fintype n] (hχ : χ ≠ 1) : OperatorIdentities k n M q χ where
  FFStar_formula φ L _ _ f := by
    rw [FFStar_apply, ofDual_lat, sum_withKer L q]
    simp only [cross_up_ofDual]
  FFStar_mul_FF := LinearMap.ext fun φ => by
    rw [Module.End.mul_apply, Model.FFStar_FF q hχ φ]
    simp
  FF_mul_FFStar := LinearMap.ext fun φ => by
    rw [Module.End.mul_apply, FF_FFStar q hχ φ]
    simp
  FFStar_FF_ram φ h := FFStar_FF_ram q hχ h
  FF_FFStar_ram φ h := FF_FFStar_ram q hχ h
  FF_mem_ram φ h := mem_ram (fun c => FF_dia q χ c) h
  FFStar_mem_ram φ h := mem_ram (fun c => FFStar_dia q χ c) h
  D_dia c := D_dia q c
  FF_dia c := FF_dia q χ c
  FF_eq_D_Gs φ h := FF_eq_D_Gs_of_mem_Mram q h
  Gs_mul_GsStar := Gs_mul_GsStar hχ
  D_U_ram φ h := D_U_ram q hχ h
  U_D_ram φ h := U_D_ram q hχ h
  FFStar_dia c := FFStar_dia q χ c
  U_dia c := U_dia q c
  dia_mem_ram c φ h := mem_ram (fun d => dia_dia c d) h
  phiOne_dia c m _ P Q := by
    funext x
    unfold phiOne
    by_cases hM : Maps P Q x
    · rw [if_pos hM, if_pos ((maps_dia c).mpr hM)]
    · rw [if_neg hM, if_neg fun h' => hM ((maps_dia c).mp h')]
  twisted_class_sum ε φ L _ _ f := by
    rw [dia_apply, smul_ofDual, FFStar_ofDual]
    simp [LinearMap.smul_apply]
  sign_FFStar_sign_FF := by
    have e := unit_FFStar_FF (n := n) (M := M) q χ (-1)
    have hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1 := by simp
    rw [hm] at e
    exact e
  sign_ram φ h := by
    have e := LinearMap.congr_fun (unit_FFStar_FF q χ (-1)) φ
    have hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1 := by simp
    rw [hm] at e
    simp only [Module.End.mul_apply] at e
    rw [e, FFStar_FF_ram q hχ h]
  unit_ram c φ h := by
    have e := LinearMap.congr_fun (unit_FFStar_FF q χ c) φ
    simp only [Module.End.mul_apply] at e
    rw [e, FFStar_FF_ram q hχ h]
end GlobalTheory.PairOp
