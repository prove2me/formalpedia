-- Prove2me | solution 1 for GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:04:50.957401+00:00
-- url     : https://prove2.me/submissions/5f2b6a12-e9e1-4cf8-a041-aa7715b8140d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_exists_unit_valuation_eq_of_adm
import Theorems.Thm_GlobalTheory_QNorm_isSquare_mul_of_nonsquare_units
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits
import Theorems.Thm_GlobalTheory_QNorm_mem_sqSub
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
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → Disjoint S T → (∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) (u : F)) ↔ v ∉ A)) → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := by
  intro F _ _ _ S T hS hST hA
  classical
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  obtain ⟨u, hu, huA⟩ := hA (T.filter fun v =>
    ¬ IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)))
  have huU : u ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits] at hu ⊢
    intro v hv
    exact hu v fun h => hv (Finset.mem_union_left _ h)
  have hsq : u * (a * x) ∈ finSq F T := by
    simp only [finSq, Subgroup.mem_iInf]
    intro v hv
    rw [mem_sqSub, Units.val_mul, map_mul]
    have h := huA v hv
    rw [Finset.mem_filter] at h
    by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F))
    · exact (h.2 fun hh => hh.2 hs).mul hs
    · refine isSquare_mul_of_nonsquare_units F v ?_ _ _ ?_ ?_ (fun hh => h.1 hh ⟨hv, hs⟩) hs
      · rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2, hval]
        exact (hS v (hTS v hv)).1
      · rw [hval]
        exact (mem_sUnits F S u).1 hu v (hTS v hv)
      · rw [hval]
        exact hy v hv
  have hx : x = (u * a)⁻¹ * (u * (a * x)) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup (inv_mem (mul_mem huU haU)) hsq
end GlobalTheory.QNorm
