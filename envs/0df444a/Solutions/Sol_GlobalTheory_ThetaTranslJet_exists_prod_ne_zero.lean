-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_prod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:08:52.792219+00:00
-- url     : https://prove2.me/submissions/7c9eb841-3177-4f5a-becb-76e73fec579e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Theorems.Thm_GlobalTheory_ThetaTranslJet_spans_pow
import Theorems.Thm_GlobalTheory_ThetaTranslJet_polyDeriv_eq_pairing
import Theorems.Thm_GlobalTheory_ThetaTranslJet_pairing_eq_zero
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_pairing_ne_zero
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaJet_coeff_single_taylorDir
import Theorems.Thm_GlobalTheory_ThetaJet_sub_affine_mem_sq
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_GlobalTheory_taylorDir_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGauss.transl_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution {σ κ W : Type} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (u : σ → W) (f : κ → W → ℂ) (hf : ∀ k, AnalyticAt ℂ (f k) 0) (hf0 : ∀ k, f k 0 = 0)
    (hsp : ∀ c : σ → ℂ, c ≠ 0 → ∃ k, ∑ i, c i * fderiv ℂ (f k) 0 (u i) ≠ 0)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ s : Fin P.totalDegree → κ, ∀ h : W → ℂ, AnalyticAt ℂ h 0 → h 0 ≠ 0 →
      polyDeriv P u (fun z => (∏ j, f (s j) z) * h z) 0 ≠ 0 := by
  classical
  set m := germIdeal σ ℂ with hm
  have hmem : ∀ x : MvPowerSeries σ ℂ, x ∈ m ↔ MvPowerSeries.constantCoeff x = 0 := fun x => by
    rw [← pow_one m, mem_germIdeal_pow_iff]
    simp [Finsupp.degree_eq_zero_iff]
  have htm : ∀ k, taylorDir u (f k) ∈ m := fun k => by simp [hmem, hf0]
  set J := Submodule.span ℂ (Set.range fun k => taylorDir u (f k)) with hJ
  have hJm : ∀ y ∈ m, ∃ s ∈ J, y - s ∈ m ^ 2 := by
    intro y hy
    have hle : y ∈ J ⊔ (m ^ 2).restrictScalars ℂ := by
      by_contra hne
      obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
      have hφ' : ∀ x ∈ J ⊔ (m ^ 2).restrictScalars ℂ, φ x = 0 := fun x hx => by
        have := Submodule.mem_map_of_mem (f := φ) hx
        rwa [hφ, Submodule.mem_bot] at this
      have hform : ∀ x ∈ m, φ x =
          ∑ i, φ (MvPowerSeries.X i) * MvPowerSeries.coeff (Finsupp.single i 1) x := by
        intro x hx
        have := hφ' _ (Submodule.mem_sup_right (ThetaJet.sub_affine_mem_sq x))
        rw [map_sub, sub_eq_zero, (hmem x).1 hx] at this
        rw [this]
        simp [mul_comm]
      by_cases hc : (fun i => φ (MvPowerSeries.X i)) = 0
      · apply hφ0
        rw [hform y hy]
        simp [congrFun hc]
      · obtain ⟨k, hk⟩ := hsp _ hc
        apply hk
        have := hφ' _ (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
        rw [hform _ (htm k)] at this
        simpa only [ThetaJet.coeff_single_taylorDir u (hf k)] using this
    obtain ⟨s, hs, w, hw, e⟩ := Submodule.mem_sup.1 hle
    exact ⟨s, hs, by rw [← e, add_sub_cancel_left]; exact hw⟩
  have hex : ∃ s : Fin P.totalDegree → κ, pairing P (∏ j, taylorDir u (f (s j))) ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := exists_pairing_ne_zero hP
    obtain ⟨A, hA, hA'⟩ : ∃ A ∈ J ^ P.totalDegree, x - A ∈ m ^ (P.totalDegree + 1) := by
      generalize P.totalDegree = d at hx ⊢
      cases d with
      | zero =>
        refine ⟨MvPowerSeries.constantCoeff x • 1, Submodule.smul_mem _ _ ?_, ?_⟩
        · rw [pow_zero]; exact Submodule.one_le.1 le_rfl
        · simp [hmem]
      | succ d => exact spans_pow m J hJm d x hx
    by_contra hcon
    push Not at hcon
    have h1 := pairing_eq_zero P hA'
    rw [map_sub, sub_eq_zero] at h1
    rw [hJ, Submodule.span_pow] at hA
    refine hx0 (h1.trans ((Submodule.span_le (p := LinearMap.ker (pairing P))).2 ?_ hA))
    intro a ha
    obtain ⟨g, rfl⟩ := Set.mem_pow.1 ha
    choose s hs using fun j => (g j).2
    rw [List.prod_ofFn]
    simp only [← hs]
    exact hcon s
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, fun h hh h0 => ?_⟩
  have e := taylorDir_mul u (Finset.analyticAt_fun_prod Finset.univ fun j _ => hf (s j)) hh
  rw [taylorDir_prod u _ fun j _ => hf (s j)] at e
  rw [polyDeriv_eq_pairing]
  change pairing P (taylorDir u ((fun z => ∏ j, f (s j) z) * h)) ≠ 0
  have h1 : ∏ j, taylorDir u (f (s j)) ∈ m ^ P.totalDegree := by
    simpa using Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ => m) fun j _ => htm (s j)
  have h2 : taylorDir u h - h 0 • 1 ∈ m := by simp [hmem]
  have h3 := pairing_eq_zero P (x := _) (by rw [pow_succ]; exact Ideal.mul_mem_mul h1 h2)
  rw [mul_sub, map_sub, sub_eq_zero, mul_smul_comm, mul_one, map_smul] at h3
  rw [e, h3]
  exact mul_ne_zero h0 hs
end GlobalTheory.ThetaTranslJet
