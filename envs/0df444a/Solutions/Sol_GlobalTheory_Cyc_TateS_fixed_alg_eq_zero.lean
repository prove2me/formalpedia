-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.fixed_alg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:59.70563+00:00
-- url     : https://prove2.me/submissions/2c564b8b-567c-4870-ad0c-ea52268fa0bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_Gj_fix
import Theorems.Thm_GlobalTheory_Cyc_TateS_coe_inj
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_coe
import Theorems.Thm_GlobalTheory_T_exists_cyclotomicTowerLevelGenerator_properties
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {x : PadicComplex l} (hx : x ∈ Xj K j) (hx' : x ∈ algC K)
    (hfix : act g x = x) : x = 0 := by
  obtain ⟨m, hm⟩ := hx'
  obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
  rw [act_coe hact] at hfix
  have hga : g a = a := coe_inj hfix
  have hpow : ∀ k : ℕ, (g ^ k) a = a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hga, ih]
  have haj : a ∈ Ks K j := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (Ks K j), IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨k, hk⟩ := ((GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ hact hχ K j hj).2 g hg).2.1 σ hσ m
    have h1 := Gj_fix K hk ha
    have h2 : σ = σ * (g ^ k)⁻¹ * g ^ k := by group
    rw [h2, AlgEquiv.mul_apply, hpow, h1]
  exact (GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.1 _ (mem_inC.2 ⟨a, haj, rfl⟩) _ hx 0 (by simp)
end GlobalTheory.Cyc.TateS
