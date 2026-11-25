-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.solve_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:16.486647+00:00
-- url     : https://prove2.me/submissions/eb6d928f-bec3-435e-8a99-5f1b8721dd4d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_root_mem
import Theorems.Thm_GlobalTheory_Cyc_TateS_Gj_le
import Theorems.Thm_GlobalTheory_Cyc_TateS_Gj_fix
import Theorems.Thm_GlobalTheory_Cyc_TateS_prim_lift
import Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_le
import Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_le_of
import Theorems.Thm_GlobalTheory_Cyc_TateS_mem_Xalg
import Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_alg
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_coe
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_algC
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_prim_sub_one
import Theorems.Thm_GlobalTheory_Cyc_TateS_gen_root
import Theorems.Thm_GlobalTheory_T_exists_cyclotomicTowerLevelGenerator_properties
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono


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
    {g : GQ l} (hg : IsGen χ K j g) {ζ : PadicComplex l} (hζ : IsPrimitiveRoot ζ l)
    {x : PadicComplex l} (hx : x ∈ Xalg K j) :
    ∃ y ∈ Xj K j, y ∈ algC K ∧ act g y - y = (ζ - 1) * x := by
  have hp : l.Prime := Fact.out
  let B : AddSubgroup (PadicComplex l) :=
    { carrier := {x | ∃ y ∈ Xj K j, y ∈ algC K ∧ act g y - y = (ζ - 1) * x}
      zero_mem' := ⟨0, zero_mem _, zero_mem _, by simp⟩
      add_mem' := by
        rintro a b ⟨y, hy, hy', h⟩ ⟨y', hz, hz', h'⟩
        exact ⟨y + y', add_mem hy hz, add_mem hy' hz', by rw [map_add]; linear_combination h + h'⟩
      neg_mem' := by
        rintro a ⟨y, hy, hy', h⟩
        exact ⟨-y, neg_mem hy, neg_mem hy', by rw [map_neg]; linear_combination -h⟩ }
  refine Xalg_le_of K j B (fun i hi z y hz hy hy1 => ?_) hx
  obtain ⟨b, rfl⟩ : ∃ b, i = j + b + 1 := ⟨i - j - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hy
  have hg' := ((GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ hact hχ K j hj).2 g hg).1 b
  obtain ⟨η, hη, hgz⟩ := gen_root hχ K hg' hz
  obtain ⟨ζ₀, rfl, hζ₀⟩ := prim_lift hp.ne_zero hζ
  have hη1 : η - 1 ≠ 0 := sub_ne_zero.2 (hη.ne_one hp.one_lt)
  have hj1 : 1 ≤ j + b := by have := hj.1; omega
  have hmem : ∀ {e : Om l}, IsPrimitiveRoot e l → e - 1 ∈ Ks K (j + b) := fun h =>
    sub_mem (Ks_mono K hj1 (root_mem K (by rw [pow_one, h.pow_eq_one]))) (one_mem _)
  set w : Om l := (ζ₀ - 1) / (η - 1) * y with hw
  have hwK : w ∈ Ks K (j + b) := mul_mem (div_mem (hmem hζ₀) (hmem hη)) hy
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, norm_div, norm_prim_sub_one hζ₀, ← norm_prim_sub_one hη,
      div_self (norm_ne_zero_iff.2 hη1), one_mul]
    exact hy1
  have hu : algebraMap (Om l) (PadicComplex l) (z * w) ∈ Xalg K j :=
    mem_Xalg K hi hz (by rwa [Nat.add_sub_cancel]) hw1
  set u := algebraMap (Om l) (PadicComplex l) (z * w) with hu'
  have hgk : ∀ k : ℕ, g ^ k ∈ (K0 K).fixingSubgroup := fun k => pow_mem (Gj_le K j hg.1) k
  refine ⟨∑ k ∈ Finset.range (l ^ b), act (g ^ k) u, sum_mem fun k _ =>
    (GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.2.2.2.1 _ (hgk k) _ (Xalg_le K j hu),
    sum_mem fun k _ => act_algC hact K (hgk k) (Xalg_alg K j hu), ?_⟩
  have hs : act g (∑ k ∈ Finset.range (l ^ b), act (g ^ k) u) -
      ∑ k ∈ Finset.range (l ^ b), act (g ^ k) u = act (g ^ l ^ b) u - act (g ^ 0) u := by
    rw [← Finset.sum_range_sub (fun k => act (g ^ k) u), map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ', map_mul]
    rfl
  rw [hs, pow_zero, map_one, hu', act_coe hact, map_mul (g ^ l ^ b), hgz, Gj_fix K hg'.1 hwK]
  change _ - algebraMap (Om l) (PadicComplex l) (z * w) = _
  rw [← map_one (algebraMap (Om l) (PadicComplex l)), ← map_sub, ← map_sub, ← map_mul]
  congr 1
  rw [hw]
  field_simp
end GlobalTheory.Cyc.TateS
