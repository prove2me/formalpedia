-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.est_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:17.662667+00:00
-- url     : https://prove2.me/submissions/8cd2b096-07b4-421c-be26-501a4b8ff472

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_Gj_le
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_coe
import Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_le
import Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_alg
import Theorems.Thm_GlobalTheory_Cyc_TateS_int_decomp
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_algC
import Theorems.Thm_GlobalTheory_Cyc_TateS_fixed_alg_eq_zero
import Theorems.Thm_GlobalTheory_Cyc_TateS_solve_alg
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_l
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_le_one
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_fix
import Theorems.Thm_GlobalTheory_Cyc_TateS_zeta_sub_one_mem
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_le_one
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono
import Theorems.Thm_GlobalTheory_UnramValue_norm_l
import Theorems.Thm_GlobalTheory_UnramValue_norm_le_one


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
    {d : PadicComplex l} (hd : d ∈ Xalg K j) (n : ℕ) (hn : ‖act g d - d‖ ≤ (l : ℝ)⁻¹ ^ n) :
    ‖(ζ - 1) * d‖ ≤ (l : ℝ)⁻¹ ^ n := by
  have hp : l.Prime := Fact.out
  have T1 := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1
  have hg0 := Gj_le K j hg.1
  have hdX := Xalg_le K j hd
  have hdA := Xalg_alg K j hd
  have hwX : act g d - d ∈ Xj K j := sub_mem (T1.2.2.2.2.1 g hg0 d hdX) hdX
  obtain ⟨m, hm⟩ : act g d - d ∈ algC K := sub_mem (act_algC hact K hg0 hdA) hdA
  obtain ⟨a, ha, hwa⟩ := mem_inC.1 hm
  have hlO : ((l : Om l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hlC : ((l : PadicComplex l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hnl : ‖(l : PadicComplex l) ^ n‖ = (l : ℝ)⁻¹ ^ n := by rw [norm_pow, norm_l]
  have hcoe : algebraMap (Om l) (PadicComplex l) (a / (l : Om l) ^ n) =
      (act g d - d) / (l : PadicComplex l) ^ n := by
    rw [map_div₀, map_pow, map_natCast, hwa]
  obtain ⟨o, ho, d', hd', hod⟩ := int_decomp K hj.1 m (a / (l : Om l) ^ n)
    (div_mem (Ks_mono K (Nat.le_add_left _ _) ha) (pow_mem (natCast_mem _ _) _))
    (by
      rw [← norm_coe, hcoe, norm_div, div_le_one (norm_pos_iff.2 hlC), hnl]
      exact hn)
  rw [hcoe, div_eq_iff hlC] at hod
  have hmul : ∀ {x : PadicComplex l}, x ∈ Xj K j → (l : PadicComplex l) ^ n * x ∈ Xj K j := by
    intro x hx
    have := nsmul_mem hx (l ^ n)
    rwa [nsmul_eq_mul, Nat.cast_pow] at this
  have ho0 : algebraMap (Om l) (PadicComplex l) o = 0 :=
    T1.2.1 _ (mem_inC.2 ⟨o, ho, rfl⟩) _ (sub_mem hwX (hmul (Xalg_le K j hd'))) n
      (by rw [hod]; ring)
  rw [ho0, zero_add] at hod
  obtain ⟨y, hyX, hyA, hy⟩ := solve_alg hact hχ K hj hg hζ hd'
  have hz := zeta_sub_one_mem K hj.1 hζ
  have h0 := fixed_alg_eq_zero hact hχ K hj hg
    (x := (ζ - 1) * d - (l : PadicComplex l) ^ n * y)
    (sub_mem (T1.2.2.2.1 _ hz d hdX) (hmul hyX))
    (sub_mem (mul_mem ⟨j, hz.1⟩ hdA) (mul_mem (pow_mem (natCast_mem _ _) _) hyA))
    (by
      rw [map_sub, map_mul, map_mul, act_fix hact K hg.1 hz.1, map_pow, map_natCast]
      linear_combination (ζ - 1) * hod - (l : PadicComplex l) ^ n * hy)
  rw [sub_eq_zero.1 h0, norm_mul, hnl]
  exact mul_le_of_le_one_right (by positivity) (norm_le_one hact hχ K hj.1 hyX)
end GlobalTheory.Cyc.TateS
