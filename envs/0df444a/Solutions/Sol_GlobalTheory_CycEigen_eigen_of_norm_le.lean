-- Prove2me | solution 1 for GlobalTheory.CycEigen.eigen_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:28:46.995652+00:00
-- url     : https://prove2.me/submissions/048b73a3-6e5c-4000-bea0-2f5f5c205b1b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrame
import Theorems.Thm_GlobalTheory_CycEigen_hinf_le_gj
import Theorems.Thm_GlobalTheory_CycEigen_gj_le
import Theorems.Thm_GlobalTheory_CycEigen_norm_chiC
import Theorems.Thm_GlobalTheory_CycEigen_chiC_hinf
import Theorems.Thm_GlobalTheory_CycEigen_act_inC
import Theorems.Thm_GlobalTheory_CycEigen_chiC_mem_inC
import Theorems.Thm_GlobalTheory_CycEigen_mem_inC_iff
import Theorems.Thm_GlobalTheory_CycEigen_twAct_fixed_eq_zero
import Theorems.Thm_GlobalTheory_T_cyclotomicTower_fixed_iff_mem_completedIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_tate_decomposition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CycEigen
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l) (hy1 : ∀ a, ‖y a‖ ≤ 1)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : chiC χ u g • (U g).mulVec y = y := by
  obtain ⟨hg, -, hU, -, hH, hU1⟩ := hF
  obtain ⟨hdec, hdir, -, hmul, hstab, -⟩ := GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K m hm.1
  have hO : ∀ a, y a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act hact K (y a) (hy1 a)).1 fun h hh => ?_
    have := congrFun (hy h (hinf_le_gj K m hh)) a
    simpa [twAct, chiC_hinf hχ K u hh, hH h hh] using this
  choose y0 hy0 x hx hsum using fun a => hdec (y a) (hO a)
  have hfix : (fun a => act g (y0 a)) = y0 := funext fun a => act_inC hact hg.1 (hy0 a).1
  have hyx : y = y0 + x := funext hsum
  have hadd : twAct act χ u U g y = twAct act χ u U g y0 + twAct act χ u U g x := by
    have e : (fun a => act g (y a)) = (fun a => act g (y0 a)) + fun a => act g (x a) := by
      funext a; rw [hsum a, map_add]; rfl
    simp only [twAct]
    rw [e, Matrix.mulVec_add, smul_add]
  have hc : chiC χ u g ∈ intC (Ks K m) := ⟨chiC_mem_inC χ u g _, (norm_chiC hχ u g).le⟩
  have hX : ∀ a, twAct act χ u U g x a ∈ Xj K m := by
    intro a
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact hmul _ hc _ ((Xj K m).sum_mem fun b _ =>
      hmul _ (hU g hg.1 a b) _ (hstab g (gj_le K m hg.1) _ (hx b)))
  have hK : ∀ a, twAct act χ u U g y0 a - y0 a ∈ inC (Ks K m) := by
    intro a
    rw [mem_inC_iff]
    simp only [twAct, hfix, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact sub_mem (mul_mem ((mem_inC_iff _ _).1 hc.1) (sum_mem fun b _ =>
      mul_mem ((mem_inC_iff _ _).1 (hU g hg.1 a b).1) ((mem_inC_iff _ _).1 (hy0 b).1)))
      ((mem_inC_iff _ _).1 (hy0 a).1)
  have hrel : ∀ a, twAct act χ u U g y0 a - y0 a = x a - twAct act χ u U g x a := by
    intro a
    have h1 := congrFun (hadd.symm.trans (hy g hg.1)) a
    rw [Pi.add_apply, hsum a] at h1
    linear_combination h1
  have hzero : ∀ a, twAct act χ u U g y0 a - y0 a = 0 := fun a =>
    hdir _ (hK a) _ ((Xj K m).sub_mem (hx a) (hX a)) 0 (by rw [pow_zero, one_mul]; exact hrel a)
  have hx0 : x = 0 := by
    refine twAct_fixed_eq_zero hact hχ hm hg U (hU g hg.1) hU1 u x hx ?_
    funext a
    exact (sub_eq_zero.1 ((hrel a).symm.trans (hzero a))).symm
  rw [hx0, add_zero] at hyx
  have h2 := hy g hg.1
  rw [hyx] at h2 ⊢
  rwa [twAct, hfix] at h2
end GlobalTheory.CycEigen
