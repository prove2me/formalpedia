-- Prove2me | solution 1 for GlobalTheory.CycCoinv.torsion_coinvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:31.813216+00:00
-- url     : https://prove2.me/submissions/02177f39-4c95-49c5-96dd-f6c1fa23063b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Theorems.Thm_GlobalTheory_CycCoinv_tors_int
import Theorems.Thm_GlobalTheory_CycCoinv_add_mem_Ohat
import Theorems.Thm_GlobalTheory_CycCoinv_algebraMap_mem
import Theorems.Thm_GlobalTheory_CycCoinv_quot_mem
import Theorems.Thm_GlobalTheory_CycCoinv_norm_chi
import Theorems.Thm_GlobalTheory_CycCoinv_norm_prod_chi
import Theorems.Thm_GlobalTheory_CycCoinv_act_fix
import Theorems.Thm_GlobalTheory_CycCoinv_twAct_add
import Theorems.Thm_GlobalTheory_CycSeries_perturbation
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_fix
import Theorems.Thm_GlobalTheory_T_aeval_prod_eq_zero_hodgeTate_cyclotomicFrame
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.CycCoinv
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycCoinv
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (w w' : Fin r → PadicComplex l) (k : ℕ), (∀ a, w a ∈ Ohat K) → (∀ a, w' a ∈ Ohat K) → twAct act χ i U g w' - w' = (l : PadicComplex l) ^ k • w → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Ohat K) ∧ twAct act χ i U g y - y = (l : PadicComplex l) ^ (max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • w := by
  intro l hl act χ hact hχ K m r hm U g hF J hHT i w w' k hw hw' h
  have heig := GlobalTheory.T.aeval_prod_eq_zero_hodgeTate_cyclotomicFrame l act χ hact hχ K m r hm U g hF J hHT
  obtain ⟨hg, -, hUO, -, -, hU1⟩ := hF
  have hU : ∀ a b, U g a b ∈ intR (Ks K m) := hUO g hg.1
  obtain ⟨hdec, huniq, hXO, hmul, hstab, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K m hm.1
  have hgX := hstab g (IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K m) hg.1)
  choose w0 hw0 wx hwx hwe using fun a => hdec _ (hw a)
  choose v0 hv0 vx hvx hve using fun a => hdec _ (hw' a)
  obtain rfl : w = w0 + wx := funext hwe
  obtain rfl : w' = v0 + vx := funext hve
  have hl0 : (l : PadicComplex l) ≠ 0 := Nat.cast_ne_zero.2 hl.1.ne_zero
  have hchi : ∀ u : ℤ, chiC χ u g = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ u) :=
    fun u => by simp [chiC]
  have hcO : ∀ u : ℤ, chiC χ u g ∈ intR (Ks K m) := fun u => by
    rw [hchi]
    exact algebraMap_mem _ _ (by rw [norm_zpow, norm_chi hm hg, one_zpow])
  have hcc : chiC χ i g * chiC χ (-i) g = 1 := by
    rw [hchi, hchi, ← map_mul, ← zpow_add₀ (χ g).ne_zero]; simp
  have htw : ∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ intR (Ks K m)) →
      twAct act χ i U g y - y = chiC χ i g • ((U g).mulVec y - chiC χ (-i) g • y) := by
    intro y hy
    have : (fun a => act g (y a)) = y := funext fun a => act_fix hact hg.1 (hy a).1
    rw [twAct, this, smul_sub, smul_smul, hcc, one_smul]
  have hlk : (l : PadicComplex l) ^ k ∈ intR (Ks K m) := pow_mem (natCast_mem _ _) _

  have h0 : twAct act χ i U g v0 - v0 = (l : PadicComplex l) ^ k • w0 := by
    rw [twAct_add] at h
    funext a
    have hO : (twAct act χ i U g v0 - v0) a - (l : PadicComplex l) ^ k * w0 a ∈ intR (Ks K m) := by
      rw [htw v0 hv0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact sub_mem (mul_mem (hcO i) (sub_mem (sum_mem fun b _ => mul_mem (hU a b) (hv0 b))
        (mul_mem (hcO _) (hv0 a)))) (mul_mem hlk (hw0 a))
    have hX : (l : PadicComplex l) ^ k * wx a - (twAct act χ i U g vx a - vx a) ∈ Xj K m := by
      refine sub_mem (hmul _ hlk _ (hwx a)) (sub_mem ?_ (hvx a))
      simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact hmul _ (hcO i) _ (sum_mem fun b _ => hmul _ (hU a b) _ (hgX _ (hvx b)))
    have := huniq _ hO.1 _ hX 0 (by
      have ha := congrFun h a
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢
      linear_combination ha)
    exact sub_eq_zero.1 this
  set N := max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) with hN

  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)
  obtain ⟨yx, hyx, hyxe⟩ := (GlobalTheory.CycSeries.perturbation l act χ hact hχ K m hm g hg r U hU hU1 i).2 ζ hζ
    (((l : PadicComplex l) ^ N / (ζ - 1)) • wx)
    (fun a => hmul _ (quot_mem K hm.1 hζ (le_max_left _ _)) _ (hwx a))
  rw [smul_smul, mul_div_cancel₀ _ hz0] at hyxe

  have h1 : (U g).mulVec v0 - chiC χ (-i) g • v0
      = (chiC χ (-i) g * (l : PadicComplex l) ^ k) • w0 := by
    rw [mul_smul, ← h0, htw v0 hv0, smul_smul, mul_comm, hcc, one_smul]
  have hci : chiC χ (-i) g ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  obtain ⟨y, hy, hye⟩ := tors_int (intR (Ks K m)) (U g) hU (fun u => chiC χ (-u) g)
    (fun u => hcO _) J heig i w0 v0 hw0 _ (mul_ne_zero hci (pow_ne_zero _ hl0)) h1
  set β : ℚ_[l] := ∏ u ∈ J.erase i, ((χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u)) with hβ
  have hβn := norm_prod_chi hm hg J i
  rw [← hβ] at hβn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have hβ0 : β ≠ 0 := by
    rw [← norm_pos_iff, hβn]; positivity
  have hβe : ∏ u ∈ J.erase i, (chiC χ (-i) g - chiC χ (-u) g)
      = algebraMap ℚ_[l] (PadicComplex l) β := by
    simp only [hchi, hβ, map_prod, map_sub]
  have ht : algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) ∈ intR (Ks K m) := by
    apply algebraMap_mem
    rw [norm_div, div_le_one (norm_pos_iff.2 hβ0), hβn, norm_pow, Padic.norm_p]
    exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1.le) (le_max_right _ _)
  set t := algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) with htd
  have htβ : t * algebraMap ℚ_[l] (PadicComplex l) β = (l : PadicComplex l) ^ N := by
    rw [htd, ← map_mul, div_mul_cancel₀ _ hβ0, map_pow, map_natCast]
  have hy0 : ∀ a, ((t * chiC χ (-i) g) • y) a ∈ intR (Ks K m) := fun a =>
    mul_mem (mul_mem ht (hcO _)) (hy a)
  refine ⟨(t * chiC χ (-i) g) • y + yx, fun a => add_mem_Ohat K m (hy0 a) (hXO _ (hyx a)), ?_⟩
  have h2 : twAct act χ i U g ((t * chiC χ (-i) g) • y) - (t * chiC χ (-i) g) • y
      = (l : PadicComplex l) ^ N • w0 := by
    rw [htw _ hy0, Matrix.mulVec_smul, smul_comm (chiC χ (-i) g), ← smul_sub, hye, hβe,
      smul_smul, smul_smul, ← htβ]
    congr 1
    linear_combination t * algebraMap ℚ_[l] (PadicComplex l) β * hcc
  rw [twAct_add, smul_add, ← h2, ← hyxe]
  abel
end GlobalTheory.CycCoinv
