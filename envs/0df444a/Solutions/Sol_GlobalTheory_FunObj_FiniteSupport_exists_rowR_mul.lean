-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.exists_rowR_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:16:06.480797+00:00
-- url     : https://prove2.me/submissions/ae22e61d-4ff9-4b05-b452-b18d682a80b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_exists_symR_mul
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_moveArgs_theta
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_comap_symR_congr
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_mul_reindex
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_bd_submatrix
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_bd_reindex_iff
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_char_eq_one
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_tensor_shift
import Theorems.Thm_GlobalTheory_FunObj_fill_theta
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mono
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_bd_zero
import Theorems.Thm_GlobalTheory_RootEx_Supp_exists_bd_of_char
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {G : Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
  [ν.IsAddHaarMeasure]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution (hψ : ψ ≠ 1) {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (s : kˣ) : ∃ δ : ValueGroupWithZero k, ∀ (keep : Bool) (g : G.VertexGroup) (x : ColArgs G) (y : RowArgs G)
      (j : ℕ) (hj : j < G.m - 2), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 →
      Bd (valuation k (s : k)) (g (G.m, j)).val → Bd (valuation k (s : k)) ((g (G.m, j))⁻¹).val →
      ∃ r ∈ rowR hs (j := j + 1) (by omega), ∃ w : GL (Fin (G.rank (G.m, j + 1))) k,
        Bd δ w.val ∧ Bd δ (w⁻¹).val ∧ g (G.m, j + 1) = r * w := by
  obtain ⟨γ₂, hγ₂⟩ := exists_bd_of_char ψ hψ (ϖ ^ e * s⁻¹)
  set γ : ValueGroupWithZero k := max 1 (max (valuation k (s : k)) γ₂) with hγ
  have g0 : 1 ≤ γ := le_max_left _ _
  have g1 : valuation k (s : k) ≤ γ := (le_max_left _ _).trans (le_max_right _ _)
  have g2 : γ₂ ≤ γ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨γ * γ, fun keep g x y j hj hne hb1 hb2 => ?_⟩
  have hj1 : j < G.m - 1 := by omega
  have hf1 : topRank G (j + 1) + (G.m - 2 - j) = G.rank (G.m, j + 1) := by have := topRank_add hs (j + 1); omega
  have hf2 : topRank G j + (G.m - 2 - j + 1) = G.rank (G.m, j) := by have := topRank_add hs j; omega
  obtain ⟨v, hv⟩ : ∃ v : Vars G, T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp only [flatTensor, flatIntegrand, moved, Grid.pathAct, hcon, mul_zero, zero_mul, integral_zero]
  have hint : Bd 1 (((g (G.m, j + 1))⁻¹).val * downMap hs x v j * (g (G.m, j)).val) := by
    have h1 : G.moveArgs .one g (fill hs x y v) (.theta G.m j) ∈ matLat _ (stdLat k _) := by
      by_contra hc
      exact hv (hT.2.1 _ _ (by simp [oppositePath]; omega) hc)
    rw [moveArgs_theta, fill_theta, transpose_transpose, mem_matLat_stdLat] at h1
    exact fun r t => h1 t r
  have h1 : Bd γ (((frameGL hf1 (g (G.m, j + 1)))⁻¹).val * stepPt (c := G.m - 2 - j) (x j) (v ⟨j, hj1⟩)) := by
    have h2 := hint.mul hb2
    rw [one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, downMap, dif_pos hj1, mul_reindex hf1,
      bd_reindex_iff, map_inv] at h2
    exact h2.mono g1
  obtain ⟨r, hr, w, hw1, hw2, hrw⟩ := exists_symR_mul (δ := valuation k ((ϖ ^ e * s⁻¹ : kˣ) : k)) (by omega) ψ g0
    (fun a ha => (hγ₂ a ha).trans g2) _ _ _ h1 fun d hd1 hd2 hd3 => by
      have hd : IsAuxiliaryHeckeCharacter (Pi.single (⟨j, hj1⟩ : Fin (G.m - 1)) d : Shifts G) := fun i => by
        by_cases hi : i = ⟨j, hj1⟩
        · subst hi; rw [Pi.single_eq_same]; exact ⟨hd1, hd2⟩
        · rw [Pi.single_eq_of_ne hi]; exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
      have h3 := char_eq_one hs ψ ν hne hd fun v => ?_
      · rw [Finset.sum_eq_single (⟨j, hj1⟩ : Fin (G.m - 1)), Pi.single_eq_same] at h3
        · exact h3
        · intro i _ hi; rw [Pi.single_eq_of_ne hi]; simp [ch]
        · simp
      · have h5 := tensor_shift hs hT g x y v hd fun l hl => ?_
        · simp only [moved, Grid.pathAct, h5]
        · by_cases hl' : l = j
          · subst hl'
            rw [Pi.single_eq_same, mul_reindex hf1, map_inv]
            have h4 := ((bd_reindex_iff (frame hf1) (frame hf2)).2 hd3).mul hb1
            simpa [mul_assoc] using h4
          · rw [Pi.single_eq_of_ne (fun h => hl' (congrArg Fin.val h))]
            simpa using bd_zero _
  refine ⟨(frameGL hf1).symm r, ?_, (frameGL hf1).symm w, bd_submatrix hw1 _ _, ?_, ?_⟩
  · rw [rowR, toFrame, comap_symR_congr (c' := G.m - 2 - j) (by omega) _ hf1]
    simpa using hr
  · rw [← map_inv]; exact bd_submatrix hw2 _ _
  · rw [← map_mul, ← hrw, MulEquiv.symm_apply_apply]
end GlobalTheory.FunObj.FiniteSupport
