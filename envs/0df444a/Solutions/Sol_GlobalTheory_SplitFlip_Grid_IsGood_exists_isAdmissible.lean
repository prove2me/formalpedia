-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.IsGood.exists_isAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:25.752803+00:00
-- url     : https://prove2.me/submissions/9345e3b4-1422-4f3d-8000-ddf2409df8e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO
import Theorems.Thm_GlobalTheory_SplitFlip_hasDepth_indicator
import Theorems.Thm_GlobalTheory_SplitFlip_Grid_isTensor_pureTensor
import Theorems.Thm_GlobalTheory_SplitFlip_isOpen_detCong
import Theorems.Thm_GlobalTheory_SplitFlip_mul_mul_mem_matLat_iff
import Theorems.Thm_GlobalTheory_SplitFlip_Assignment_read_mem_KO
import Theorems.Thm_GlobalTheory_SplitFlip_Grid_IsGood_condLE_kappa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
namespace Grid.IsGood
theorem _root_.solution {G : Grid k} {ϖ : kˣ} {ψ : AddChar k Circle} {e : ℕ} (h : G.IsGood ϖ ψ e)
    (hϖ : IsUnif ϖ) (s : Assignment) {γ : List Edge} (hγ : IsPath γ) (hm : ∀ b ∈ γ, b.InGrid G.m) :
    ∃ S : G.PiLocalization₂, S.path = γ ∧ S.IsAdmissible s ϖ e ∧ S.tensor 0 = 1 := by
  refine ⟨⟨γ, fun X => detCong (ϖ ^ e) _, G.lines₂ γ fun b =>
      Set.indicator (SetLike.coe (matLat (Fin (G.rank b.tgt)) (stdLat k (Fin (G.rank b.src))))) 1⟩, rfl,
    ⟨hγ, fun X _ => ⟨isOpen_detCong _ _, inf_le_left⟩,
      G.isTensor_pureTensor ϖ e γ _ fun b _ => hasDepth_indicator hϖ e _, fun X _ u hu => ?_⟩, ?_⟩
  · have hg : ∀ Y, (Pi.mulSingle X u : G.VertexGroup) Y ∈ detCong (ϖ ^ e) _ := fun Y => by
      by_cases hY : Y = X
      · subst hY; simpa using hu
      · simp [hY, one_mem]
    generalize (Pi.mulSingle X u : G.VertexGroup) = g at hg
    funext x
    have h1 : (γ.map (G.edgeFactor s g)).prod = 1 := List.prod_eq_one fun c hc => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      simp only [Grid.edgeFactor, h.condLE_kappa (hm b hb) _ _ (hg _).2,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (s.read_mem_KO (hg _).1))]
      simp
    simp only [Grid.pathAct, h1, one_mul, Grid.lines₂]
    refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
    have h2 := mul_mul_mem_matLat_iff (inv_mem (s.read_mem_KO (hg b.tgt).1)) (s.read_mem_KO (hg b.src).1) (x b)
    simp only [Grid.moveArgs]
    by_cases hx : x b ∈ matLat _ (stdLat k _)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h2.2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun H => hx (h2.1 H))]
  · refine List.prod_eq_one fun c hc => ?_
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hc
    exact Set.indicator_of_mem (zero_mem (matLat _ (stdLat k _))) _
end Grid.IsGood
end GlobalTheory.SplitFlip
