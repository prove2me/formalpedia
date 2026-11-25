-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.thetaVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:47.13801+00:00
-- url     : https://prove2.me/submissions/507724de-824f-455f-b09d-f47cb8107255

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_stdH_herm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_std_selfDual
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_std_semiChar
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_productEvenTheta_zero_eq_one
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_productEvenTheta_mem_thetaSpace
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_std_line
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_fourthRoot
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_analytic_inter
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_inter_smul
import Theorems.Thm_GlobalTheory_ThetaInter_inter_inter
import Theorems.Thm_GlobalTheory_ThetaInter_inter_mem_fixedBy


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
variable {n : Type} [Fintype n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution : ThetaVector := by
  intro L ω₀ n _ _ h Λ α β g S κ hκ
  set A := imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) with hA
  have f1 : Finite (A ⧸ (stdLat L (Fin 4 × n)).addSubgroupOf A) := Nat.finite_of_card_ne_zero S.idx₁
  have f2 : Finite (stdLat L (Fin 4 × n) ⧸ A.addSubgroupOf (stdLat L (Fin 4 × n))) :=
    Nat.finite_of_card_ne_zero S.idx₂
  have hH := stdH_herm L (n := Fin 4 × n)
  have hd := std_selfDual L (n := Fin 4 × n)
  have hs := std_semiChar L S.per S.betaStd
  have hF := productEvenTheta_mem_thetaSpace L ω₀ S.betaStd
  have hiso : ∀ x y, stdH L (Fin 4 × n) (g x) (g y) = matH (blk4 h) x y := S.isom
  have hK : inter (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n)) A (F0 L ω₀ (Fin 4 × n)) ∈ Th (stdH L _) β A :=
    ⟨analytic_inter _ _ _ _ hF.1, inter_mem_fixedBy hH hs S.selfDual S.betaSemi hF.2⟩
  set K := inter (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n)) A (F0 L ω₀ (Fin 4 × n)) with hKdef
  have hk : kernel4 L ω₀ Λ β g = fun z => K (g z) := rfl
  have hK0 : K ≠ 0 := by
    intro h0
    have h1 := inter_inter hH hd S.selfDual hs hF.2
    rw [← hKdef, h0, ← zero_smul ℂ (0 : (Fin 4 × n → ℂ) → ℂ), inter_smul, zero_smul] at h1
    have := congrFun h1 0
    rw [productEvenTheta_zero_eq_one L S.half] at this
    exact zero_ne_one this
  have hP : kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) := by
    rw [hk]
    refine ⟨fun z _ => (hK.1 _ trivial).comp
      ((LinearMap.toContinuousLinearMap (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))).analyticAt z),
      fun x hx z => ?_⟩
    have := hK.2 (g x) ⟨x, hx, rfl⟩ (g z)
    rw [opU, hiso, hiso, ← map_add, S.betaAlpha] at this
    exact this
  have hne : κ • kernel4 L ω₀ Λ β g ≠ 0 := by
    refine smul_ne_zero hκ fun h0 => hK0 (funext fun z => ?_)
    simpa [hk] using congrFun h0 (g.symm z)
  have hline : ∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ),
      ∃ c : ℂ, G = c • κ • kernel4 L ω₀ Λ β g := by
    intro G hG
    have hG' : (fun z => G (g.symm z)) ∈ Th (stdH L _) β A := by
      refine ⟨fun z _ => (hG.1 _ trivial).comp
        ((LinearMap.toContinuousLinearMap (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))).analyticAt z), ?_⟩
      rintro _ ⟨x, hx, rfl⟩ z
      obtain ⟨y, rfl⟩ := g.surjective z
      change β (g x) * opU _ (g x) _ (g y) = G (g.symm (g y))
      rw [opU, hiso, hiso, ← map_add, S.betaAlpha, g.symm_apply_apply, g.symm_apply_apply]
      exact hG.2 x hx y
    have h1 := std_line L S.half S.betaStd
      (differentiableOn_univ.1 (analytic_inter (stdH L _) β A (stdLat L _) hG'.1).differentiableOn)
      (inter_mem_fixedBy hH S.betaSemi hd hs hG'.2)
    have h2 := inter_inter hH S.selfDual hd S.betaSemi hG'.2
    rw [h1, inter_smul, ← hKdef] at h2
    generalize inter (stdH L (Fin 4 × n)) β A (stdLat L _) (fun z => G (g.symm z)) 0 = c at h2
    refine ⟨c * κ⁻¹, funext fun z => ?_⟩
    have := congrFun h2 (g z)
    rw [g.symm_apply_apply] at this
    rw [← this, smul_smul, inv_mul_cancel_right₀ hκ, hk]
    rfl
  obtain ⟨e, u⟩ := fourthRoot n h Λ α S.alpha0 _ (Submodule.smul_mem _ κ hP) hne hline
  refine ⟨e, fun θ hθ h4 => ⟨?_, u θ hθ h4⟩⟩
  rintro rfl
  apply hne
  rw [← h4]
  funext z
  simp [tens4]
end GlobalTheory.Mem.Col2.ThetaVec
