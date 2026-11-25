-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.std_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:55.249305+00:00
-- url     : https://prove2.me/submissions/2af4cf43-1936-4d53-b79b-59cfb18fb625

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_evenTheta_spans_thetaSpace
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_th0Char_zero
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_stdH_single
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_single_mem

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
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution {ω₀ : ℂ} (h0 : ω₀ / 2 ∉ L.lattice) {α : (n → ℂ) → ℂ}
    (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) {G : (n → ℂ) → ℂ} (hG : Differentiable ℂ G)
    (hF : G ∈ fixedBy (stdH L n) α (stdLat L n)) : G = G 0 • F0 L ω₀ n := by
  have one : ∀ (z : n → ℂ) (i : n), G z = G (Function.update z i 0) * F.th0 L (ω₀ / 2) (z i) := by
    intro z i
    have := evenTheta_spans_thetaSpace L h0 (G := fun x => G (Function.update z i x))
      (hG.comp (fun x => (hasDerivAt_update z i x).differentiableAt)) (fun ω hω x => by
        have h1 := hF _ (single_mem L i hω) (Function.update z i x)
        rw [hα _ (single_mem L i hω), stdChar,
          Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, th0Char_zero]) (by simp),
          opU, stdH_single, stdH_single] at h1
        have h2 : Function.update z i x + Pi.single i ω = Function.update z i (x + ω) := by
          funext j
          by_cases h : j = i
          · subst h; simp
          · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
        rw [h2] at h1
        simpa [opU] using h1) (z i)
    simpa using this
  have all : ∀ (s : Finset n) (z : n → ℂ),
      G z = G (fun i => if i ∈ s then 0 else z i) * ∏ i ∈ s, F.th0 L (ω₀ / 2) (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      intro z
      rw [ih z, one _ i, Finset.prod_insert hi, if_neg hi, mul_assoc]
      congr 2
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  funext z
  rw [all Finset.univ z]
  simp only [Finset.mem_univ, if_true]
  rfl
end GlobalTheory.Mem.Col2.ThetaVec
