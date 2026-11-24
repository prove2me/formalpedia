-- Prove2me | solution 1 for GlobalTheory.FunObj.flatTensor_pureTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:32.74554+00:00
-- url     : https://prove2.me/submissions/332bbebd-63db-4507-82fd-7acf45856350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_FunObj_integral_prod_mul_of_split
import Theorems.Thm_GlobalTheory_FunObj_measurePreserving_elim
import Theorems.Thm_GlobalTheory_FunObj_keptPart_joinVars
import Theorems.Thm_GlobalTheory_FunObj_stepPt_joinVars
import Theorems.Thm_GlobalTheory_FunObj_ch_add_keptPt
import Theorems.Thm_GlobalTheory_FunObj_integrable_step
import Theorems.Thm_GlobalTheory_FunObj_phase_eq
import Theorems.Thm_GlobalTheory_FunObj_pureTensor_fill
import Theorems.Thm_GlobalTheory_FunObj_stepDatum_mem_SB
import Theorems.Thm_GlobalTheory_FunObj_continuous_pairPhase
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable {ψ}
namespace GlobalTheory.FunObj
theorem _root_.solution [ν.IsAddHaarMeasure] (hm : 0 < G.m) (hψ : Continuous ψ)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (hφ : ∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) (x : ColArgs G) (y : RowArgs G) :
    Integrable (flatIntegrand hs ψ (G.lines₂ (oppositePath G.m) φ) x y) (varsVol G ν) ∧
    Integrable (contractIntegrand hs ψ ν φ x) (keptVol G ν) ∧
    flatTensor hs ψ ν (G.lines₂ (oppositePath G.m) φ) x y =
      (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ *
        ∫ w, contractIntegrand hs ψ ν φ x w ∂(keptVol G ν) := by
  classical
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hchar : ∀ (s : Finset (Fin (G.m - 1))) (f : Fin (G.m - 1) → k),
      (ψ (-∑ j ∈ s, f j) : ℂ) = ∏ j ∈ s, (ψ (-f j) : ℂ) := fun s f => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_add, AddChar.map_add_eq_mul,
        Circle.coe_mul, ih]
  obtain ⟨h1, h2, h3⟩ := integral_prod_mul_of_split
    (g := fun j : Fin (G.m - 1) => joinVars (k := k) (n := Fin (topRank G (j + 1))) (c := G.m - 2 - j)
      (n' := Fin (topRank G j)))
    (fun j => measurePreserving_elim ν (stepVarEquiv _ _ _))
    (p := fun j => keptPart) (fun j => measurable_pi_lambda _ fun _ => measurable_pi_apply _)
    (fun j => keptPart_joinVars)
    (fun j => by convert integrable_step hψ ν (stepDatum_mem_SB hs j (hφ j j.2)) (x j))
    (H := fun w => (ψ (-pairPhase x w) : ℂ))
    (continuous_subtype_val.comp (hψ.comp (continuous_pairPhase x).neg)).measurable (fun w => (Circle.norm_coe _).le)
  have e1 : flatIntegrand hs ψ (G.lines₂ (oppositePath G.m) φ) x y = fun e =>
      ((∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ) *
      ((∏ j : Fin (G.m - 1), stepDatum hs φ j (stepPt (x j) (e j)) * (ψ (-ch (stepPt (x j) (e j))) : ℂ)) *
        (ψ (-pairPhase x fun j => keptPart (e j)) : ℂ)) := by
    funext e
    rw [flatIntegrand, pureTensor_fill hs hm, phase_eq, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, hchar,
      Finset.prod_mul_distrib]
    ring
  simp only [stepPt_joinVars, ch_add_keptPt] at h2 h3
  rw [flatTensor, e1, integral_const_mul]
  unfold varsVol keptVol contractIntegrand flatStep opE
  refine ⟨Integrable.const_mul (by convert h1) _, by convert h2, congrArg _ (by convert h3)⟩
end GlobalTheory.FunObj
