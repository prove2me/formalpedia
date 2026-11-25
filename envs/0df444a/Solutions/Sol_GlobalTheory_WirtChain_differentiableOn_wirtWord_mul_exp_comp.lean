-- Prove2me | solution 1 for GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:19.561973+00:00
-- url     : https://prove2.me/submissions/4fa9515a-8ab9-40ad-8f5c-d9fde7ee3192

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
import Theorems.Thm_GlobalTheory_WirtChain_ExpSum_const_mul
import Theorems.Thm_GlobalTheory_WirtChain_ExpSum_holo
import Theorems.Thm_GlobalTheory_WirtChain_ExpSum_deriv
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_nil
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
open Classical
namespace GlobalTheory.WirtChain
theorem _root_.solution : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by
  intro Φ I _ _ U V D G t b l hU hV hmaps ht hb hl hGs hGh w z hz
  have key : ∀ w : List (I × Bool), ∃ F, ExpSum U G t l F ∧ ∀ σ ∈ D,
      Set.EqOn (wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z'))) (F σ) U := by
    intro w
    induction w with
    | nil =>
      refine ⟨_, ExpSum.term 0 b [] hb, fun σ _ z _ => ?_⟩
      simp [wirtWord_nil]
    | cons a w ih =>
      obtain ⟨F, hF, hEq⟩ := ih
      obtain ⟨F₁, hF₁, hd₁⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 1)
      obtain ⟨F₂, hF₂, hd₂⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 Complex.I)
      refine ⟨fun σ z => (1 / 2 : ℂ) * (F₁ σ z + (if a.2 then Complex.I else -Complex.I) * F₂ σ z),
        (ExpSum.add hF₁ (hF₂.const_mul _)).const_mul _, fun σ hσ z hz => ?_⟩
      have hev : wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) =ᶠ[nhds z] F σ :=
        Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => hEq σ hσ hy
      rw [wirtWord_cons]
      simp only [wirt]
      rw [hev.fderiv_eq, hd₁ σ hσ z hz, hd₂ σ hσ z hz]
      ring
  obtain ⟨F, hF, hEq⟩ := key w
  exact (hF.holo hmaps hGh hz).congr fun σ hσ => hEq σ hσ hz
end GlobalTheory.WirtChain
