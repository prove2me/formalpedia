-- Prove2me | solution 1 for GlobalTheory.SingleBlock.mul_left_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:35.777798+00:00
-- url     : https://prove2.me/submissions/598fdab7-ba36-4cb5-9eba-33e954ebc81a

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_mem
import Theorems.Thm_GlobalTheory_SingleBlock_II_add
import Theorems.Thm_GlobalTheory_SingleBlock_mul_II
import Theorems.Thm_GlobalTheory_SingleBlock_exists_of_congr
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_II_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F} (hh : ∀ i j, h i j ∈ O) (k : P)
    (hk : ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = h.toBlocks₁₁)
    (hc : h.toBlocks₂₁ ∈ IIset O ϖ)
    {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hx : x ∈ suppSet t O ϖ P) :
    h * x ∈ suppSet t O ϖ P ∧ phiU O ϖ P ρ (h * x) = ((ρ k : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by
  obtain ⟨⟨p, hp, ep⟩, h2⟩ := hx
  have e : h * x = fromRows (h.toBlocks₁₁ * toRows₁ x + h.toBlocks₁₂ * toRows₂ x)
      (h.toBlocks₂₁ * toRows₁ x + h.toBlocks₂₂ * toRows₂ x) := by
    rw [← fromBlocks_mul_fromRows, fromBlocks_toBlocks, fromRows_toRows]
  have h3 : toRows₂ (h * x) ∈ IIset O ϖ := by
    rw [e, toRows₂_fromRows]
    refine II_add (LemmaU.II_mul O ϖ _ hc _ ?_) (mul_II (fun i j => hh _ _) h2)
    rw [← ep]; exact (hP hp).1
  obtain ⟨k', ek', hk'⟩ := exists_of_congr hϖ hϖ0 hloc hKP hP ρ hρ (k * ⟨p, hp⟩)
    (m := toRows₁ (h * x)) (by
      rw [e, toRows₁_fromRows, ← hk, ← ep]
      have : (((k * ⟨p, hp⟩ : P) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (p : Matrix (Fin r) (Fin r) F) := rfl
      rw [this, add_sub_cancel_left]
      exact mul_II (fun i j => hh _ _) h2)
  refine ⟨⟨⟨_, k'.2, ek'⟩, h3⟩, ?_⟩
  rw [phiU_of_mem ρ _ ek' h3, phiU_of_mem ρ ⟨p, hp⟩ ep h2, hk', map_mul, Units.val_mul]
end GlobalTheory.SingleBlock
