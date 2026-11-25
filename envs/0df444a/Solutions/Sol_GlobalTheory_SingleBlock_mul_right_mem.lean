-- Prove2me | solution 1 for GlobalTheory.SingleBlock.mul_right_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:36.501686+00:00
-- url     : https://prove2.me/submissions/59ef9efb-e7ff-401d-8719-d219aeee79ec

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_II_mul
import Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d
import Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_a68189d70cdc


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
theorem _root_.solution (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) (g : P)
    {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hx : x ∈ suppSet t O ϖ P) :
    x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ suppSet t O ϖ P ∧
      phiU O ϖ P ρ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) =
        ((ρ g : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by
  obtain ⟨⟨k, hk, ek⟩, h2⟩ := hx
  have e : (((⟨k, hk⟩ * g : P) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      toRows₁ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) := by
    rw [LemmaU.toRows₁_mul, ← ek]; rfl
  have h3 : toRows₂ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) ∈ IIset O ϖ := by
    rw [LemmaU.toRows₂_mul]; exact LemmaU.II_mul O ϖ _ h2 _ (hP g.2).1
  refine ⟨⟨⟨_, (⟨k, hk⟩ * g : P).2, e⟩, h3⟩, ?_⟩
  rw [phiU_of_mem ρ _ e h3, phiU_of_mem ρ ⟨k, hk⟩ ek h2, map_mul, Units.val_mul, mul_comm]
end GlobalTheory.SingleBlock
