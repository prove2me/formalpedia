-- Prove2me | solution 1 for GlobalTheory.SingleBlock.add_mem_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:31.906317+00:00
-- url     : https://prove2.me/submissions/fe803ffe-ecd5-4c38-bbc4-12b913313045

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_mem
import Theorems.Thm_GlobalTheory_SingleBlock_II_add
import Theorems.Thm_GlobalTheory_SingleBlock_exists_of_congr
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_iiset_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {x y : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hy : ∀ i j, ϖ⁻¹ * (y i j - x i j) ∈ O)
    (hx : x ∈ suppSet t O ϖ P) :
    y ∈ suppSet t O ϖ P ∧ phiU O ϖ P ρ y = phiU O ϖ P ρ x := by
  obtain ⟨⟨p, hp, ep⟩, h2⟩ := hx
  have h3 : toRows₂ y ∈ IIset O ϖ := by
    have : toRows₂ y = toRows₂ x + (toRows₂ y - toRows₂ x) := by abel
    rw [this]
    refine II_add h2 ?_
    rw [Vol.iiset_eq O ϖ hϖ0]
    exact fun i j => hy _ _
  obtain ⟨k', ek', hk'⟩ := exists_of_congr hϖ hϖ0 hloc hKP hP ρ hρ ⟨p, hp⟩
    (m := toRows₁ y) (by
      rw [Vol.iiset_eq O ϖ hϖ0]
      intro i j
      have := hy (Sum.inl i) j
      have e2 : (p : Matrix (Fin r) (Fin r) F) i j = x (Sum.inl i) j := congrFun (congrFun ep i) j
      simpa [← e2] using this)
  refine ⟨⟨⟨_, k'.2, ek'⟩, h3⟩, ?_⟩
  rw [phiU_of_mem ρ _ ek' h3, phiU_of_mem ρ ⟨p, hp⟩ ep h2, hk']
end GlobalTheory.SingleBlock
