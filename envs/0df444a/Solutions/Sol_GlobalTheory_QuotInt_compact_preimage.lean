-- Prove2me | solution 1 for GlobalTheory.QuotInt.compact_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:59.827541+00:00
-- url     : https://prove2.me/submissions/296f487f-bf85-4dc8-b5b4-0e9976fc55de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Theorems.Thm_GlobalTheory_QuotInt_continuous_embX
import Theorems.Thm_GlobalTheory_QuotInt_block_left
import Theorems.Thm_GlobalTheory_QuotInt_block_right
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.QuotInt
theorem _root_.solution (hN : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k))) {C : Set (GL (n ⊕ Fin c) k)}
    (hC : IsCompact C) : ∃ D : Set (GL n k × N k n c p), IsCompact D ∧
      ∀ z : GL n k × N k n c p, embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) ∈ C → z ∈ D := by
  have hb : Continuous (fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) := by
    refine continuous_matrix fun i j => ?_
    exact (Units.continuous_val.matrix_elem (Sum.inl i) (Sum.inl j))
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have h1 := hC.image hb
  have h2 := hC.image (MulOpposite.continuous_op.comp (hb.comp continuous_inv))
  have h3 := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (h1.prod h2)
  have h4 := (h3.prod hC).image (f := fun z => (embX c z.1)⁻¹ * z.2)
    ((continuous_embX.comp continuous_fst).inv.mul continuous_snd)
  have h5 := hN.isClosedEmbedding_subtypeVal.isCompact_preimage h4
  refine ⟨_, h3.prod h5, fun z hz => ?_⟩
  have hz1 : z.1 ∈ Units.embedProduct (Matrix n n k) ⁻¹'
      (((fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) '' C) ×ˢ
        ((MulOpposite.op ∘ (fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) ∘ fun a => a⁻¹) '' C)) :=
    ⟨⟨_, hz, block_left z.1 z.2.2⟩, ⟨_, hz, by
      simp only [Function.comp, _root_.mul_inv_rev, ← map_inv]
      rw [block_right _ ((N k n c p).inv_mem z.2.2)]
      rfl⟩⟩
  exact ⟨hz1, ⟨(z.1, _), ⟨hz1, hz⟩, by simp⟩⟩
end GlobalTheory.QuotInt
