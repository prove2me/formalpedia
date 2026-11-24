-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotLinear.exists_compact_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:04.274027+00:00
-- url     : https://prove2.me/submissions/f4c161a4-0885-4624-96c2-ed91ff2f1b72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
import Theorems.Thm_GlobalTheory_RootEx_QuotLinear_isClosed_N
import Theorems.Thm_GlobalTheory_RootEx_QuotLinear_continuous_embX
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotLinear
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.QuotLinear
theorem _root_.solution {K : Set (GL (n ⊕ Fin c) k)} (hK : IsCompact K) :
    ∃ (A : Set (GL n k)) (B : Set (N k n c p)), IsCompact A ∧ IsCompact B ∧
      ∀ (x : GL n k) (u : N k n c p), embX c x * (u : GL (n ⊕ Fin c) k) ∈ K → x ∈ A ∧ u ∈ B := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
    fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
  have hb : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem _ _
  have hφ : Continuous φ :=
    (hb.comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp (hb.comp Units.continuous_coe_inv))
  have hA := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hK.image hφ)
  have hB := (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hA.image (continuous_embX (c := c))).inv.mul hK)
  refine ⟨_, _, hA, hB, fun x u h => ?_⟩
  have hx : x ∈ (Units.embedProduct (Matrix n n k)) ⁻¹' (φ '' K) := by
    refine ⟨_, h, ?_⟩
    have e : (embX c x * (u : GL (n ⊕ Fin c) k))⁻¹ =
        embX c x⁻¹ * (embX c x * (u : GL (n ⊕ Fin c) k)⁻¹ * (embX c x)⁻¹) := by
      rw [map_inv]; group
    simp only [φ]
    rw [e, Radical.toBlocks₁₁_embX_mul x u.2,
      Radical.toBlocks₁₁_embX_mul x⁻¹ (Radical.conj_mem x (inv_mem u.2))]
    rfl
  refine ⟨hx, ?_⟩
  refine ⟨(embX c x)⁻¹, ?_, _, h, by simp⟩
  rw [Set.mem_inv, inv_inv]
  exact ⟨x, hx, rfl⟩
end GlobalTheory.RootEx.QuotLinear
