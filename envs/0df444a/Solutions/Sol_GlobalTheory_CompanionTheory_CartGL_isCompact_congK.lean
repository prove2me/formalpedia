-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.isCompact_congK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:37:06.781804+00:00
-- url     : https://prove2.me/submissions/6ceb80c7-6239-4517-b2a1-e4c70e7674e0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_isCompact_entryBall
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_mem_congK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsCompact (congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  have hS := isCompact_entryBall L n r
  have hS' := hS.image MulOpposite.continuous_op
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  have e : (congK L n r h0 h1 : Set (GL (Fin n) L)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) L) ⁻¹'
        ({M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} ×ˢ
          (MulOpposite.op '' {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r})) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      Set.mem_image, Set.mem_setOf_eq, MulOpposite.op_inj, exists_eq_right]
    exact ⟨fun hk => ⟨fun i j => (hk i j).1, fun i j => (hk i j).2⟩,
      fun hk i j => ⟨hk.1 i j, hk.2 i j⟩⟩
  rw [e]
  exact h
end GlobalTheory.CompanionTheory.CartGL
