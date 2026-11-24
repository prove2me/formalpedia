-- Prove2me | solution 1 for GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:13:14.268041+00:00
-- url     : https://prove2.me/submissions/87c61bf2-82fb-4c43-b40b-2546a73df5e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ v, a v ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h v
    have hv := h v
    unfold GlobalTheory.Idele.localIdeal at hv
    revert hv
    generalize a v = y
    intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hk
      exact HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) r
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [show c • x = (c : v.adicCompletion F) * x from rfl]
      exact mul_mem c.2 hx
  · intro h v
    unfold GlobalTheory.Idele.localIdeal
    rw [← mul_one (a v), show a v * 1 = (⟨a v, h v⟩ : v.adicCompletionIntegers F) •
      (1 : v.adicCompletion F) from rfl]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one _⟩)
end GlobalTheory.AdLat
