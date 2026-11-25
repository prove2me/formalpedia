-- Prove2me | solution 1 for MassDataIdxSpl.snd_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:11.548077+00:00
-- url     : https://prove2.me/submissions/de0c2277-9f95-45d8-9872-8b972f8fc238

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
import Theorems.Thm_MassDataIdxSpl_snd_smul_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxSpl
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
variable {ι : Type} (Y : ι → n → T) (s : Set ι)
namespace MassDataIdxSpl
theorem _root_.solution {v : n → T} (hv : v ∈ Submodule.span T (Y '' s)) :
    pr2 θ v ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [snd_smul_alt]; exact Submodule.smul_mem _ _ hx
end MassDataIdxSpl
