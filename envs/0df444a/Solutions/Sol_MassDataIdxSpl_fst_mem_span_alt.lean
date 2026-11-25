-- Prove2me | solution 1 for MassDataIdxSpl.fst_mem_span_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:10.783311+00:00
-- url     : https://prove2.me/submissions/aa80cc62-b69f-4318-bd61-dbe8f24c7286

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
import Theorems.Thm_MassDataIdxSpl_fst_smul_alt

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
    pr1 θ v ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [fst_smul_alt]; exact Submodule.smul_mem _ _ hx
end MassDataIdxSpl
