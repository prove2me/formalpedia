-- Prove2me | solution 1 for MassDataIdxSpl.mem_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:54.717936+00:00
-- url     : https://prove2.me/submissions/3653d5e7-6eea-4f41-bc46-8815538d01aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
import Theorems.Thm_MassDataIdxSpl_inj_add
import Theorems.Thm_MassDataIdxSpl_inl_fst_alt
import Theorems.Thm_MassDataIdxSpl_inr_snd_alt
import Theorems.Thm_MassDataIdxSpl_fst_mem_span_alt
import Theorems.Thm_MassDataIdxSpl_snd_mem_span
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace MassDataIdxSpl
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
variable {ι : Type} (Y : ι → n → T) (s : Set ι)
private theorem inl_mem_span_lemma {w : n → K} (hw : w ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s)) :
    inj1 θ w ∈ Submodule.span T (Y '' s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [inl_fst_alt]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem _ c hx
private theorem inr_mem_span_lemma_2 {w : n → K} (hw : w ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s)) :
    inj2 θ w ∈ Submodule.span T (Y '' s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [inr_snd_alt]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem _ c hx
end MassDataIdxSpl
end
end

set_option autoImplicit false
noncomputable section
open MassDataIdxSpl
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
variable {ι : Type} (Y : ι → n → T) (s : Set ι)
namespace MassDataIdxSpl
theorem _root_.solution (v : n → T) :
    v ∈ Submodule.span T (Y '' s) ↔ pr1 θ v ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s) ∧
      pr2 θ v ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s) := by
  refine ⟨fun hv => ⟨fst_mem_span_alt θ Y s hv, snd_mem_span θ Y s hv⟩, fun ⟨h1, h2⟩ => ?_⟩
  rw [← inj_add θ v]
  exact Submodule.add_mem _ (inl_mem_span_lemma θ Y s h1) (inr_mem_span_lemma_2 θ Y s h2)
end MassDataIdxSpl
