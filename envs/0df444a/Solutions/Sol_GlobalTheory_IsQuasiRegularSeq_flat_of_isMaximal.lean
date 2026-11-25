-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.flat_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:44.146783+00:00
-- url     : https://prove2.me/submissions/fd152db7-33f7-43fb-8e01-95169319bf58

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_mem_pow_smul_of_map_mem
import Theorems.Thm_GlobalTheory_flat_of_basis_mod_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution [IsNoetherianRing A] (B : Type*) [CommRing B]
    [IsNoetherianRing B] [Algebra A B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {ι : Type*} [Finite ι] {f : ι → A} (h : IsQuasiRegularSeq M f)
    (hmax : (Ideal.span (Set.range f)).IsMaximal)
    (hI : (Ideal.span (Set.range f)).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson) :
    Module.Flat A M := by
  set I := Ideal.span (Set.range f) with hIdef
  letI := Ideal.Quotient.field I
  let b := Module.Free.chooseBasis (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))
  choose m hm using fun s => Submodule.Quotient.mk_surjective _ (b s)
  have hb : ∀ z, (Submodule.Quotient.mk (Finsupp.linearCombination A m z) :
      M ⧸ (I • ⊤ : Submodule A M)) =
      Finsupp.linearCombination (A ⧸ I) b (z.mapRange (Ideal.Quotient.mk I) (map_zero _)) := by
    intro z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, Submodule.Quotient.mk_add, hx, hy, Finsupp.mapRange_add (map_add _), map_add]
    | single s a => simp [hm, ← Ideal.Quotient.algebraMap_eq]
  refine flat_of_basis_mod_pow B hI m ?_ fun n z hz s => ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨z, hz⟩ := Finsupp.mapRange_surjective (Ideal.Quotient.mk I) (map_zero _)
      Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk y))
    have h1 := hb z
    rw [hz, b.linearCombination_repr, Submodule.Quotient.eq'] at h1
    have h2 : Finsupp.linearCombination A m z ∈ Submodule.span A (Set.range m) := by
      rw [← Finsupp.range_linearCombination]
      exact ⟨z, rfl⟩
    simpa using Submodule.add_mem_sup h2 h1
  · have h1 := h.mem_pow_smul_of_map_mem (Finsupp.linearCombination A m) (fun z hz => ?_) n z hz
    · have := Submodule.mem_map_of_mem (f := Finsupp.lapply (R := A) s) h1
      rw [Submodule.map_smul''] at this
      simpa using Submodule.smul_mono le_rfl le_top this
    · rw [← Submodule.Quotient.mk_eq_zero, hb] at hz
      have h2 := (linearIndependent_iff.mp b.linearIndependent) _ hz
      rw [← z.sum_single]
      refine Submodule.sum_mem _ fun s _ => ?_
      rw [← mul_one (z s), ← smul_eq_mul, ← Finsupp.smul_single]
      refine Submodule.smul_mem_smul (Ideal.Quotient.eq_zero_iff_mem.mp ?_) trivial
      simpa using DFunLike.congr_fun h2 s
end IsQuasiRegularSeq
end GlobalTheory
