-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanMove.isCartan_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:25.592799+00:00
-- url     : https://prove2.me/submissions/85229443-4cfa-4f26-b0db-e310231997c4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MovingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_apply_mem_closure
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_symm_mem_closure
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
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
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanMove
variable {G G' : Type} [Group G] [Group G']
namespace GlobalTheory.CompanionTheory.CartanMove
theorem _root_.solution (e : G ≃* G') {K' : Subgroup G'} {d l : ℕ} (h : IsCartan K' d l) :
    IsCartan (K'.comap e.toMonoidHom) d l := by
  obtain ⟨c', t', h1, h2, h3, h4⟩ := h
  have hmem : ∀ {x : G'}, x ∈ K' → e.symm x ∈ K'.comap e.toMonoidHom := fun {x} hx => by
    simpa [Subgroup.mem_comap] using hx
  refine ⟨fun i => e.symm (c' i), fun j => e.symm (t' j), ?_, ?_, ?_, ?_⟩
  · intro i k
    simpa [Subgroup.mem_comap] using h1 i (e k)
  · intro i j
    exact (h2 i j).map e.symm
  · intro g
    obtain ⟨i, j, s, hs, k, hk, k', hk', hg⟩ := h3 (e g)
    refine ⟨i, j, e.symm s, symm_mem_closure e t' hs, e.symm k, hmem hk, e.symm k', hmem hk', ?_⟩
    apply e.injective
    simpa [map_mul] using hg
  · intro s hs s' hs' k hk
    obtain ⟨a, ha, b, hb, hab⟩ := h4 (e s) (apply_mem_closure e t' hs) (e s')
      (apply_mem_closure e t' hs') (e k) hk
    refine ⟨e.symm a, hmem ha, e.symm b, hmem hb, ?_⟩
    apply e.injective
    simpa [map_mul] using hab
end GlobalTheory.CompanionTheory.CartanMove
