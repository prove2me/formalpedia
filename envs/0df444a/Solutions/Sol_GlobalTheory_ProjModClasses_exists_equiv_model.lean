-- Prove2me | solution 1 for GlobalTheory.ProjModClasses.exists_equiv_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:11.299945+00:00
-- url     : https://prove2.me/submissions/86fe3932-ed04-4ee0-ba83-0ca43d1c0f21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField
import Theorems.Thm_GlobalTheory_ProjModClasses_mk0_rep
import Theorems.Thm_GlobalTheory_ProjModClasses_nonempty_equiv_of_mk0_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.ProjModClasses
variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModClasses
theorem _root_.solution : ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.Projective R X], Module.finrank R X = r →
    ∃ c : Fin r → ClassGroup R, Nonempty (X ≃ₗ[R] Model c)
  | 0, X, _, _, _, _, h => by
    have : Subsingleton X := by
      by_contra hX
      rw [not_subsingleton_iff_nontrivial] at hX
      have := (Module.finrank_pos_iff (R := R) (M := X)).2 hX
      omega
    exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | r + 1, X, _, _, _, _, h => by
    have hX : Nontrivial X := (Module.finrank_pos_iff (R := R) (M := X)).1 (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hx
    set I : Ideal R := LinearMap.range f with hIdef
    have hI : I ≠ ⊥ := fun h0 => hf (by
      have : f x ∈ I := LinearMap.mem_range_self f x
      rw [h0] at this
      simpa using this)
    let g : X →ₗ[R] I := f.rangeRestrict
    have hg : Function.Surjective g := LinearMap.surjective_rangeRestrict f
    obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
    let K := LinearMap.ker g
    have hex : Function.Exact K.subtype g := LinearMap.exact_subtype_ker_map g
    let e := ((hex.splitSurjectiveEquiv Subtype.val_injective) ⟨s, hs⟩).1
    have he := ((hex.splitSurjectiveEquiv Subtype.val_injective) ⟨s, hs⟩).2
    haveI : Module.Projective R K := by
      refine Module.Projective.of_split K.subtype (LinearMap.fst R K I ∘ₗ e.toLinearMap) ?_
      ext y
      have h1 : (K.subtype y) = e.symm (y, 0) := by
        rw [he.1]; rfl
      show ((e (K.subtype y)).1 : X) = (y : X)
      rw [h1]
      simp

    have hrk := LinearMap.rank_range_add_rank_ker g
    rw [LinearMap.range_eq_top.2 hg, rank_top] at hrk
    have hIne : Nontrivial I := Submodule.nontrivial_iff_ne_bot.2 hI
    have hI1 : Module.finrank R I = 1 := by
      have a := (Module.finrank_pos_iff (R := R) (M := I)).2 hIne
      have b : Module.finrank R I ≤ 1 := (Submodule.finrank_le I).trans (by simp)
      omega
    have hK : Module.finrank R K = r := by
      have := congrArg Cardinal.toNat hrk
      rw [Cardinal.toNat_add (Module.rank_lt_aleph0 R I) (Module.rank_lt_aleph0 R K)] at this
      change Module.finrank R I + Module.finrank R K = Module.finrank R X at this
      omega
    obtain ⟨c, ⟨eK⟩⟩ := solution r K hK
    have hmem : I ∈ nonZeroDivisors (Ideal R) := mem_nonZeroDivisors_of_ne_zero hI
    obtain ⟨eI⟩ := nonempty_equiv_of_mk0_eq (I := ⟨I, hmem⟩)
      (J := ⟨rep (ClassGroup.mk0 ⟨I, hmem⟩), rep_mem _⟩) (mk0_rep _).symm
    exact ⟨Fin.cons (ClassGroup.mk0 ⟨I, hmem⟩) c,
      ⟨e.trans ((LinearEquiv.prodComm R K I).trans ((eI.prodCongr eK).trans (consLin _ c)))⟩⟩
end GlobalTheory.ProjModClasses
