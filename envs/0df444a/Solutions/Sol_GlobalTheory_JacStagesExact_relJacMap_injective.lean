-- Prove2me | solution 1 for GlobalTheory.JacStagesExact.relJacMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:33:57.500889+00:00
-- url     : https://prove2.me/submissions/1977bb7e-f513-49d8-9c95-e016685b56d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientRelativeJacquetBlockLevi
import Theorems.Thm_GlobalTheory_InertSupp_unipRad_eq_unipOf
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_IwahoriInj_twKer_mono
import Theorems.Thm_GlobalTheory_JacquetExact_exists_finset_of_mem_twKer
import Theorems.Thm_GlobalTheory_JacquetExact_mem_twKer_of_compact
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_UnipCompact_exists_compact_subgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages GlobalTheory.InertSupp
open GlobalTheory GlobalTheory.JacStagesExact
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.JacStagesExact
theorem _root_.solution (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (relJacMap e' f) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨S, hS, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
  have hH : ∀ a, ∃ H : Subgroup (GL (Fin (d a)) k), H ≤ unipRad k (e' a) ∧
      IsCompact (H : Set (GL (Fin (d a)) k)) ∧ ∀ u ∈ S, u a ∈ H := by
    intro a
    have hN : unipRad k (e' a) = unipOf k fun i => ((blk (e' a) i).val : ℤ) :=
      unipRad_eq_unipOf k fun i j => by simp
    obtain ⟨H, hle, hc, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup k (Fin (d a)) _
      (S.image fun u => u a) (by
        intro u hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
        have hm : u' a ∈ unipRad k (e' a) := hS u' hu' a (Set.mem_univ a)
        exact hN ▸ hm)
    exact ⟨H, hle.trans hN.ge, hc, fun u hu => hSH _ (Finset.mem_image_of_mem _ hu)⟩
  choose H hle hc hSH using hH
  let H' : Subgroup (Levi k fun a => Fin (d a)) := Subgroup.pi Set.univ H
  have hc' : IsCompact (H' : Set (Levi k fun a => Fin (d a))) := by
    have : (H' : Set (Levi k fun a => Fin (d a))) = Set.pi Set.univ fun a => (H a : Set _) := rfl
    rw [this]
    exact isCompact_univ_pi hc
  have hle' : H' ≤ relUnipD k e' := fun u hu a _ => hle a (hu a (Set.mem_univ a))
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono hle'
    (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ f hf hc' (h2 H' fun u hu a _ => hSH a u hu))
end GlobalTheory.JacStagesExact
