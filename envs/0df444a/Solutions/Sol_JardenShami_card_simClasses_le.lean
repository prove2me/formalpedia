-- Prove2me | solution 1 for JardenShami.card_simClasses_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:27.495952+00:00
-- url     : https://prove2.me/submissions/ed61bf57-a127-4a9a-bf03-529f718d6f12

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_sim_witness_mono_and_equivalence
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_lt
import Theorems.Thm_JardenShami_Kappa_mk_eq


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C)
    (h : Order.succ μ < κ) :
    #(Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}) ≤ μ := by
  classical
  obtain ⟨-, heqv⟩ := sim_witness_mono_and_equivalence κ μ hκ C hC
  set R := Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ} with hR
  by_contra hc
  obtain ⟨P, hPR, hPc⟩ := Cardinal.le_mk_iff_exists_subset.1 (Order.succ_le_of_lt (lt_of_not_ge hc))
  -- representatives
  have hrep : ∀ p : P, ∃ β : Kappa κ, {γ : Kappa κ | Sim C β γ} = p := fun p => hPR p.2
  choose r hr using hrep
  have hrinj : Function.Injective r := fun p p' h => Subtype.ext ((hr p).symm.trans (h ▸ hr p'))
  have hrc : #(Set.range r) < κ := by
    rw [Cardinal.mk_range_eq _ hrinj, hPc]
    exact h
  obtain ⟨αs, hαs⟩ := Kappa.exists_gt_of_card_lt hκ hrc
  -- the colors `C(r p, α*)` are pairwise distinct
  let φ : P → Kappa μ := fun p => C.color (r p) αs (hαs _ ⟨p, rfl⟩)
  have hφ : Function.Injective φ := by
    intro p p' e
    have hsim : Sim C (r p) (r p') := ⟨αs, _, _, e⟩
    refine Subtype.ext ?_
    rw [← hr p, ← hr p']
    ext γ
    exact ⟨fun h => heqv.trans (heqv.symm hsim) h, fun h => heqv.trans hsim h⟩
  have := Cardinal.mk_le_of_injective hφ
  rw [hPc, Kappa.mk_eq] at this
  exact (Order.lt_succ_of_not_isMax (not_isMax μ)).not_ge this
end JardenShami
