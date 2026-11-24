-- Prove2me | solution 1 for GlobalTheory.BorelCoh.exists_equivariant_proj_of_le_sum_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:36.546327+00:00
-- url     : https://prove2.me/submissions/948be301-2f4f-414e-84aa-d59563b038d3

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_BasicForm
import Definitions.Def_PositivityTheory_AutomorphicForms_PublishedInputs_BorelInjectivity_EquivariantProjections_ExistsEquivariantProjOfLeSumIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BorelCoh CategoryTheory
open scoped ContDiff Matrix
open GlobalTheory GlobalTheory.BorelCoh
namespace GlobalTheory.BorelCoh
theorem _root_.solution {M O : Type} [AddCommGroup M] [Module ℂ M]
    (act : O → Module.End ℂ M) (V : Submodule ℂ M) (hVst : ∀ o, ∀ x ∈ V, act o x ∈ V)
    (hV : V ≤ ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) :
    ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧
      (∀ x, p x ∈ V) ∧ (∀ x ∈ V, p x = x) := by
  set Wt := ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W with hWt
  have hst_sup : ∀ A B : Submodule ℂ M, (∀ o, ∀ x ∈ A, act o x ∈ A) → (∀ o, ∀ x ∈ B, act o x ∈ B) →
      ∀ o, ∀ x ∈ A ⊔ B, act o x ∈ A ⊔ B := by
    intro A B hA hB o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hA o y hy) (hB o z hz)

  let s : Set (Submodule ℂ M) := {C | (∀ o, ∀ x ∈ C, act o x ∈ C) ∧ C ≤ Wt ∧ Disjoint V C}
  obtain ⟨C, -, ⟨hCst, hCW, hCd⟩, hCmax⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, sSup_le fun z hz => (hcs hz).2.1, ?_⟩, fun z hz => le_sSup hz⟩
    · intro o x hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcs hz).1 o x hxz⟩
    · rw [Submodule.disjoint_def]
      intro x hxV hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.disjoint_def.1 (hcs hz).2.2) x hxV hxz) ⊥
    ⟨fun o x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero], bot_le, disjoint_bot_right⟩

  have hWle : Wt ≤ V ⊔ C := by
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSst, hSne, hSmin⟩ := hS
    have hinst : ∀ o, ∀ x ∈ S ⊓ (V ⊔ C), act o x ∈ S ⊓ (V ⊔ C) := fun o x hx =>
      ⟨hSst o x hx.1, hst_sup V C hVst hCst o x hx.2⟩
    rcases hSmin _ inf_le_left hinst with h | h
    · have hSW : S ≤ Wt := le_iSup₂_of_le S ⟨hSst, hSne, hSmin⟩ le_rfl
      have hmem : C ⊔ S ∈ s := ⟨hst_sup C S hCst hSst, sup_le hCW hSW,
        Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (by rw [disjoint_comm, disjoint_iff]; exact h)⟩
      exact (le_sup_right.trans (hCmax hmem le_sup_left)).trans le_sup_right
    · exact h ▸ inf_le_right
  have hW : Wt = V ⊔ C := le_antisymm hWle (sup_le hV hCW)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl Wt
  have hc : IsCompl V (C ⊔ D) := by
    constructor
    · exact Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (hW ▸ hD.disjoint)
    · rw [codisjoint_iff, ← sup_assoc, ← hW, hD.sup_eq_top]
  have hl : ∀ v ∈ V, (V.linearProjOfIsCompl (C ⊔ D) hc v : M) = v := fun v hv =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩)
  have hr : ∀ w ∈ C ⊔ D, V.linearProjOfIsCompl (C ⊔ D) hc w = 0 := fun w hw =>
    Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
  refine ⟨V.subtype ∘ₗ V.linearProjOfIsCompl (C ⊔ D) hc, ?_, fun x => (V.linearProjOfIsCompl _ hc x).2, hl⟩
  intro o x hx
  rw [hW] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have hz' : z ∈ C ⊔ D := Submodule.mem_sup_left hz
  have hz'' : act o z ∈ C ⊔ D := Submodule.mem_sup_left (hCst o z hz)
  show (V.linearProjOfIsCompl _ hc (act o (y + z)) : M) = act o (V.linearProjOfIsCompl _ hc (y + z))
  rw [map_add, map_add, map_add, hr _ hz'', hr _ hz', add_zero, add_zero, hl _ (hVst o y hy), hl _ hy]
end GlobalTheory.BorelCoh
