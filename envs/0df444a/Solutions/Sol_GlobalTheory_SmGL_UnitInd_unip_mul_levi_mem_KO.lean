-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.unip_mul_levi_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:37.54926+00:00
-- url     : https://prove2.me/submissions/b2c4cf7e-547d-4454-8e98-339e9f0ecef3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_coe_mem_unipRad
import Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (u : unipRad k e) (g : Levi k m) :
    (u : GL n k) * leviEmb k e g ∈ KO k n ↔ (u : GL n k) ∈ KO k n ∧ ∀ a, g a ∈ KO k (m a) := by
  have key : (∀ a, g a ∈ KO k (m a)) → leviEmb k e g ∈ KO k n := fun h => by
    have aux : ∀ t : Levi k m, (∀ a i j, (t a).val i j ∈ 𝒪[k]) → ∀ i j, (leviEmb k e t).val i j ∈ 𝒪[k] := by
      intro t ht i j
      obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same]; exact ht a i j
      · rw [leviEmb_apply_ne k e t hab]; exact zero_mem _
    refine (mem_KO_iff _).2 ⟨aux g fun a => ((mem_KO_iff _).1 (h a)).1, ?_⟩
    rw [← map_inv]
    exact aux g⁻¹ fun a => ((mem_KO_iff _).1 (h a)).2
  refine ⟨fun h => ?_, fun h => mul_mem h.1 (key h.2)⟩
  let p : parab k e := ⟨u, unipRad_le_parab k e u.2⟩ * ⟨_, leviEmb_mem_parab k e g⟩
  have hp : leviProj k e p = g := by
    rw [map_mul, (coe_mem_unipRad k _).1 u.2, leviProj_leviEmb, one_mul]
  have hg : ∀ a, g a ∈ KO k (m a) := fun a => by
    obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 h
    refine (mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [← hp]; exact h1 _ _
    · rw [← hp, ← Pi.inv_apply, ← map_inv]; exact h2 _ _
  exact ⟨(mul_mem_cancel_right (key hg)).1 h, hg⟩
end GlobalTheory.SmGL.UnitInd
