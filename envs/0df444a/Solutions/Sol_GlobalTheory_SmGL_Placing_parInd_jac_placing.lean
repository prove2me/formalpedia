-- Prove2me | solution 1 for GlobalTheory.SmGL.Placing.parInd_jac_placing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:17:03.723625+00:00
-- url     : https://prove2.me/submissions/c097f201-1b56-49b3-991f-62ba9f89fa10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
import Theorems.Thm_GlobalTheory_SmGL_Placing_smInd_equiv
import Theorems.Thm_GlobalTheory_SmGL_Placing_jacquet_equiv
import Theorems.Thm_GlobalTheory_SmGL_Placing_exists_moves
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_coe_mem_unipRad
import Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
namespace GlobalTheory.SmGL.Placing
section General
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
end General
section Blocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R}
end Blocks
open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
private theorem moves_inv_of_moves {ι : Type} {e e' : ι ≃ n} {w : GL n R}
    (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w) : _root_.GlobalTheory.SmGL.Placing.Moves e' e w⁻¹ := by
  intro g x y
  have := hw (w⁻¹ * g * w⁻¹⁻¹) x y
  rw [← this]
  congr 2
  group
open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviProj_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    _root_.GlobalTheory.SmGL.leviProj R e' ⟨w * p * w⁻¹, conj_mem_parab_of_moves hw p.2⟩ =
      _root_.GlobalTheory.SmGL.leviProj R e p := by
  refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
  simpa [_root_.GlobalTheory.SmGL.leviProj, _root_.GlobalTheory.SmGL.diagBlock] using hw (p : GL n R) ⟨a, i⟩ ⟨a, j⟩
open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem conj_mem_unipRad_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {u : GL n R} (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) :
    w * u * w⁻¹ ∈ _root_.GlobalTheory.SmGL.unipRad R e' := by
  have hP := _root_.GlobalTheory.SmGL.unipRad_le_parab R e hu
  have h1 := (_root_.GlobalTheory.SmGL.coe_mem_unipRad R (p := ⟨u, hP⟩)).1 hu
  exact (_root_.GlobalTheory.SmGL.coe_mem_unipRad R
    (p := ⟨w * u * w⁻¹, conj_mem_parab_of_moves hw hP⟩)).2
    ((leviProj_conj_of_moves hw ⟨u, hP⟩).trans h1)
open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviEmb_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (x : _root_.GlobalTheory.SmGL.Levi R m) :
    w * _root_.GlobalTheory.SmGL.leviEmb R e x * w⁻¹ = _root_.GlobalTheory.SmGL.leviEmb R e' x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨p, rfl⟩ := e'.surjective i
  obtain ⟨q, rfl⟩ := e'.surjective j
  rw [hw]
  simp [_root_.GlobalTheory.SmGL.leviEmb, Matrix.reindex_apply]
end GlobalTheory.SmGL.Placing
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
open ValuativeRel MeasureTheory
namespace GlobalTheory.SmGL.Placing
namespace _root_.GlobalTheory.SmGL.Placing
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α]
    [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e e' : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V],
    (∀ ρ : Representation ℂ (_root_.GlobalTheory.SmGL.Levi k m) V,
      Nonempty ((_root_.GlobalTheory.SmGL.parInd e ρ).Equiv (_root_.GlobalTheory.SmGL.parInd e' ρ))) ∧
    ∀ π : Representation ℂ (GL n k) V,
      Nonempty ((_root_.GlobalTheory.SmGL.jac e π).Equiv (_root_.GlobalTheory.SmGL.jac e' π)) := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e e' V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e' e
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.smInd_equiv w
      (fun q => ⟨⟨_, conj_mem_parab_of_moves hw q.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw q]⟩)
      (fun p => ⟨⟨_, conj_mem_parab_of_moves hw' p.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw' p]⟩)
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e e'
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.jacquet_equiv π _ _ _ w
      (fun u hu => conj_mem_unipRad_of_moves hw hu)
      (fun u hu => conj_mem_unipRad_of_moves hw' hu)
      (leviEmb_conj_of_moves hw)
end _root_.GlobalTheory.SmGL.Placing
end GlobalTheory.SmGL.Placing
