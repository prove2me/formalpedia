-- Prove2me | solution 1 for MatchingLogic.localize_not_redundant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:39.164995+00:00
-- url     : https://prove2.me/submissions/26fa1fec-7eb9-4b53-a0ce-f3f477bcad77

module
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Independence
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_box
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution :
    ¬ (∀ (S : Signature) (Var : Type) (_ : DecidableEq Var)
         (Γ : Set (Pattern S Var)) (φ : Pattern S Var),
         (∀ γ ∈ Γ, Closed γ) → Closed φ →
         (GlobalCons Γ φ ↔ LocalCons Γ φ)) := by
  intro hall
  let S₁ : Signature := ⟨Bool, fun _ => 1⟩
  let γ : Pattern S₁ Bool := .ex false (.app false (fun _ => .var false))
  let e : Coord S₁ := ⟨true, 0⟩
  let φ : Pattern S₁ Bool := box e γ
  let Γ : Set (Pattern S₁ Bool) := {γ}
  have hγ : Closed γ := by
    simp [γ, Closed]
  have hΓ : ∀ δ ∈ Γ, Closed δ := by
    intro δ hδ
    have : δ = γ := by simpa [Γ] using hδ
    simpa [this] using hγ
  have hφ : Closed φ := by
    unfold Closed at hγ ⊢
    simpa [φ] using hγ
  have hglobal : GlobalCons Γ φ := by
    intro M hM ρ
    have hγtotal := hM γ (by simp [Γ]) ρ
    unfold Model.Total
    change M.denote ρ (box e γ) = Set.univ
    rw [denote_box]
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro v _
    rw [hγtotal]
    exact Set.mem_univ v
  have hsatisfiable : ∃ M : Model S₁, M.SatSet Γ := by
    let T : Model S₁ :=
      { carrier := Bool
        nonempty := ⟨false⟩
        interp := fun _ _ => Set.univ }
    refine ⟨T, ?_⟩
    intro δ hδ ρ
    have hδ' : δ = γ := by simpa [Γ] using hδ
    subst δ
    unfold Model.Total
    apply Set.eq_univ_iff_forall.mpr
    intro u
    rw [show γ = .ex false (.app false (fun _ => .var false)) by rfl,
      denote_ex]
    apply Set.mem_iUnion.mpr
    refine ⟨u, ?_⟩
    rw [denote_app]
    refine ⟨fun _ => u, ?_, ?_⟩
    · intro i
      simp
    · exact Set.mem_univ u
  have hglobal_nonvacuous : GlobalCons Γ φ ∧ ∃ M : Model S₁, M.SatSet Γ :=
    ⟨hglobal, hsatisfiable⟩
  have hnotlocal : ¬LocalCons Γ φ := by
    intro hlocal
    let M₁ : Model S₁ :=
      { carrier := Bool
        nonempty := ⟨false⟩
        interp := fun σ a => match σ with
          | false => {false}
          | true => if a 0 = true then {false} else ∅ }
    let ρ₁ : Bool → Bool := fun _ => false
    have hwΓ : false ∈ M₁.denoteSet ρ₁ Γ := by
      simp only [Model.denoteSet, Set.mem_iInter]
      intro δ hδ
      have hδ' : δ = γ := by simpa [Γ] using hδ
      subst δ
      rw [show γ = .ex false (.app false (fun _ => .var false)) by rfl,
        denote_ex]
      apply Set.mem_iUnion.mpr
      refine ⟨false, ?_⟩
      rw [denote_app]
      refine ⟨fun _ => false, ?_, ?_⟩
      · intro i
        simp
      · rfl
    have hwφ := hlocal M₁ ρ₁ hwΓ
    change false ∈ M₁.denote ρ₁ (box e γ) at hwφ
    rw [denote_box] at hwφ
    have hstep : M₁.stepAt e false true := by
      refine ⟨fun _ => true, ?_, rfl⟩
      rfl
    have hvγ := hwφ true hstep
    rw [show γ = .ex false (.app false (fun _ => .var false)) by rfl,
      denote_ex] at hvγ
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hvγ
    rw [denote_app] at ha
    obtain ⟨A, _, hout⟩ := ha
    exact Bool.noConfusion hout
  exact hnotlocal ((hall S₁ Bool inferInstance Γ φ hΓ hφ).mp hglobal_nonvacuous.1)
end MatchingLogic
