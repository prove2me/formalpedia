-- Prove2me | solution 1 for MatchingLogic.soundness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:38.327249+00:00
-- url     : https://prove2.me/submissions/7c2b1402-0477-4abf-861f-3666c9ed26ac

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Theorems.Thm_MatchingLogic_Model_denote_substVar_of_captureFree
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_app_eq_empty
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_congr
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_nt
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
attribute [local instance] Classical.propDecidable
private theorem pform_mem_denote_iff (M : Model S) (ρ : Var → M.carrier)
    (θ : Nat → Pattern S Var) (u : M.carrier) (p : PForm) :
    u ∈ M.denote ρ (p.subst θ) ↔
      p.eval (fun n => decide (u ∈ M.denote ρ (θ n))) = true := by
  induction p with
  | atom n => simp [PForm.subst, PForm.eval]
  | bot => simp [PForm.subst, PForm.eval]
  | imp p q ihp ihq =>
      simp [PForm.subst, PForm.eval, ihp, ihq]
private theorem pform_taut_total (M : Model S) (ρ : Var → M.carrier)
    (θ : Nat → Pattern S Var) {p : PForm} (hp : p.Taut) :
    M.denote ρ (p.subst θ) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro u
  apply (pform_mem_denote_iff M ρ θ u p).mpr
  exact hp (fun n => decide (u ∈ M.denote ρ (θ n)))
private theorem Model.app_update_union (M : Model S) (σ : S.Sym)
    (A : Fin (S.arity σ) → Set M.carrier) (i : Fin (S.arity σ))
    (B C : Set M.carrier) :
    M.app σ (Function.update A i (B ∪ C)) =
      M.app σ (Function.update A i B) ∪
        M.app σ (Function.update A i C) := by
  ext u
  constructor
  · rintro ⟨a, ha, hu⟩
    have hai : a i ∈ B ∪ C := by simpa using ha i
    rcases hai with hi | hi
    · left
      exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using hi
        · simpa [Function.update_apply, hji] using ha j, hu⟩
    · right
      exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using hi
        · simpa [Function.update_apply, hji] using ha j, hu⟩
  · rintro (⟨a, ha, hu⟩ | ⟨a, ha, hu⟩)
    · exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using (show a i ∈ B ∪ C from Or.inl (by simpa using ha i))
        · simpa [Function.update_apply, hji] using ha j, hu⟩
    · exact ⟨a, fun j => by
        by_cases hji : j = i
        · subst j
          simpa using (show a i ∈ B ∪ C from Or.inr (by simpa using ha i))
        · simpa [Function.update_apply, hji] using ha j, hu⟩
private theorem Model.app_mono_at (M : Model S) (σ : S.Sym)
    (A : Fin (S.arity σ) → Set M.carrier) (i : Fin (S.arity σ))
    {B C : Set M.carrier} (hBC : B ⊆ C) :
    M.app σ (Function.update A i B) ⊆
      M.app σ (Function.update A i C) := by
  rintro u ⟨a, ha, hu⟩
  exact ⟨a, fun j => by
    by_cases hji : j = i
    · subst j
      simpa using hBC (by simpa using ha i)
    · simpa [Function.update_apply, hji] using ha j, hu⟩
private theorem denote_app_update (M : Model S) (ρ : Var → M.carrier)
    (σ : S.Sym) (args : Fin (S.arity σ) → Pattern S Var)
    (i : Fin (S.arity σ)) (φ : Pattern S Var) :
    M.denote ρ (.app σ (Function.update args i φ)) =
      M.app σ (Function.update (fun j => M.denote ρ (args j)) i
        (M.denote ρ φ)) := by
  simp only [denote_app]
  congr 2
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]
private theorem denote_or (M : Model S) (ρ : Var → M.carrier)
    (φ ψ : Pattern S Var) :
    M.denote ρ (Pattern.or φ ψ) = M.denote ρ φ ∪ M.denote ρ ψ := by
  simp [Pattern.or]
private theorem denote_and (M : Model S) (ρ : Var → M.carrier)
    (φ ψ : Pattern S Var) :
    M.denote ρ (Pattern.and φ ψ) = M.denote ρ φ ∩ M.denote ρ ψ := by
  simp [Pattern.and]
private theorem imp_total_of_subset (M : Model S) (ρ : Var → M.carrier)
    {φ ψ : Pattern S Var} (h : M.denote ρ φ ⊆ M.denote ρ ψ) :
    M.denote ρ (.imp φ ψ) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro u
  by_cases hu : u ∈ M.denote ρ φ
  · exact Set.mem_union_right _ (h hu)
  · exact Set.mem_union_left _ hu
private theorem subset_of_imp_total (M : Model S) (ρ : Var → M.carrier)
    {φ ψ : Pattern S Var} (h : M.denote ρ (.imp φ ψ) = Set.univ) :
    M.denote ρ φ ⊆ M.denote ρ ψ := by
  intro u hu
  have hut : u ∈ M.denote ρ (.imp φ ψ) := by
    rw [h]
    exact Set.mem_univ u
  rcases hut with hnot | hψ
  · exact (hnot hu).elim
  · exact hψ
private theorem denote_appCtx_empty (M : Model S) (ρ : Var → M.carrier)
    (C : AppCtx S Var) {φ : Pattern S Var} (hφ : M.denote ρ φ = ∅) :
    M.denote ρ (C.plug φ) = ∅ := by
  induction C with
  | hole => exact hφ
  | node σ i args C ih =>
      simp only [AppCtx.plug, denote_app]
      apply Model.app_eq_empty M σ _ i
      simpa using ih
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
attribute [local instance] Classical.propDecidable
namespace MatchingLogic
theorem _root_.solution : Soundness S Var := by
  intro Γ φ hprov
  induction hprov with
  | hyp hφ =>
      intro M hM
      exact hM _ hφ
  | taut hp =>
      intro M _ ρ
      exact pform_taut_total M ρ _ hp
  | mp hφ hφψ ihφ ihφψ =>
      intro M hM ρ
      exact Set.eq_univ_iff_forall.mpr fun u =>
        subset_of_imp_total M ρ (ihφψ M hM ρ)
          (by rw [ihφ M hM ρ]; exact Set.mem_univ u)
  | exQuant hcf =>
      intro M _ ρ
      apply imp_total_of_subset M ρ
      intro u hu
      rw [M.denote_substVar_of_captureFree ρ hcf] at hu
      exact Set.mem_iUnion.mpr ⟨ρ _, hu⟩
  | exGen hφψ hxfree ih =>
      rename_i x φ₁ φ₂
      intro M hM ρ
      apply imp_total_of_subset M ρ
      intro u hu
      obtain ⟨a, hua⟩ := Set.mem_iUnion.mp hu
      have huψ := subset_of_imp_total M (Function.update ρ x a)
        (ih M hM (Function.update ρ x a)) hua
      rw [denote_congr M φ₂ (Function.update ρ x a) ρ (by
        intro q hq
        have hqx : q ≠ x := fun h => hxfree (by simpa [h] using hq)
        simp [hqx])] at huψ
      exact huψ
  | propBot =>
      rename_i σ i args
      intro M _ ρ
      apply imp_total_of_subset M ρ
      rw [denote_app_update]
      rw [Model.app_eq_empty M σ _ i (by simp)]
      exact Set.empty_subset _
  | propOr =>
      intro M _ ρ
      apply imp_total_of_subset M ρ
      simp only [denote_app_update, denote_or]
      rw [Model.app_update_union]
  | propEx hfree =>
      rename_i σ i args x φ₀
      intro M _ ρ
      apply imp_total_of_subset M ρ
      simp only [denote_app_update]
      rintro u ⟨a, ha, hu⟩
      have hai : a i ∈ ⋃ b : M.carrier,
          M.denote (Function.update ρ x b) φ₀ := by simpa using ha i
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hai
      apply Set.mem_iUnion.mpr
      refine ⟨b, a, ?_, hu⟩
      intro j
      by_cases hji : j = i
      · subst j
        simpa using hb
      · have hden : M.denote (Function.update ρ x b) (args j) =
            M.denote ρ (args j) := by
          apply denote_congr M (args j)
          intro q hq
          have hqx : q ≠ x := fun h => hfree j hji (by simpa [h] using hq)
          simp [hqx]
        simpa [Function.update_apply, hji, hden] using ha j
  | framing hφψ ih =>
      intro M hM ρ
      apply imp_total_of_subset M ρ
      simp only [denote_app_update]
      apply Model.app_mono_at
      exact subset_of_imp_total M ρ (ih M hM ρ)
  | existence =>
      intro M _ ρ
      apply Set.eq_univ_iff_forall.mpr
      intro u
      exact Set.mem_iUnion.mpr ⟨u, by simp⟩
  | singleton C₁ C₂ =>
      rename_i x φ₀
      intro M _ ρ
      apply imp_total_of_subset M ρ
      by_cases hxφ : ρ x ∈ M.denote ρ φ₀
      · have hnegative :
            M.denote ρ (Pattern.and (.var x) (Pattern.nt φ₀)) = ∅ := by
          rw [denote_and, denote_var, denote_nt]
          ext u
          simp [hxφ]
        have hctx := denote_appCtx_empty M ρ C₂ hnegative
        rw [denote_nt, hctx]
        simp
      · have hpositive : M.denote ρ (Pattern.and (.var x) φ₀) = ∅ := by
          rw [denote_and, denote_var]
          ext u
          simp [hxφ]
        rw [denote_appCtx_empty M ρ C₁ hpositive]
        exact Set.empty_subset _
end MatchingLogic
