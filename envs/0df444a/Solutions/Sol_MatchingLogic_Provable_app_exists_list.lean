-- Prove2me | solution 1 for MatchingLogic.Provable.app_exists_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:39.772822+00:00
-- url     : https://prove2.me/submissions/7ef92bcb-8dc1-40f2-ad54-ec85b1d45c1a

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Provable_imp_refl
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature}
namespace Pattern
end Pattern
namespace Pattern
end Pattern
private theorem Provable.app_exists_list_aux {Gamma : Set (Pattern S Nat)}
    {sigma : S.Sym} (is : List (Fin (S.arity sigma)))
    (y : Fin (S.arity sigma) -> Nat)
    (body : Fin (S.arity sigma) -> Pattern S Nat)
    (hnodup : is.Nodup)
    (hfresh : forall i j, i ≠ j -> y i ∉ FV (body j)) :
    Provable Gamma (.imp
      (.app sigma (Pattern.exOn is y body))
      (Pattern.exList (is.map y) (.app sigma body))) := by
  induction is with
  | nil =>
      have heq : Pattern.exOn [] y body = body := by
        funext i
        simp [Pattern.exOn]
      simpa [heq, Pattern.exList] using
        (Provable.imp_refl Gamma (.app sigma body))
  | cons i is ih =>
      have hi : i ∉ is := (List.nodup_cons.mp hnodup).1
      have htail : is.Nodup := (List.nodup_cons.mp hnodup).2
      have hside : forall j, j ≠ i ->
          y i ∉ FV (Pattern.exOn is y body j) := by
        intro j hji
        by_cases hj : j ∈ is
        · rw [Pattern.exOn, if_pos hj]
          intro hmem
          by_cases hyij : y i = y j
          · exact hmem.2 hyij
          · exact hfresh i j (Ne.symm hji) hmem.1
        · simpa [Pattern.exOn, hj] using hfresh i j (Ne.symm hji)
      have hprop := Provable.propEx (Γ := Gamma) (σ := sigma) (i := i)
        (args := Pattern.exOn is y body) (x := y i) (φ := body i) hside
      have hstep : Provable Gamma
          (.imp (.app sigma (Pattern.exOn (i :: is) y body))
            (.ex (y i) (.app sigma (Pattern.exOn is y body)))) := by
        have hleft :
            Function.update (Pattern.exOn is y body) i (.ex (y i) (body i)) =
              Pattern.exOn (i :: is) y body := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [Pattern.exOn]
          · simp [Pattern.exOn, hji]
        have hright :
            Function.update (Pattern.exOn is y body) i (body i) =
              Pattern.exOn is y body := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [Pattern.exOn, hi]
          · simp [hji]
        simpa only [hleft, hright] using hprop
      have hrec := ih htail
      exact hstep.imp_trans (by
        simpa [Pattern.exList] using Provable.ex_mono hrec)
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    {sigma : S.Sym} (y : Fin (S.arity sigma) -> Nat)
    (body : Fin (S.arity sigma) -> Pattern S Nat)
    (hfresh : forall i j, i ≠ j -> y i ∉ FV (body j)) :
    Provable Gamma (.imp
      (.app sigma (fun i => .ex (y i) (body i)))
      (Pattern.exList (List.ofFn y) (.app sigma body))) := by
  have hn : (List.ofFn (fun i : Fin (S.arity sigma) => i)).Nodup := by
    rw [List.nodup_ofFn]
    exact Function.injective_id
  have h := Provable.app_exists_list_aux (Gamma := Gamma) (sigma := sigma)
    (List.ofFn (fun i : Fin (S.arity sigma) => i)) y body hn hfresh
  have hexOn :
      Pattern.exOn (List.ofFn (fun i : Fin (S.arity sigma) => i)) y body =
        (fun i => .ex (y i) (body i)) := by
    funext i
    rw [Pattern.exOn, if_pos (List.mem_ofFn.mpr ⟨i, rfl⟩)]
  simpa [hexOn, List.map_ofFn, Function.comp_def] using h
end Provable
end MatchingLogic
