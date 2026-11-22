-- Prove2me | solution 1 for MatchingLogic.EntryIII.realize_toFOAux_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:28.284958+00:00
-- url     : https://prove2.me/submissions/9ab6ddd8-be57-464e-95e5-2b54b7cd6f24

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.EntryIII
theorem _root_.solution (M : Model S) [(relLanguage S).Structure M.carrier]
    (hcompat : ∀ (sigma : S.Sym) (out : M.carrier)
      (args : Fin (S.arity sigma) → M.carrier),
      FirstOrder.Language.Structure.RelMap (relSym sigma) (Fin.cons out args) ↔
        out ∈ M.interp sigma args)
    (p : Pattern S Var) {alpha : Type u}
    (eta : Var → alpha) (cur : alpha) (v : alpha → M.carrier) :
    FirstOrder.Language.Formula.Realize
        (MatchingLogic.EntryIII.Pattern.toFOAux p eta cur) v ↔
      v cur ∈ M.denote (v ∘ eta) p := by
  induction p generalizing alpha with
  | var x => simp [Pattern.toFOAux, Function.comp_def]
  | bot => simp [Pattern.toFOAux]
  | imp phi psi ihphi ihpsi =>
      rw [Pattern.toFOAux, FirstOrder.Language.Formula.realize_imp,
        ihphi eta cur v, ihpsi eta cur v]
      simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
      tauto
  | ex x phi ih =>
      simp only [Pattern.toFOAux, FirstOrder.Language.Formula.realize_iExs,
        denote_ex, Set.mem_iUnion]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w (), ?_⟩
        rw [ih (Function.update (Sum.inl ∘ eta) x (Sum.inr ())) (Sum.inl cur)
          (Sum.elim v w)] at hw
        have heq :
            Sum.elim v w ∘ Function.update (Sum.inl ∘ eta) x (Sum.inr ()) =
              Function.update (v ∘ eta) x (w ()) := by
          funext y
          by_cases hy : y = x
          · subst y
            simp
          · simp [hy, Function.comp_def]
        rwa [heq] at hw
      · rintro ⟨a, ha⟩
        refine ⟨fun _ => a, ?_⟩
        rw [ih (Function.update (Sum.inl ∘ eta) x (Sum.inr ())) (Sum.inl cur)
          (Sum.elim v (fun _ => a))]
        have heq :
            Sum.elim v (fun _ => a) ∘
                Function.update (Sum.inl ∘ eta) x (Sum.inr ()) =
              Function.update (v ∘ eta) x a := by
          funext y
          by_cases hy : y = x
          · subst y
            simp
          · simp [hy, Function.comp_def]
        rwa [heq]
  | app sigma args ih =>
      simp only [Pattern.toFOAux, FirstOrder.Language.Formula.realize_iExs,
        FirstOrder.Language.Formula.realize_inf,
        FirstOrder.Language.Formula.realize_rel,
        FirstOrder.Language.Formula.realize_iInf,
        denote_app, MatchingLogic.Model.app]
      constructor
      · rintro ⟨w, hrel, hargs⟩
        have htuple :
            (fun i => FirstOrder.Language.Term.realize (Sum.elim v w)
              ((Fin.cons (FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inl cur))
                (fun j => FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inr j)) :
                  Fin (S.arity sigma + 1) →
                    (relLanguage S).Term (alpha ⊕ Fin (S.arity sigma))) i)) =
              Fin.cons (v cur) w := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        rw [htuple] at hrel
        refine ⟨w, ?_, ?_⟩
        · intro i
          have hi := hargs i
          rw [ih i (Sum.inl ∘ eta) (Sum.inr i) (Sum.elim v w)] at hi
          simpa [Function.comp_def] using hi
        · exact (hcompat sigma (v cur) w).mp (by simpa using hrel)
      · rintro ⟨w, hargs, hrel⟩
        have htuple :
            (fun i => FirstOrder.Language.Term.realize (Sum.elim v w)
              ((Fin.cons (FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inl cur))
                (fun j => FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inr j)) :
                  Fin (S.arity sigma + 1) →
                    (relLanguage S).Term (alpha ⊕ Fin (S.arity sigma))) i)) =
              Fin.cons (v cur) w := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        refine ⟨w, ?_, ?_⟩
        · rw [htuple]
          exact (hcompat sigma (v cur) w).mpr hrel
        · intro i
          rw [ih i (Sum.inl ∘ eta) (Sum.inr i) (Sum.elim v w)]
          simpa [Function.comp_def] using hargs i
end MatchingLogic.EntryIII
