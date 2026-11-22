-- Prove2me | solution 1 for MatchingLogic.IsMCS.exList_witness_elim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:42.780901+00:00
-- url     : https://prove2.me/submissions/f1eefa95-ccd6-4540-983c-71b27fcc4b9f

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_freshWitness_elim
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars
public import Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_comp_eq_of_fresh_result
public import Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_eq_substVar_of_fresh
public import Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_not_mem_FV_of_ne
public import Theorems.Thm_MatchingLogic_Pattern_substVar_eq_self_of_not_mem_FV
public import Theorems.Thm_MatchingLogic_Pattern_substVar_exList
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
private theorem substVar_witnessBody_update {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (w : Fin (S.arity sigma) -> Nat)
    (i : Fin (S.arity sigma)) (z : Nat)
    (hwP : ∀ j, w j ∉ p.allVars)
    (hwPhi : ∀ j k, w j ∉ (Phi k).allVars)
    (hwi : ∀ j, j ≠ i -> w i ≠ w j)
    (hz : z ∉ (witnessBody sigma Phi p x w).allVars) :
    substVar (w i) z (witnessBody sigma Phi p x w) =
      witnessBody sigma Phi p x (Function.update w i z) := by
  have hzarg : ∀ j, z ∉
      (Pattern.and (Phi j)
        (.imp (.ex x p) (captureAvoidingSubst x (w j) p))).allVars := by
    intro j hmem
    apply hz
    simp only [witnessBody, allVars, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    exact ⟨j, hmem⟩
  have hzPhi : ∀ j, z ∉ (Phi j).allVars := by
    intro j hmem
    exact hzarg j (by simp [allVars, hmem])
  have hzP : z ∉ p.allVars := by
    intro hmem
    exact hzarg i (by simp [allVars, hmem])
  have hzSub : z ∉ (substVar x (w i) p).allVars := by
    rw [← captureAvoidingSubst_eq_substVar_of_fresh (hwP i)]
    intro hmem
    exact hzarg i (by simp [allVars, hmem])
  simp only [witnessBody, substVar]
  congr
  funext j
  have hPhiRaw : substVar (w i) z (Phi j) = Phi j :=
    substVar_eq_self_of_not_mem_FV (fun h => hwPhi i j ((Phi j).FV_subset_allVars h))
  have hPRaw : substVar (w i) z p = p :=
    substVar_eq_self_of_not_mem_FV (fun h => hwP i (p.FV_subset_allVars h))
  have hcond : ¬ x = w i -> substVar (w i) z p = p := fun _ => hPRaw
  by_cases hji : j = i
  · subst j
    have hzCA : z ∉ (captureAvoidingSubst x (w i) p).allVars := by
      simpa [captureAvoidingSubst_eq_substVar_of_fresh (hwP i)] using hzSub
    have hcur : substVar (w i) z (captureAvoidingSubst x (w i) p) =
        captureAvoidingSubst x z p := by
      have hc := captureAvoidingSubst_comp_eq_of_fresh_result
        (x := x) (y := w i) (z := z) (p := p) (hwP i) hzP hzSub
      simpa [captureAvoidingSubst_eq_substVar_of_fresh hzCA] using hc
    simpa only [Function.update_self, imp.injEq, ite_eq_left_iff, ex.injEq,
      true_and, and_true] using And.intro hPhiRaw (And.intro hcond hcur)
  · have hwne : w i ≠ w j := hwi j hji
    have hother : substVar (w i) z (captureAvoidingSubst x (w j) p) =
        captureAvoidingSubst x (w j) p :=
      substVar_eq_self_of_not_mem_FV
        (captureAvoidingSubst_not_mem_FV_of_ne hwne
          (fun h => hwP i (p.FV_subset_allVars h)))
    have hupdate : Function.update w i z j = w j := by simp [hji]
    simpa only [hupdate, imp.injEq, ite_eq_left_iff, ex.injEq, true_and,
      and_true] using And.intro hPhiRaw (And.intro hcond hother)
private theorem allVars_subset_exList (ys : List Nat) (q : Pattern S Nat) :
    q.allVars ⊆ (exList ys q).allVars := by
  induction ys with
  | nil => exact fun _ h => h
  | cons y ys ih =>
      intro a ha
      simp only [exList, allVars, Finset.mem_insert]
      exact Or.inr (ih ha)
private theorem mem_allVars_exList_of_mem {a : Nat} {ys : List Nat}
    {q : Pattern S Nat} (ha : a ∈ ys) : a ∈ (exList ys q).allVars := by
  induction ys with
  | nil => simp at ha
  | cons y ys ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [exList, allVars]
      · simp only [exList, allVars, Finset.mem_insert]
        exact Or.inr (ih ha)
private theorem IsMCS.exList_witness_elim_aux {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (is : List (Fin (S.arity sigma)))
    (his : is.Nodup) (w : Fin (S.arity sigma) -> Nat)
    (hwP : ∀ j, w j ∉ p.allVars)
    (hwPhi : ∀ j k, w j ∉ (Phi k).allVars)
    (hwdist : ∀ i ∈ is, ∀ j, i ≠ j -> w i ≠ w j)
    (hmem : Pattern.exList (is.map w) (Pattern.witnessBody sigma Phi p x w) ∈ Gamma) :
    ∃ out : Fin (S.arity sigma) -> Nat,
      (∀ j, out j ∉ p.allVars) ∧
      (∀ j k, out j ∉ (Phi k).allVars) ∧
      Pattern.witnessBody sigma Phi p x out ∈ Gamma := by
  induction is generalizing w with
  | nil =>
      exact ⟨w, hwP, hwPhi, by simpa [Pattern.exList] using hmem⟩
  | cons i is ih =>
      have hi : i ∉ is := (List.nodup_cons.mp his).1
      have his' : is.Nodup := (List.nodup_cons.mp his).2
      have hhead : Pattern.ex (w i)
          (Pattern.exList (is.map w) (Pattern.witnessBody sigma Phi p x w)) ∈ Gamma := by
        simpa [Pattern.exList] using hmem
      obtain ⟨z, hzq, hsub⟩ := hM.freshWitness_elim hW hhead
      have hraw : substVar (w i) z
          (Pattern.exList (is.map w) (Pattern.witnessBody sigma Phi p x w)) ∈ Gamma := by
        simpa [Pattern.captureAvoidingSubst_eq_substVar_of_fresh hzq] using hsub
      have hdist : ∀ a ∈ is.map w, w i ≠ a := by
        intro a ha
        rcases List.mem_map.mp ha with ⟨j, hj, rfl⟩
        exact hwdist i (by simp) j (fun h => hi (h ▸ hj))
      have hzbody : z ∉ (Pattern.witnessBody sigma Phi p x w).allVars := by
        intro hzmem
        exact hzq (Pattern.allVars_subset_exList (is.map w)
          (Pattern.witnessBody sigma Phi p x w) hzmem)
      let w' := Function.update w i z
      have hbody : substVar (w i) z (Pattern.witnessBody sigma Phi p x w) =
          Pattern.witnessBody sigma Phi p x w' := by
        apply Pattern.substVar_witnessBody_update Phi p x w i z hwP hwPhi
        · intro j hji
          exact hwdist i (by simp) j hji.symm
        · exact hzbody
      have hzTail : ∀ a ∈ is, z ≠ w a := by
        intro a ha hEq
        apply hzq
        rw [hEq]
        exact Pattern.mem_allVars_exList_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)
      have htailNames : is.map w' = is.map w := by
        apply List.map_congr_left
        intro j hj
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        simp [w', hji]
      have hnext : Pattern.exList (is.map w')
          (Pattern.witnessBody sigma Phi p x w') ∈ Gamma := by
        rw [Pattern.substVar_exList (is.map w)
          (Pattern.witnessBody sigma Phi p x w) hdist] at hraw
        rw [hbody] at hraw
        simpa [htailNames] using hraw
      have hzarg : ∀ j, z ∉
          (Pattern.and (Phi j)
            (.imp (.ex x p) (Pattern.captureAvoidingSubst x (w j) p))).allVars := by
        intro j hzmem
        exact hzbody (by
          simp only [Pattern.witnessBody, Pattern.allVars,
            Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨j, hzmem⟩)
      have hzP : z ∉ p.allVars := by
        intro hzmem
        exact hzarg i (by simp [Pattern.allVars, hzmem])
      have hzPhi : ∀ j, z ∉ (Phi j).allVars := by
        intro j hzmem
        exact hzarg j (by simp [Pattern.allVars, hzmem])
      have hwP' : ∀ j, w' j ∉ p.allVars := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa [w'] using hzP
        · simpa [w', hji] using hwP j
      have hwPhi' : ∀ j k, w' j ∉ (Phi k).allVars := by
        intro j k
        by_cases hji : j = i
        · subst j
          simpa [w'] using hzPhi k
        · simpa [w', hji] using hwPhi j k
      have hwdist' : ∀ a ∈ is, ∀ b, a ≠ b -> w' a ≠ w' b := by
        intro a ha b hab
        have hai : a ≠ i := fun h => hi (h ▸ ha)
        by_cases hbi : b = i
        · subst b
          simpa [w', hai] using (hzTail a ha).symm
        · simpa [w', hai, hbi] using hwdist a (by simp [ha]) b hab
      exact ih his' w' hwP' hwPhi' hwdist' hnext
end Pattern
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (hnested : Pattern.exList (List.ofFn y)
      (.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma) :
    ∃ z : Fin (S.arity sigma) -> Nat,
      (forall i, z i ∉ p.allVars) ∧
      (forall i j, z i ∉ (Phi j).allVars) ∧
      Pattern.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (z i) p))) ∈ Gamma := by
  let ids := List.ofFn (fun i : Fin (S.arity sigma) => i)
  have hids : ids.Nodup := by
    dsimp [ids]
    rw [List.nodup_ofFn]
    exact Function.injective_id
  have hnested' : Pattern.exList (ids.map y)
      (Pattern.witnessBody sigma Phi p x y) ∈ Gamma := by
    simpa [ids, Pattern.witnessBody, List.map_ofFn, Function.comp_def] using hnested
  have hdist : ∀ i ∈ ids, ∀ j, i ≠ j -> y i ≠ y j := by
    intro i _ j hij
    exact hyinj.ne hij
  simpa [Pattern.witnessBody] using
    (Pattern.IsMCS.exList_witness_elim_aux hM hW Phi p x ids hids y
      hyfreshP hyfreshPhi hdist hnested')
end IsMCS
end MatchingLogic
