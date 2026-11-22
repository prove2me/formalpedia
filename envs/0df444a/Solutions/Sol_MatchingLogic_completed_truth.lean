-- Prove2me | solution 1 for MatchingLogic.completed_truth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:51.320905+00:00
-- url     : https://prove2.me/submissions/0f1b9327-625d-4018-9d18-9e1cd4b09d52

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
public import Theorems.Thm_MatchingLogic_AppCtx_plug_comp
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_witnessed
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_GeneratedCarrier_isMCS
public import Theorems.Thm_MatchingLogic_GeneratedCarrier_witnessed
public import Theorems.Thm_MatchingLogic_IsMCS_bot_not_mem
public import Theorems.Thm_MatchingLogic_IsMCS_imp_mem_iff
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp
public import Theorems.Thm_MatchingLogic_IsMCS_mp_mem
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_denote_captureAvoidingSubst
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_trans
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote
public import Theorems.Thm_MatchingLogic_Pattern_complexity_captureAvoidingSubst
public import Theorems.Thm_MatchingLogic_Provable_captureAvoidingExQuant
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_completedEmbed_injective
public import Theorems.Thm_MatchingLogic_completedEmbed_mem_completedInterp_iff
public import Theorems.Thm_MatchingLogic_completedModel_interp
public import Theorems.Thm_MatchingLogic_completedValuation_eq_embed_iff
public import Theorems.Thm_MatchingLogic_completedValuation_surjective
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_mem_completedInterp
public import Theorems.Thm_MatchingLogic_mem_generatedInterp
attribute [local simp] MatchingLogic.AppCtx.plug_comp
attribute [local simp] MatchingLogic.CanonicalCarrier.coe_mk
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
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.canonicalStep_iff
attribute [local simp] MatchingLogic.completedModel_interp
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingContext_nil
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.mem_canonicalInterp
attribute [local simp] MatchingLogic.mem_completedInterp
attribute [local simp] MatchingLogic.mem_generatedInterp


section
@[expose] public section
namespace MatchingLogic
open Set
open scoped BigOperators
variable {S : Signature}
noncomputable section
private theorem completed_truth_at_complexity
    (hExist : CanonicalExistenceProperty S) (root : CanonicalCarrier S) :
    ∀ n : Nat, ∀ p : Pattern S Nat, p.complexity = n →
      ∀ world : GeneratedCarrier root,
        p ∈ world.val.val ↔
          completedEmbed root world ∈
            (completedModel root).denote (completedValuation root) p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p hcomplexity world
      cases p with
      | var x =>
          simpa [denote_var, eq_comm] using
            (completedValuation_eq_embed_iff root x world).symm
      | bot =>
          simp [denote_bot, GeneratedCarrier.isMCS world |>.bot_not_mem]
      | imp p q =>
          have hpLt : p.complexity < n := by
            rw [← hcomplexity]
            simp only [Pattern.complexity]
            omega
          have hqLt : q.complexity < n := by
            rw [← hcomplexity]
            simp only [Pattern.complexity]
            omega
          have hp := ih p.complexity hpLt p rfl world
          have hq := ih q.complexity hqLt q rfl world
          have hbool := (GeneratedCarrier.isMCS world).imp_mem_iff p q
          rw [denote_imp]
          simp only [Set.mem_union, Set.mem_compl_iff]
          exact hbool.trans (or_congr (not_congr hp) hq)
      | app sigma args =>
          have hargLe : ∀ i : Fin (S.arity sigma),
              (args i).complexity ≤ ∑ j, (args j).complexity := by
            intro i
            exact Finset.single_le_sum
              (f := fun j : Fin (S.arity sigma) => (args j).complexity)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          have hargLt : ∀ i : Fin (S.arity sigma),
              (args i).complexity < n := by
            intro i
            have hle := hargLe i
            rw [← hcomplexity]
            simp only [Pattern.complexity]
            omega
          constructor
          · intro happ
            obtain ⟨components, hargs, hinterp⟩ :=
              hExist world.val sigma args happ
            have hgenerated : ∀ i, Generated root (components i) := by
              intro i
              exact world.property.tail
                ((canonicalStep_iff world.val (components i)).mpr
                  ⟨sigma, components, i, hinterp, rfl⟩)
            let generatedComponents : Fin (S.arity sigma) → GeneratedCarrier root :=
              fun i => ⟨components i, hgenerated i⟩
            have hdenArgs : ∀ i,
                completedEmbed root (generatedComponents i) ∈
                  (completedModel root).denote (completedValuation root) (args i) := by
              intro i
              exact (ih (args i).complexity (hargLt i) (args i) rfl
                (generatedComponents i)).mp (hargs i)
            have hgeneratedInterp : world ∈
                generatedInterp root sigma generatedComponents := by
              change world.val ∈ canonicalInterp sigma
                (fun i => (generatedComponents i).val)
              simpa [generatedComponents] using hinterp
            rw [denote_app]
            refine ⟨fun i => completedEmbed root (generatedComponents i), hdenArgs, ?_⟩
            exact (completedEmbed_mem_completedInterp_iff
              root generatedComponents world).mpr hgeneratedInterp
          · intro hden
            rw [denote_app] at hden
            rcases hden with ⟨inputs, hdenArgs, hout⟩
            change completedEmbed root world ∈
              completedInterp root sigma inputs at hout
            rcases hout with ⟨components, hinputs, hreal | hstar⟩
            · rcases hreal with ⟨output, houtput, hinterp⟩
              have hworld : world = output :=
                completedEmbed_injective root houtput
              subst output
              apply (mem_generatedInterp.mp hinterp) args
              intro i
              apply (ih (args i).complexity (hargLt i) (args i) rfl
                (components i)).mpr
              rw [← hinputs i]
              exact hdenArgs i
            · have himpossible : (completedEmbed root world).val = none := hstar.1
              simp [completedEmbed] at himpossible
      | ex x p =>
          have hpLt : p.complexity < n := by
            rw [← hcomplexity]
            simp [Pattern.complexity]
          constructor
          · intro hex
            obtain ⟨y, himp⟩ := (GeneratedCarrier.witnessed world) hex
            let q := Pattern.captureAvoidingSubst x y p
            have hqComplexity : q.complexity < n := by
              rw [Pattern.complexity_captureAvoidingSubst]
              exact hpLt
            have hq : q ∈ world.val.val :=
              (GeneratedCarrier.isMCS world).mp_mem hex himp
            have hqDenote :=
              (ih q.complexity hqComplexity q rfl world).mp hq
            have hupdated : completedEmbed root world ∈
                (completedModel root).denote
                  (Function.update (completedValuation root) x
                    (completedValuation root y)) p := by
              rw [← Model.denote_captureAvoidingSubst]
              exact hqDenote
            rw [denote_ex]
            exact Set.mem_iUnion.mpr ⟨completedValuation root y, hupdated⟩
          · intro hden
            rw [denote_ex] at hden
            rcases Set.mem_iUnion.mp hden with ⟨point, hpoint⟩
            obtain ⟨z, rfl⟩ := completedValuation_surjective root point
            let q := Pattern.captureAvoidingSubst x z p
            have hqComplexity : q.complexity < n := by
              rw [Pattern.complexity_captureAvoidingSubst]
              exact hpLt
            have hqDenote : completedEmbed root world ∈
                (completedModel root).denote (completedValuation root) q := by
              rw [Model.denote_captureAvoidingSubst]
              exact hpoint
            have hq : q ∈ world.val.val :=
              (ih q.complexity hqComplexity q rfl world).mpr hqDenote
            exact (GeneratedCarrier.isMCS world).mem_of_provable_imp hq
              (Provable.captureAvoidingExQuant x z p)
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
open scoped BigOperators
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatTruth
namespace MatchingLogic
theorem _root_.solution (hExist : CanonicalExistenceProperty S)
    (root : CanonicalCarrier S) (world : GeneratedCarrier root)
    (p : Pattern S Nat) :
    p ∈ world.val.val ↔
      completedEmbed root world ∈
        (completedModel root).denote (completedValuation root) p :=
  completed_truth_at_complexity hExist root p.complexity p rfl world
end MatchingLogic
