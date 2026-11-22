-- Prove2me | solution 1 for MatchingLogic.generated_singleton_variables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:56.812121+00:00
-- url     : https://prove2.me/submissions/2126db32-bbb7-49d9-a3e9-584de86b3c6f

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_AppCtx_plug_comp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_GeneratedCarrier_isMCS
public import Theorems.Thm_MatchingLogic_mem_generatedInterp
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_Generated_exists_generatingPath
public import Theorems.Thm_MatchingLogic_GeneratingPath_plug_mem_root
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_and_mem_iff
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_empty
public import Theorems.Thm_MatchingLogic_IsMCS_mp_mem
public import Theorems.Thm_MatchingLogic_IsMCS_neg_mem_iff_not_mem
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_LocProvable_of_mem
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
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
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.mem_canonicalInterp


attribute [local simp] MatchingLogic.AppCtx.plug_comp
attribute [local simp] MatchingLogic.canonicalStep_iff
attribute [local simp] MatchingLogic.mem_generatedInterp
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.generatingContext_nil
section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
namespace AppCtx
end AppCtx
namespace GeneratedCarrier
end GeneratedCarrier
private theorem subset_of_shared_var_and_paths
    (root left right : CanonicalCarrier S)
    {leftPath rightPath : List (Coord S)}
    (hleftPath : GeneratingPath root left leftPath)
    (hrightPath : GeneratingPath root right rightPath)
    {x : Nat} (hxleft : Pattern.var x ∈ (left : Set (Pattern S Nat)))
    (hxright : Pattern.var x ∈ (right : Set (Pattern S Nat))) :
    (left : Set (Pattern S Nat)) ⊆ (right : Set (Pattern S Nat)) := by
  intro p hp
  by_contra hnright
  have hntp : Pattern.nt p ∈ (right : Set (Pattern S Nat)) :=
    (CanonicalCarrier.isMCS right).neg_mem_iff_not_mem.mpr hnright
  have hleftAnd : Pattern.and (.var x) p ∈
      (left : Set (Pattern S Nat)) :=
    (CanonicalCarrier.isMCS left).and_mem_iff.mpr ⟨hxleft, hp⟩
  have hrightAnd : Pattern.and (.var x) (Pattern.nt p) ∈
      (right : Set (Pattern S Nat)) :=
    (CanonicalCarrier.isMCS right).and_mem_iff.mpr ⟨hxright, hntp⟩
  have hleftRoot := hleftPath.plug_mem_root hleftAnd
  have hrightRoot := hrightPath.plug_mem_root hrightAnd
  have hsingle : Provable (∅ : Set (Pattern S Nat))
      (.imp ((generatingContext leftPath).plug (Pattern.and (.var x) p))
        (Pattern.nt
          ((generatingContext rightPath).plug
            (Pattern.and (.var x) (Pattern.nt p))))) :=
    Provable.singleton (generatingContext leftPath) (generatingContext rightPath)
  have hsingleRoot :=
    (CanonicalCarrier.isMCS root).mem_of_provable_empty hsingle
  have hnotRight :=
    (CanonicalCarrier.isMCS root).mp_mem hleftRoot hsingleRoot
  exact (CanonicalCarrier.isMCS root).1
    ((LocProvable.of_mem hrightRoot).mp (LocProvable.of_mem hnotRight))
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
namespace MatchingLogic
theorem _root_.solution (root : CanonicalCarrier S)
    {left right : CanonicalCarrier S}
    (hleft : Generated root left) (hright : Generated root right)
    {x : Nat} (hxleft : Pattern.var x ∈ (left : Set (Pattern S Nat)))
    (hxright : Pattern.var x ∈ (right : Set (Pattern S Nat))) :
    left = right := by
  obtain ⟨leftPath, hleftPath⟩ := hleft.exists_generatingPath
  obtain ⟨rightPath, hrightPath⟩ := hright.exists_generatingPath
  apply Subtype.ext
  exact Set.Subset.antisymm
    (subset_of_shared_var_and_paths root left right hleftPath hrightPath hxleft hxright)
    (subset_of_shared_var_and_paths root right left hrightPath hleftPath hxright hxleft)
end MatchingLogic
