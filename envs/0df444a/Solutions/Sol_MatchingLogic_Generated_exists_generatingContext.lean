-- Prove2me | solution 1 for MatchingLogic.Generated.exists_generatingContext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:39.561961+00:00
-- url     : https://prove2.me/submissions/118b4cef-0e79-4314-8b48-f297d3247cd6

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_Generated_exists_generatingPath
public import Theorems.Thm_MatchingLogic_GeneratingPath_plug_mem_root

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
namespace MatchingLogic
namespace Generated
theorem _root_.solution {root world : CanonicalCarrier S}
    (hgen : Generated root world) :
    ∃ C : AppCtx S Nat,
      ∀ p ∈ (world : Set (Pattern S Nat)),
        C.plug p ∈ (root : Set (Pattern S Nat)) := by
  obtain ⟨path, hpath⟩ := hgen.exists_generatingPath
  exact ⟨generatingContext path, fun _ hp => hpath.plug_mem_root hp⟩
end Generated
end MatchingLogic
