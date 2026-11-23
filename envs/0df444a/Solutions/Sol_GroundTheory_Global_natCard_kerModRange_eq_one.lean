-- Prove2me | solution 1 for GroundTheory.Global.natCard_kerModRange_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:29.749803+00:00
-- url     : https://prove2.me/submissions/f3456869-8da2-4146-804a-26d79355291a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_mk_eq_mk_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.ProfCoh
  GroundTheory.GroupCoh
open scoped NumberField.LiesOver ComplexConjugate
namespace GroundTheory.Global
theorem _root_.solution {A : Type*} [AddCommGroup A] {f g : A →+ A}
    (h : ∀ x ∈ f.ker, x ∈ g.range) : Nat.card (KerModRange f g) = 1 := by
  have : Subsingleton (KerModRange f g) := ⟨fun p q => by
    induction p using QuotientAddGroup.induction_on with | H x =>
    induction q using QuotientAddGroup.induction_on with | H y =>
    rw [KerModRange.mk_eq_mk_iff]
    exact h _ (sub_mem x.2 y.2)⟩
  exact Nat.card_of_subsingleton (0 : KerModRange f g)
end GroundTheory.Global
