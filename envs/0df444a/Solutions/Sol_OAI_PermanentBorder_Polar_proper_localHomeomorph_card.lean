-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.proper_localHomeomorph_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:03:17.100916+00:00
-- url     : https://prove2.me/submissions/5f40a241-e0bf-49c3-83eb-fc6b6336c7bc

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RegularSections.lean:L361-L375
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.proper_localHomeomorph_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections

-- ---- from OAI.Algebra.Determinantal.RegularSections ----
namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem localHomeomorph_restrictPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (h : IsLocalHomeomorph f) (s : Set Y) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U,hU,hE⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp h x.val
  let V : Set (f ⁻¹' s) := Subtype.val ⁻¹' U
  let e : V ≃ₜ ((U.domRestrict f) ⁻¹' s) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨V, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
  exact (hE.restrictPreimage s).comp e.isOpenEmbedding

theorem covering_card_locallyConstant {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (h : IsCoveringMap f) :
    IsLocallyConstant (fun y => Nat.card (f ⁻¹' {y})) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  obtain ⟨hd,U,hy,hU,hf,H,hH⟩ := h y
  filter_upwards [hU.mem_nhds hy] with z hz
  have he : IsEvenlyCovered f z (f ⁻¹' {y}) := ⟨hd,U,hz,hU,hf,H,hH⟩
  exact Nat.card_congr he.fiberHomeomorph.toEquiv.symm

theorem proper_localHomeomorph_card {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [PreconnectedSpace Y] {f : X → Y}
    (hp : IsProperMap f) (hl : IsLocalHomeomorph f) (y z : Y) :
    Nat.card (f ⁻¹' {y}) = Nat.card (f ⁻¹' {z}) := by
  have hfin (a : Y) : (f ⁻¹' {a}).Finite := by
    let : CompactSpace (f ⁻¹' {a}) := isCompact_iff_compactSpace.mp
      (hp.isCompact_preimage isCompact_singleton)
    let : DiscreteTopology (f ⁻¹' {a}) :=
      (localHomeomorph_restrictPreimage hl {a}).comap_discreteTopology
    exact Set.finite_coe_iff.mp finite_of_compact_of_discrete
  have hcov : IsCoveringMap f := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    exact hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun a _ => hfin a) hl.isLocalHomeomorphOn
  exact (covering_card_locallyConstant hcov).apply_eq_of_preconnectedSpace y z

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open Topology Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.proper_localHomeomorph_card := @_root_.OAI.PermanentBorder.Polar.proper_localHomeomorph_card
