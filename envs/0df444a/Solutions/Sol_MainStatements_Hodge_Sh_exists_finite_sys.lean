-- Prove2me | solution 1 for MainStatements.Hodge.Sh.exists_finite_sys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:24.613531+00:00
-- url     : https://prove2.me/submissions/6d99e35d-bc5e-4ec1-98fe-a411096303e7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_FinSys

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Sh
namespace MainStatements.Hodge.Sh
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsSeparated s)
    (hq : QuasiCompact s) : ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have := hq
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U.1 : Set X))
    (fun U ↦ U.1.isOpen) fun x _ ↦ by
      have hx : x ∈ ⨆ i : X.affineOpens, (i : X.Opens) := (iSup_affineOpens_eq_top X).symm ▸ trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  refine ⟨NEFin t, inferInstance, inferInstance, ⟨sysOfCover s hs (fun i : t ↦ i.1) ?_⟩⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hit⟩, hi⟩
end MainStatements.Hodge.Sh
