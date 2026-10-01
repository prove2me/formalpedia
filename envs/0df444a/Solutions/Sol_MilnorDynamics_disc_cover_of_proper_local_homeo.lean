-- Prove2me | solution 1 for MilnorDynamics.disc_cover_of_proper_local_homeo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:27:33.203355+00:00
-- url     : https://prove2.me/submissions/79100b8c-b8f8-4bfb-85f4-f4b18cec91a7

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- Proof of `MilnorDynamics.disc_cover_of_proper_local_homeo`.
--
-- A proper local homeomorphism onto a Hausdorff space is a covering map. `g` is
-- proper, hence closed; it is a local homeomorphism, so the preimage of each point
-- is discrete (injective there via an open partial homeomorph); a proper map has
-- compact fibres; compact and discrete is finite; a closed map that is a local
-- homeomorphism on the preimage of every point with finite fibres is a covering map
-- on that set.
--
-- Math used:
--   IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn  Mathlib/Topology/Covering/Basic.lean:560
--   IsProperMap.isClosedMap                              Mathlib/Topology/Maps/Proper/Basic.lean:92
--   IsProperMap.isCompact_preimage                       Mathlib/Topology/Maps/Proper/Basic.lean:210
--   IsLocalHomeomorph.isLocalHomeomorphOn               Mathlib/Topology/IsLocalHomeomorph.lean:178
--   IsDiscrete.of_openPartialHomeomorph                Mathlib/Topology/Covering/Basic.lean:499
--   IsCompact.finite                                    Mathlib/Topology/Compactness/Compact.lean:1060
--   isCoveringMap_iff_isCoveringMapOn_univ              Mathlib/Topology/Covering/Basic.lean:294
--
-- `T2Space` is required on `Metric.ball 0 1`; it propagates from `ℂ`
-- (T2Space, Complex/Basic.lean:128) to subtypes (Hausdorff.lean:358).
--
-- The goal is first rewritten to `IsCoveringMapOn g Set.univ`, so `s` is fixed by the
-- goal before `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` is applied; no
-- explicit `{0, 1}ᶜ` term is ever ascribed against a metavariable sort.

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution {p : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ p (Metric.ball 0 1))
    (hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))
    (himage : p '' (Metric.ball 0 1) = {0, 1}ᶜ)
    (hproper : IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)))
    (hlocal :
      IsLocalHomeomorph (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))) :
    IsCoveringMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun x _ => ?_) (hlocal.isLocalHomeomorphOn)
  have hc : IsCompact {x} := isCompact_singleton
  have hdisc : IsDiscrete ((hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) ⁻¹' {x}) := by
    refine IsDiscrete.of_openPartialHomeomorph _ subset_rfl (fun e _ => by
      rcases hlocal e with ⟨φ, hφmem, hφeq⟩
      exact ⟨φ, hφmem, hφeq.symm⟩)
  exact hproper.isCompact_preimage hc |>.finite hdisc
