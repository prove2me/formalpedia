-- Prove2me | solution 1 for MilnorDynamics.disc_cover_proper_local_is_covering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:26:34.79464+00:00
-- url     : https://prove2.me/submissions/7755de46-5ed7-438a-894e-aacafe35d855

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- Proof of `MilnorDynamics.disc_cover_proper_local_is_covering`, variant 6.
--
-- Two defects caused the CE verdicts on variants 1-5.
--
-- (a) `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` has signature
--       (hf : IsClosedMap f) (hs : forall x in s, (f ⁻¹' {x}).Finite)
--       (h : IsLocalHomeomorphOn f (f ⁻¹' s)) : IsCoveringMapOn f s
--     with `s` an *implicit* variable. Passing `(s := (Set.univ : Set {0, 1}ᶜ))`
--     left the ascription `{0, 1}ᶜ` to be elaborated against a metavariable sort
--     `?m`, which is why the remote reported `Singleton ?m`, `Insert ?m` and
--     `Compl (Type ?u)` failures at that line. Here `Set.univ` is passed
--     *positionally*, after which the codomain type `Ersorg...` `{0, 1}ᶜ` is
--     already known from the goal, so no metavariable is created.
--
-- (b) `IsCompact.toFinite` does not exist at this revision. The correct route is
--     the one Mathlib itself uses at Mathlib/Topology/Covering/Basic.lean:581:
--     turn the fibre into an `IsDiscrete` set with `IsDiscrete.of_openPartialHomeomorph`
--     (which needs only injectivity on the open partial homeomorph's source), then
--     apply `IsCompact.finite`, which is `(hs : IsCompact s) (hs' : IsDiscrete s) : s.Finite`.
--
-- Math used:
--   IsProperMap.isClosedMap                 Mathlib/Topology/Maps/Proper/Basic.lean:92
--   IsProperMap.isCompact_preimage          Mathlib/Topology/Maps/Proper/Basic.lean:210
--   IsLocalHomeomorph.isLocalHomeomorphOn   Mathlib/Topology/IsLocalHomeomorph.lean:178
--   IsDiscrete.of_openPartialHomeomorph    Mathlib/Topology/Covering/Basic.lean:499
--   IsCompact.finite                        Mathlib/Topology/Compactness/Compact.lean:1060
--   isCoveringMap_iff_isCoveringMapOn_univ  Mathlib/Topology/Covering/Basic.lean:294

-- Defect (c), reported by the remote verdict on v6 itself. v6 applied
-- `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` and then read a field
-- `.isCoveringMap` off the resulting `IsCoveringMapOn`. There is no such field: the
-- `IsCoveringMapOn` namespace (Mathlib/Topology/Covering/Basic.lean:300-304) has only
-- `isCoveringMap_restrictPreimage`, `of_isCoveringMap_restrictPreimage` and
-- `of_isCoveringMap_subtype`; `isCoveringMap` belongs to `IsCoveringMap`. The remote
-- reported exactly this at line 52:
--   Invalid field `isCoveringMap`: The environment does not contain
--   `Function.isCoveringMap`, so it is not possible to project the field
--   `isCoveringMap` from an expression ... of type
--   `∀ x ∈ ?m.146, IsEvenlyCovered ... x`
-- The residual metavariable `?m.146` in that type shows `s` was still undetermined:
-- the goal had not yet been reduced to `IsCoveringMapOn g Set.univ`.
--
-- Fix: `rw [isCoveringMap_iff_isCoveringMapOn_univ]` on the goal FIRST, so the goal
-- reads `IsCoveringMapOn (hp.restrict ...) Set.univ`. `s` is then fixed to `Set.univ`
-- by the goal before the lemma is applied, no metavariable survives, and no field
-- projection is needed: the lemma's conclusion is already the goal.
--
-- Defect (d), reported by the remote verdict on the `rw` version. That version wrote
-- the fibre obligation as `(fun x _ => ?_)` and then also ran `intro x`. The lambda
-- already binds `x` and the membership proof, so the `intro x` had nothing left to
-- introduce:
--   line 73: Tactic `introN` failed: There are no additional binders or `let` bindings
--   in the goal to introduce
--   ...
--   x : ↑{0, 1}ᶜ
--   x✝ : x ∈ univ
--   ⊢ (MapsTo.restrict ... ⁻¹' {x}).Finite
-- The displayed goal is precisely the obligation we want, with `x` already in context,
-- so the fix is to drop the redundant `intro x`.
--
-- Defect (e), reported by the remote verdict on the version that dropped the `intro`.
-- Two things, both from over-eager ascription:
--   line 86: failed to synthesize `Singleton ?m.176`, `Insert ?m.171`, `Compl (Type ?u.104)`
--   line 89: Application type mismatch: the argument `φ` has type
--     `OpenPartialHomeomorph ↑(Metric.ball 0 1) ↑{0, 1}ᶜ` of sort `Type` but is expected
--     to have type `e ∈ φ.source` of sort `Prop`;
--     Insufficient number of fields for `⟨…⟩`: Constructor `Eq.refl` does not have
--     explicit fields, but 2 were provided
--
-- (e1) The `have hc : IsCompact ({x} : Set {0, 1}ᶜ)` line reintroduced defect (a) at a
-- new site: `{0, 1}ᶜ` was again ascribed against a metavariable sort, because `x`'s type
-- is only known as a metavariable `↑?s` at that point. The ascription is unnecessary:
-- `isCompact_singleton` infers its own type, and `hproper.isCompact_preimage` fixes the
-- set. So the `have` is stated with no ascription at all.
--
-- (e2) `(hlocal e).imp ...` is wrong twice over. `IsLocalHomeomorph` is
-- `fun x => ∃ e, x ∈ e.source ∧ f = e` (Mathlib/Topology/IsLocalHomeomorph.lean:165), so
-- `.imp` rewrites inside the `Exists` and the supplied function is offered the whole
-- conjunction, not the point. Matching that, `⟨φ, …⟩` tried to rebuild the `Exists` from
-- the point `φ` and failed. The fix is to destructure explicitly with `rcases`.
--
--     (`T2Space` propagates to subtypes, Mathlib/Topology/Separation/Hausdorff.lean:358,
--     and `ℂ` is `T2Space` by Mathlib/Analysis/Complex/Basic.lean:128.)
--
-- The shape of the call follows Mathlib's own use of this lemma at
-- Mathlib/Analysis/Complex/CoveringMap.lean:56: `s` is left to be determined by the
-- goal, so no explicit set term is elaborated in a position where its subtype is
-- still a metavariable.
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
