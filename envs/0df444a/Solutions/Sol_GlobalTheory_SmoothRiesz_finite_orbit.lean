-- Prove2me | solution 1 for GlobalTheory.SmoothRiesz.finite_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:57.878703+00:00
-- url     : https://prove2.me/submissions/11a8ebbb-248e-4b91-9638-8f0460a16a3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.SmoothRiesz
namespace GlobalTheory.SmoothRiesz
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (hsm : IsSmooth σ)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (y : V) :
    ((fun k : G => σ k y) '' (K : Set G)).Finite := by
  let S : Set G := {g | σ g y = y}
  have hSo : IsOpen S := hsm y
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun g : K => (g : G) • S) (fun g => hSo.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, Set.mem_smul_set.2 ⟨1, by simp [S], by simp⟩⟩)
  refine ((t.finite_toSet.image (fun i : K => σ (i : G) y))).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.1 hki
  refine ⟨i, hi, ?_⟩
  have hs' : σ s y = y := hs
  simp only [smul_eq_mul, map_mul, Module.End.mul_apply, hs']
end GlobalTheory.SmoothRiesz
