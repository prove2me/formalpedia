-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_multiset_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:13.856794+00:00
-- url     : https://prove2.me/submissions/113b97b7-a9e1-439a-92b7-1735c0b1daab

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_norm_le_one_of_eval_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsAlgClosed C♭] {Q : 𝒪C♭[X]} (hQ : Q.Monic) :
    ∃ s : Multiset 𝒪C♭, Q = (s.map fun b => X - Polynomial.C b).prod := by
  set f := Q.map (algebraMap 𝒪C♭ C♭)
  have hfm : f.Monic := hQ.map _
  have hfc : ∀ n, ‖f.coeff n‖ ≤ 1 := fun n => by
    rw [coeff_map, norm_algebraMap_preTilt]; exact preTilt_norm_le_one _
  have hroot : ∀ r ∈ f.roots, ‖r‖ ≤ 1 := fun r hr =>
    norm_le_one_of_eval_eq_zero hfm hfc (isRoot_of_mem_roots hr)
  classical
  let g : C♭ → 𝒪C♭ := fun r =>
    if h : ‖r‖ ≤ 1 then (norm_le_one_iff_exists_algebraMap.1 h).choose else 0
  have hg : ∀ r ∈ f.roots, algebraMap 𝒪C♭ C♭ (g r) = r := fun r hr => by
    simp only [g, dif_pos (hroot r hr)]
    exact (norm_le_one_iff_exists_algebraMap.1 (hroot r hr)).choose_spec
  have hf : f = (f.roots.map fun r => X - Polynomial.C r).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hfm
  refine ⟨f.roots.map g, map_injective _ (IsFractionRing.injective 𝒪C♭ C♭) ?_⟩
  change f = _
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  conv_lhs => rw [hf]
  congr 1
  refine Multiset.map_congr rfl fun r hr => ?_
  simp [hg r hr]
end GroundTheory.PAdicHodge
