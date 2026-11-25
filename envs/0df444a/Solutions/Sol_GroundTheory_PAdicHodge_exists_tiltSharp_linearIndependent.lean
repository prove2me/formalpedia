-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_tiltSharp_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:25.724003+00:00
-- url     : https://prove2.me/submissions/bee3a200-ab58-4e72-82b8-52e81d82c60b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Theorems.Thm_GroundTheory_PAdicHodge_linearIndependent_tiltSharp
import Theorems.Thm_GroundTheory_PAdicHodge_exists_tiltSharp_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ w : ι → C♭, (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧ (∀ i, ‖w i‖ ≤ 1) ∧
      LinearIndependent K♭ w ∧ LinearIndependent K (fun i => tiltSharp C p (w i)) := by
  obtain ⟨w, t, r, ρ, ht0, -, hr0, -, hρ0, hρ1, hp, hli, hspan, horth, hnorm, -⟩ :=
    exists_tiltSharp_family (K := K) (C := C) hv
  exact ⟨w, hspan, fun i => (hnorm i).1, hli,
    linearIndependent_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0 hρ0
      hρ1 hp⟩
end GroundTheory.PAdicHodge
