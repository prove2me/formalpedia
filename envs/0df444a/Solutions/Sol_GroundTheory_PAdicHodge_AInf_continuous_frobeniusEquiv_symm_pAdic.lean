-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_pAdic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:53:53.87526+00:00
-- url     : https://prove2.me/submissions/9ad77acb-9670-4193-9538-440bb3414ee8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

open GroundTheory.PAdicHodge.AInf in
theorem solution :
    @Continuous (AInf K p) (AInf K p) (pAdicTopology K p) (pAdicTopology K p) (φ).symm := by
  let I := Ideal.span {(p : AInf K p)}
  change @Continuous _ _ I.adicTopology I.adicTopology ((φ).symm : AInf K p → AInf K p)
  let : TopologicalSpace (AInf K p) := I.adicTopology
  refine continuous_of_continuousAt_zero ((φ).symm : AInf K p →+* AInf K p) ?_
  rw [ContinuousAt, map_zero]
  rw [I.hasBasis_nhds_zero_adic.tendsto_iff I.hasBasis_nhds_zero_adic]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro x hx
  have hI : I.map ((φ).symm : AInf K p →+* AInf K p) = I := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : I ^ n ≤ (I ^ n).comap ((φ).symm : AInf K p →+* AInf K p) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, hI]
  exact hle hx
