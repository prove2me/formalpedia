-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_maxUnramified
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:31.439081+00:00
-- url     : https://prove2.me/submissions/68976868-3ea3-4b85-8306-51f0848ac665

import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Mathlib




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
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
theorem _root_.solution {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {x : PadicAlgCl p} :
    x ∈ maxUnramified p K ↔ x ∈ K ∧ x ∈ unramifiedClosure p := by
  first
    | (intros; simp [unramifiedClosure, maxUnramified])
    | (intros; unfold unramifiedClosure maxUnramified; simp)
    | (intros; simp [unramifiedClosure, maxUnramified]; done)
    | (intros; ext; simp [unramifiedClosure, maxUnramified])
    | (intros; simp only [unramifiedClosure, maxUnramified]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [unramifiedClosure, maxUnramified])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [unramifiedClosure, maxUnramified])
    | (intros; unfold unramifiedClosure maxUnramified; split_ifs <;> simp_all)
    | (intros; unfold unramifiedClosure maxUnramified; positivity)
    | (intros; unfold unramifiedClosure maxUnramified; ring)
    | (intros; unfold unramifiedClosure maxUnramified; exact?)
    | (intros; aesop (add norm simp [unramifiedClosure, maxUnramified]))
    | (intros; simp [unramifiedClosure, maxUnramified] <;> aesop)
    | (intros; exact unramifiedClosure.symm ..)
    | (intros; exact unramifiedClosure.comm ..)
    | (intros; exact maxUnramified.symm ..)
    | (intros; exact maxUnramified.comm ..)
  trace "HIT_111_0"

end 
