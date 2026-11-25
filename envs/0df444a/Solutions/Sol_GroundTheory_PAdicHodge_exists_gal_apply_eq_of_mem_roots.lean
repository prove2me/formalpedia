-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_gal_apply_eq_of_mem_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:17.850473+00:00
-- url     : https://prove2.me/submissions/7c0fe8d7-4fb8-4485-b792-b8ac088e2b0c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x a : PadicAlgCl p}
    (ha : a ∈ ((minpoly K x).map (algebraMap K (PadicAlgCl p))).roots) :
    ∃ σ : Gal(PadicAlgCl p/K), σ x = a := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have ha' : aeval a (minpoly K x) = 0 := by
    rw [mem_roots_map (minpoly.ne_zero hx)] at ha
    rwa [aeval_def]
  have he : minpoly K a = minpoly K x :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) ha' (minpoly.monic hx)).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 he
  exact ⟨σ, hσ⟩
end GroundTheory.PAdicHodge
