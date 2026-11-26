-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_placesOver
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:33.542191+00:00
-- url     : https://prove2.me/submissions/e7cdf602-4a2c-4458-bc91-1ddaef091761

import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F : Type*} [Field F]
variable {L : Type*} [Field L] [Algebra F L]
theorem _root_.solution {S : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver S ↔ ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal := by
  first
    | (intros; simp [placesOver])
    | (intros; unfold placesOver; simp)
    | (intros; simp [placesOver]; done)
    | (intros; ext; simp [placesOver])
    | (intros; simp only [placesOver]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [placesOver])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [placesOver])
    | (intros; unfold placesOver; split_ifs <;> simp_all)
    | (intros; unfold placesOver; positivity)
    | (intros; unfold placesOver; ring)
    | (intros; unfold placesOver; exact?)
    | (intros; aesop (add norm simp [placesOver]))
    | (intros; simp [placesOver] <;> aesop)
    | (intros; exact placesOver.symm ..)
    | (intros; exact placesOver.comm ..)
  trace "HIT_182_0"

