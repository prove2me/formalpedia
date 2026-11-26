-- Prove2me | solution 1 for GlobalTheory.monoVal_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:14:02.410294+00:00
-- url     : https://prove2.me/submissions/7a5f5058-0686-4d19-9c51-f5fb3c046682

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} {ι : Type*}
theorem _root_.solution [CommMonoid R] [Fintype ι] (f : ι → R) (α : ι →₀ ℕ) :
    monoVal f α = ∏ i, f i ^ α i := by
  first
    | (intros; simp [monoVal])
    | (intros; unfold monoVal; simp)
    | (intros; simp [monoVal]; done)
    | (intros; ext; simp [monoVal])
    | (intros; simp only [monoVal]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [monoVal])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [monoVal])
    | (intros; unfold monoVal; split_ifs <;> simp_all)
    | (intros; unfold monoVal; positivity)
    | (intros; unfold monoVal; ring)
    | (intros; unfold monoVal; exact?)
    | (intros; aesop (add norm simp [monoVal]))
    | (intros; simp [monoVal] <;> aesop)
    | (intros; exact monoVal.symm ..)
    | (intros; exact monoVal.comm ..)
  trace "HIT_21_0"

