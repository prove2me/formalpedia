-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:19.106205+00:00
-- url     : https://prove2.me/submissions/a5d3e703-10bf-4346-9896-c6f87c0492bf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_repr_ofF
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_ofF_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_ofF_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_exists_algebraMap_of_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_sigma_ne_id
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_sigma_hE_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧
    (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧
    ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F),
      (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) =
        (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ
          (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) →
      ∀ (β : F) (x : Fin M × Fin d → F),
        gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔
          (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  refine ⟨ofF_bijective b, ?_, ?_⟩
  · intro x
    rw [not_iff_not]
    constructor
    · intro h
      exact (ofF_bijective b).1 (h.trans (ofF_zero b).symm)
    · rintro rfl
      exact ofF_zero b
  · intro B hB β x
    obtain ⟨c, hc⟩ := exists_algebraMap_of_fixed hσ.2.2.1 (sigma_ne_id hσ)
      (sigma_hE_self hσ hJ (ofF b x 0))
    have hco : (fun p : Fin M × Fin d => b.repr (ofF b x 0 p.1) p.2) = x := by
      funext p
      exact repr_ofF b x 0 p.1 p.2
    have htr := hB (ofF b x 0)
    rw [hco, hc, Algebra.trace_algebraMap, hσ.2.2.1] at htr
    have hgram : gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ c = β := by
      constructor
      · intro h
        have h0 := congrFun (congrFun h 0) 0
        have h1 : hE σ J (ofF b x 0) (ofF b x 0) = algebraMap F E β := h0
        rw [hc] at h1
        exact (algebraMap F E).injective h1
      · rintro rfl
        funext u v
        obtain rfl : u = 0 := Subsingleton.elim _ _
        obtain rfl : v = 0 := Subsingleton.elim _ _
        exact hc
    rw [hgram, ← htr, nsmul_eq_mul]
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have e : (1 / 2 : F) * (((2 : ℕ) : F) * c) = c := by
      push_cast
      field_simp
    rw [e]
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
