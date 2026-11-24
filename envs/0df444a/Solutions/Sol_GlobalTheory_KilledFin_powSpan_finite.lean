-- Prove2me | solution 1 for GlobalTheory.KilledFin.powSpan_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:28.456268+00:00
-- url     : https://prove2.me/submissions/73b8a5a3-1bb3-4e8c-9d89-d05287d2ec5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.KilledFin
theorem _root_.solution (t : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) [FiniteDimensional ℂ N] :
    FiniteDimensional ℂ (powSpan t d N) ∧
      Module.finrank ℂ (powSpan t d N) ≤ d * Module.finrank ℂ N := by
  let Φ : (Fin d → N) →ₗ[ℂ] V :=
    ∑ i : Fin d, (t ^ (i : ℕ)) ∘ₗ N.subtype ∘ₗ LinearMap.proj i
  have hle : powSpan t d N ≤ LinearMap.range Φ := by
    rw [powSpan, Submodule.span_le]
    rintro _ ⟨i, hi, n, hn, rfl⟩
    refine ⟨Pi.single ⟨i, hi⟩ ⟨n, hn⟩, ?_⟩
    simp [Φ, LinearMap.sum_apply, Pi.single_apply]
    rw [Finset.sum_eq_single ⟨i, hi⟩ (fun b _ hb => by simp [hb]) (by simp)]
    simp
  haveI : FiniteDimensional ℂ (LinearMap.range Φ) := inferInstance
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc Module.finrank ℂ (powSpan t d N) ≤ Module.finrank ℂ (LinearMap.range Φ) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ (Fin d → N) := LinearMap.finrank_range_le Φ
    _ = d * Module.finrank ℂ N := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
end GlobalTheory.KilledFin
