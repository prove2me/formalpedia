-- Prove2me | solution 1 for GlobalTheory.FiniteQuotientComap.finite_quotient_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:24.041545+00:00
-- url     : https://prove2.me/submissions/ee9a74e0-6aa7-4f24-baa9-9c9c1b316b05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteQuotientComap
import Theorems.Thm_GlobalTheory_FiniteQuotientComap_exists_int_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.FiniteQuotientComap
namespace GlobalTheory.FiniteQuotientComap
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L₀ L : Submodule (𝓞 E) (Fin n → E)) (h₀ : L₀.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by

  have : Module.Finite (𝓞 E) L₀ := Module.Finite.iff_fg.mpr h₀
  have : Module.Finite ℤ L₀ := Module.Finite.trans (𝓞 E) L₀
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap L₀.subtype L) q
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem L (y : Fin n → E) (by rw [hL]; exact Submodule.mem_top)
  refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, ?_⟩
  change (m : ℤ) • (Submodule.Quotient.mk y : L₀ ⧸ Submodule.comap L₀.subtype L) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  simpa using hm
end GlobalTheory.FiniteQuotientComap
