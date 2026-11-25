-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.not_isChowForm_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:39:46.229925+00:00
-- url     : https://prove2.me/submissions/02457f1a-824d-4b7c-9edf-73e5272edfd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
namespace GlobalTheory.ChowHt.Model
theorem _root_.solution {k : Type} [Field k] {N D δ : ℕ}
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : ¬ IsChowForm (⊤ : Ideal (MvPolynomial (Fin N) k)) D δ f := by
  intro h
  have hz : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f ≠ 0 := by
    intro u hu
    obtain ⟨y, -, hI, -⟩ := (h.zero_iff u).1 hu
    simpa using hI 1 trivial
  apply h.irred.not_isUnit
  rw [← Ideal.span_singleton_eq_top]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  have := hle (Ideal.subset_span rfl)
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at this
  apply hz x
  simpa [MvPolynomial.aeval_map_algebraMap] using this
end GlobalTheory.ChowHt.Model
