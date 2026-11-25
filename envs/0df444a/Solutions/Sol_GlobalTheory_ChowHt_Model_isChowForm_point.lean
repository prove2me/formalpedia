-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.isChowForm_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:43:13.550792+00:00
-- url     : https://prove2.me/submissions/29388fb0-da7e-4679-8f7b-9a6dea361023

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
theorem _root_.solution (k : Type) [Field k] :
    IsChowForm (Ideal.span {(X 1 : MvPolynomial (Fin 2) k)}) 0 1 (X (0, 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs b
    rw [support_X, Finset.mem_singleton] at hs
    subst hs
    fin_cases b
    simp [Fin.sum_univ_two, Finsupp.single_apply]
  · rw [map_X]; exact X_prime.irreducible
  · intro u
    rw [aeval_X]
    constructor
    · intro h
      refine ⟨![1, 0], by simp, ?_, ?_⟩
      · intro g hg
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
        simp
      · intro i
        fin_cases i
        simpa [Fin.sum_univ_two] using h
    · rintro ⟨y, hy, hI, hu⟩
      have h1 : y 1 = 0 := by simpa using hI (X 1) (Ideal.subset_span rfl)
      have h0 : y 0 ≠ 0 := by
        intro h0; apply hy; funext j; fin_cases j <;> simp [h0, h1]
      have := hu 0
      simp [Fin.sum_univ_two, h1, h0] at this
      exact this
end GlobalTheory.ChowHt.Model
