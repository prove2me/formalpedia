-- Prove2me | solution 1 for GlobalTheory.polyChartHom_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:18.271883+00:00
-- url     : https://prove2.me/submissions/e59dfede-759a-4d39-af0e-6647ece4130f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PolyChartSmoothFractionLift
import Theorems.Thm_GlobalTheory_polyChartHom_C
import Theorems.Thm_GlobalTheory_polyChartHom_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)
namespace GlobalTheory
theorem _root_.solution :
    (polyChartHom V R₀).range = Algebra.adjoin K
      ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪
        Set.range fun v : V =>
          algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v)) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change polyChartHom V R₀ p ∈ _
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [polyChartHom_C]
      exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul, polyChartHom_X]
      exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨v, rfl⟩))
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨C ⟨a, ha⟩, polyChartHom_C V R₀ ⟨a, ha⟩⟩
    · exact ⟨X v, polyChartHom_X V R₀ v⟩
end GlobalTheory
