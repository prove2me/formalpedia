-- Prove2me | solution 1 for GlobalTheory.linForm_elimination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:03.570557+00:00
-- url     : https://prove2.me/submissions/1855c6c9-e3b5-4583-af90-e64004ce84c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isWeaklyRegular_map_X
import Theorems.Thm_GlobalTheory_isRegular_map_X
import Theorems.Thm_GlobalTheory_linFormEquiv_X_of_notMem
import Theorems.Thm_GlobalTheory_isWeaklyRegular_map_linForm
import Theorems.Thm_GlobalTheory_isRegular_map_linForm
import Theorems.Thm_GlobalTheory_isWeaklyRegular_C_cons_map_linForm
import Theorems.Thm_GlobalTheory_isRegular_C_cons_map_linForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu
namespace GlobalTheory
theorem _root_.solution (S : Set ι) (σ : Type*) :
    (∃ φ : MvPolynomial (ι × J) R ≃ₐ[R] MvPolynomial (ι × J) R,
      (∀ i ∈ S, φ (X (i, j₀)) = ∑ j, C (u j) * X (i, j)) ∧
      ∀ x : ι × J, ¬ (x.1 ∈ S ∧ x.2 = j₀) → φ (X x) = X x) ∧
    (∃ ψ : (MvPolynomial (ι × J) R ⧸ Ideal.span (linForm u '' S)) ≃ₐ[R]
        MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R,
      ∀ x : {x : ι × J // x ∉ elimIndices S j₀}, ψ (Ideal.Quotient.mk _ (X x.1)) = X x) ∧
    (∀ l : List ι, l.Nodup →
      IsWeaklyRegular (MvPolynomial (ι × J) R) (l.map (linForm u)) ∧
      (Nontrivial R →
        RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (l.map (linForm u))) ∧
      ∀ r ∈ nonZeroDivisors R,
        IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)) ∧
        (¬ IsUnit r →
          RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)))) ∧
    (∀ l : List σ, l.Nodup →
      IsWeaklyRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) ∧
      (Nontrivial R →
        RingTheory.Sequence.IsRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)))) :=
  ⟨⟨linFormEquiv u S j₀ hu, fun _ hi => linFormEquiv_X_of_mem u hu hi,
      fun _ hx => linFormEquiv_X_of_notMem u hu hx⟩,
    ⟨quotientSpanLinFormEquiv u hu S, fun x => linFormElim_X_of_notMem u hu x.2⟩,
    fun _ hl => ⟨isWeaklyRegular_map_linForm u hu hl, fun _ => isRegular_map_linForm u hu hl,
      fun _ hr => ⟨isWeaklyRegular_C_cons_map_linForm u hu hr hl,
        fun hr' => isRegular_C_cons_map_linForm u hu hr hr' hl⟩⟩,
    fun _ hl => ⟨isWeaklyRegular_map_X hl, fun _ => isRegular_map_X hl⟩⟩
end GlobalTheory
