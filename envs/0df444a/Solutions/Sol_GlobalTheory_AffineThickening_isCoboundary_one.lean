-- Prove2me | solution 1 for GlobalTheory.AffineThickening.isCoboundary_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:24.954073+00:00
-- url     : https://prove2.me/submissions/c6c59fa8-543c-4b77-9d19-57547a9f7705

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_add
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_mul
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_add
import Theorems.Thm_GlobalTheory_AffineThickening_isCoboundary_zero
import Theorems.Thm_GlobalTheory_AffineThickening_exists_isCoboundary_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
variable [IsClosedImmersion i] [Surjective i]
  (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U), Lifts i U a 0 → Lifts i U b 0 → a * b = 0)
  {ι : Type*} {f : ι → Γ(Z, ⊤)} {U : ι → Y.Opens} (hU : ∀ j, IsAffineOpen (U j))
  (hD : ∀ j, i ⁻¹ᵁ U j = Z.basicOpen (f j))
  {s : Γ(Z, ⊤)} {σ : ∀ j, Γ(Y, U j)} (hσ : ∀ j, Lifts i (U j) (σ j) s)
include hK hU hD hσ
namespace GlobalTheory.AffineThickening
theorem _root_.solution [Finite ι] (hf : Ideal.span (Set.range f) = ⊤) :
    IsCoboundary i σ 1 := by
  let P : Ideal Γ(Z, ⊤) :=
    { carrier := {r | IsCoboundary i σ r}
      add_mem' := IsCoboundary.add
      zero_mem' := isCoboundary_zero
      smul_mem' := fun c _ h ↦ IsCoboundary.mul hK hU hD c h }
  have : P.radical = ⊤ := by
    rw [eq_top_iff, ← hf, Ideal.span_le]
    rintro _ ⟨m, rfl⟩
    exact exists_isCoboundary_pow hK hU hD hσ m
  rw [Ideal.radical_eq_top, Ideal.eq_top_iff_one] at this
  exact this
end GlobalTheory.AffineThickening
