-- Prove2me | solution 1 for MassDataIdxCore.psi_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:23:54.208565+00:00
-- url     : https://prove2.me/submissions/1c3d1fa8-2f4c-40b5-b457-953f4359b029

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
import Theorems.Thm_MassDataIdxCore_psi_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K) {H : Type} [Group H] (m : H →* GL n T)
  (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)
namespace MassDataIdxCore
theorem _root_.solution (c : O) (h : H) :
    (∀ i j, (((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j ∈ Ideal.span {c}) ↔
      ∀ i j, ∃ w ∈ O, (conjPrime₂ θ P (m h) - 1) i j = (c : K) * w := by
  have key : ∀ i j, ((((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j : K) =
      (conjPrime₂ θ P (m h) - 1) i j := by
    intro i j
    rw [← psi_map O θ J P m hK h]
    simp [Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro H1 i j
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (H1 i j)
    refine ⟨b, b.2, ?_⟩
    rw [← key, ← hb]
    push_cast
    ring
  · intro H1 i j
    obtain ⟨w, hw, hwe⟩ := H1 i j
    refine Ideal.mem_span_singleton'.mpr ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    rw [key]
    rw [hwe]
    push_cast
    ring
end MassDataIdxCore
