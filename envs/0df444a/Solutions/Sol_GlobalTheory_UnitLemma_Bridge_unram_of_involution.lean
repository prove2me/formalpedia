-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.unram_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:44.606805+00:00
-- url     : https://prove2.me/submissions/b0ce45b8-8693-43cf-a849-041df0706d5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_finrank_fixedField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge
namespace GlobalTheory.UnitLemma.Bridge
theorem _root_.solution {E : Type} [nE : NontriviallyNormedField E] [CharZero E] [IsUltrametricDist E]
    [LocallyCompactSpace E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (hne : ∃ y, c y ≠ y)
    (hn : ∀ y, ‖c y‖ = ‖y‖) (hu : ∀ y : E, ∃ x, c x = x ∧ ‖y‖ = ‖x‖) :
    ∃ (F : Type) (_ : NontriviallyNormedField F) (_ : NormedAlgebra F E) (st : StarRing E),
      GlobalTheory.JR.Unram F E ∧ ∀ y, st.star y = c y := by
  letI nF : NontriviallyNormedField (fixedField c) :=
    { (inferInstance : NormedField (fixedField c)) with
      non_trivial := by
        obtain ⟨y, hy⟩ := NontriviallyNormedField.non_trivial (α := E)
        obtain ⟨x, hx, hxy⟩ := hu y
        exact ⟨⟨x, hx⟩, by change 1 < ‖x‖; rwa [← hxy]⟩ }
  letI nA : NormedAlgebra (fixedField c) E :=
    { (inferInstance : Algebra (fixedField c) E) with
      norm_smul_le := fun a y => norm_mul_le (a : E) y }
  letI st : StarRing E :=
    { star := c
      star_involutive := hc
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add c a b }
  have hcont : Continuous c := (AddMonoidHomClass.isometry_of_norm c hn).continuous
  have hcl : IsClosed (fixedField c : Set E) := isClosed_eq hcont continuous_id
  refine ⟨fixedField c, nF, nA, st, ?_, fun _ => rfl⟩
  exact
    { charZero := inferInstance
      ultraF := inferInstance
      ultraE := inferInstance
      lcF := hcl.locallyCompactSpace
      lcE := inferInstance
      finrank_eq := finrank_fixedField c hc hne
      star_fix := fun x => x.2
      star_ne := hne
      norm_star := hn
      unram := fun y => by
        obtain ⟨x, hx, hxy⟩ := hu y
        exact ⟨⟨x, hx⟩, hxy⟩ }
end GlobalTheory.UnitLemma.Bridge
