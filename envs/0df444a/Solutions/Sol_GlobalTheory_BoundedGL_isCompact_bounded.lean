-- Prove2me | solution 1 for GlobalTheory.BoundedGL.isCompact_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:32.378388+00:00
-- url     : https://prove2.me/submissions/f90f38fb-87e1-49b4-a91f-d584b0bc7355

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlace
import Theorems.Thm_GlobalTheory_BoundedGL_isCompact_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
noncomputable section
open GlobalTheory GlobalTheory.BoundedGL
variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
namespace GlobalTheory.BoundedGL
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  intro E _ _ w n c
  set K := w.adicCompletion E
  set S : Set (Matrix (Fin n) (Fin n) K) := {A | ∀ i j, Valued.v (A i j) ≤ c} with hS
  have hK : IsCompact S := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_le w c
    have e : S = (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) K)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩
end GlobalTheory.BoundedGL
