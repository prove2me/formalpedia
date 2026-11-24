-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.exists_basis_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:58.573572+00:00
-- url     : https://prove2.me/submissions/01a1ad94-87d6-48f9-9272-566e12657717

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [FiniteDimensional K.E V]
    (h : V → V → K.E) (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) {n : ℕ} (hn : Module.finrank K.E V = n)
    (v : Fin n → V) (hv : ∀ i j, h (v i) (v j) = if i = j then 1 else 0) :
    ∃ b : Module.Basis (Fin n) K.E V, ∀ i, b i = v i := by
  let ℓ : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z, map_smul' := fun a y => hsmul a y z }
  have li : LinearIndependent K.E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (ℓ (v i)) hg
    rw [map_sum, map_zero] at h1
    simp only [map_smul, smul_eq_mul] at h1
    change ∑ j, g j * h (v j) (v i) = 0 at h1
    simpa [hv] using h1
  have sp : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    exact (Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card li, Fintype.card_fin, hn])).ge
  exact ⟨Module.Basis.mk li sp, fun i => Module.Basis.mk_apply li sp i⟩
end GlobalTheory.InertUnitOrb.ModelOfN
