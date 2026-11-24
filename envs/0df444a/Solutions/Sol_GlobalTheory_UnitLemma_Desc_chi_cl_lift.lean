-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.chi_cl_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:51:46.487991+00:00
-- url     : https://prove2.me/submissions/a8733b99-d39c-4a63-b0c3-3da5830c5eb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFramePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartOrthogonalityClasse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {K : UQ} (B : InvAlg K) {ι : Type} (e : ι → B.A) (I : Finset ι)
    (hmul : ∀ x y : B.A, IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y)
    (hnorm : ∀ w : B.A, IsUnit w → chi B e I (w * B.σ w) = 1) :
    ∃ F : B.Cl → ℚ, (∀ k, F k = chi B e I k.rep) ∧
      ∀ x : {x : B.Aˣ // B.σ (x : B.A) = x}, F (Quot.mk _ x) = chi B e I (x.1 : B.A) := by
  refine ⟨Quot.lift (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} => chi B e I (x.1 : B.A)) ?_, ?_, ?_⟩
  · rintro x y ⟨u, hu⟩
    rw [hu, hmul _ _ x.1.isUnit (u.isUnit.mul (u.isUnit.map B.σ)), hnorm _ u.isUnit, mul_one]
  · intro k
    conv_lhs => rw [← Quot.out_eq k]
    rfl
  · intro x; rfl
end GlobalTheory.UnitLemma.Desc
