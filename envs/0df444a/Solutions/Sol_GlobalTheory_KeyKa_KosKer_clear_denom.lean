-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosKer.clear_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:11.402301+00:00
-- url     : https://prove2.me/submissions/b65bd091-80cb-4f4b-91d5-e073b5178624

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulVecCongrDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosKer
open Matrix
namespace GlobalTheory.KeyKa.KosKer
theorem _root_.solution {O Ix : Type} [CommRing O] [IsDomain O] [Fintype Ix] (D : Matrix Ix Ix O)
    (h : ∀ v, (D.map (algebraMap O (FractionRing O))) *ᵥ v = 0 →
      ∃ w, (D.map (algebraMap O (FractionRing O))) *ᵥ w = v) (x : Ix → O) (hx : D *ᵥ x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ u, D *ᵥ u = c • x := by
  have hm : ∀ y : Ix → O, (D.map (algebraMap O (FractionRing O))) *ᵥ (algebraMap O (FractionRing O) ∘ y) =
      algebraMap O (FractionRing O) ∘ (D *ᵥ y) := fun y => funext fun p => (RingHom.map_mulVec _ D y p).symm
  obtain ⟨w, hw⟩ := h (algebraMap O (FractionRing O) ∘ x) (by rw [hm, hx]; ext p; simp)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose u hu using hb
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, u, funext fun p => ?_⟩
  apply IsFractionRing.injective O (FractionRing O)
  have e : algebraMap O (FractionRing O) ∘ u = (b : O) • w := funext hu
  have e2 := congrFun (hm u) p
  rw [e, mulVec_smul, hw] at e2
  simp only [Function.comp, Pi.smul_apply] at e2 ⊢
  rw [← e2, smul_eq_mul, map_mul, Algebra.smul_def]
end GlobalTheory.KeyKa.KosKer
