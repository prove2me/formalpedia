-- Prove2me | solution 1 for GlobalTheory.CardGLQuot.card_GL_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:38.760808+00:00
-- url     : https://prove2.me/submissions/16911195-08b5-4699-9776-d4b60cfd95e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors
import Theorems.Thm_GlobalTheory_CardGLQuot_card_GL_of_residue
import Theorems.Thm_GlobalTheory_CardGLQuot_isUnit_quot_pow_iff
import Theorems.Thm_GlobalTheory_CardGLQuot_natCard_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.CardGLQuot
namespace GlobalTheory.CardGLQuot
theorem _root_.solution (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥) (n : ℕ) :
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  classical
  let e := IsDedekindDomain.quotientEquivPiFactors h𝔪
  have h1 : Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) = Nat.card (∀ P : (factors 𝔪).toFinset,
      GL (Fin n) (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P)) :=
    Nat.card_congr ((Units.mapEquiv ((e.mapMatrix).trans Matrix.piRingEquiv).toMulEquiv).trans
      MulEquiv.piUnits).toEquiv
  rw [h1, Nat.card_pi, Nat.cast_prod, ← factors_eq_normalizedFactors]
  rw [← Finset.prod_coe_sort (factors 𝔪).toFinset (fun w => (Ideal.absNorm w : ℝ) ^ ((factors 𝔪).count w * n ^ 2) *
    glVol (Ideal.absNorm w : ℝ) n)]
  refine Finset.prod_congr rfl (fun P _ => ?_)
  have hmem : (P : Ideal (𝓞 E)) ∈ factors 𝔪 := Multiset.mem_toFinset.1 P.2
  have hprime : Prime (P : Ideal (𝓞 E)) := prime_of_factor _ hmem
  have hbot : (P : Ideal (𝓞 E)) ≠ ⊥ := hprime.ne_zero
  have hmax : (P : Ideal (𝓞 E)).IsMaximal :=
    ((Ideal.isPrime_of_prime hprime)).isMaximal hbot
  have hc : (factors 𝔪).count (P : Ideal (𝓞 E)) ≠ 0 := (Multiset.count_pos.2 hmem).ne'
  letI : Field (𝓞 E ⧸ (P : Ideal (𝓞 E))) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P) := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_quot, Ne, Ideal.absNorm_eq_zero_iff]
    exact pow_ne_zero _ hbot
  rw [card_GL_of_residue (Ideal.Quotient.factor (Ideal.pow_le_self hc)) (Ideal.Quotient.factor_surjective _)
    (isUnit_quot_pow_iff hmax hc) n, natCard_quot, natCard_quot, map_pow, Nat.cast_pow, ← pow_mul]
end GlobalTheory.CardGLQuot
