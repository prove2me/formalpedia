-- Prove2me | solution 1 for GlobalTheory.UnitLemma.rho_pow_eq_card_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:03:02.377832+00:00
-- url     : https://prove2.me/submissions/47aff501-3532-4112-bbca-b970340fa902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteAlgebraInvolutionRhoPowEqCardBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  intro K B a r φ c hφ hker hint k
  have hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  unfold InvAlg.rho
  rw [hK]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h1 : Nat.card {q : B.T ⧸ φ.ker //
      IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} =
      Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)} := by
    apply Nat.card_congr
    refine (e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_
    intro q
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]
    exact hint _ k
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]
    omega
  exact h2
end GlobalTheory.UnitLemma
