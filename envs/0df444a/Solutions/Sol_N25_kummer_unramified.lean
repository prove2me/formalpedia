-- Prove2me | solution 1 for N25.kummer_unramified
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:12.632791+00:00
-- url     : https://prove2.me/submissions/2859802e-b3ff-4b40-9471-c1c51d4289ce

import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option autoImplicit false

noncomputable section

namespace N25

/-- The actual division-point cocycle vanishes on inertia away from 5 and 71.
The reduction argument also applies at 2 and 3. -/
theorem _root_.solution (hPhi : PhiFiveZero)
    (P Q : J) (hP : P ∈ M) (hQ : piEnd Q = P)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : ℓ ≠ 5) (hℓ71 : ℓ ≠ 71)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : σ • Q - Q = 0 := by
  have hℓ25 : ¬ ℓ ∣ 25 := by
    intro h
    have : ℓ ∣ 5 := (Fact.out : Nat.Prime ℓ).dvd_of_dvd_pow (show ℓ ∣ 5 ^ 2 by simpa using h)
    exact hℓ5 ((Nat.dvd_prime (by decide : Nat.Prime 5)).1 this |>.resolve_left (Fact.out : Nat.Prime ℓ).ne_one)
  have hℓ71' : ¬ ℓ ∣ 71 := by
    intro h
    exact hℓ71 ((Nat.dvd_prime (by decide : Nat.Prime 71)).1 h |>.resolve_left (Fact.out : Nat.Prime ℓ).ne_one)
  obtain ⟨htr, hred⟩ :=
    ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
      25 H25 hℓ25 A hA
  have hpi : piEnd (σ • Q - Q) = 0 := by
    rw [map_sub, ← piEnd_galois_comm, hQ, hP σ, sub_self]
  have hkill : 71 • (σ • Q - Q) = 0 := by
    have h := congrArg (fun f : J →+ J => f (σ • Q - Q)) (rhoEnd_comp_piEnd hPhi)
    simpa only [AddMonoidHom.comp_apply, hpi, map_zero, nsmulAddMonoidHom_apply] using h.symm
  have hzred : ModularCurve.reductionQExpModL A (CohCarrier.GammaH 25 H25)
      (σ • Q - Q) = 0 := by
    let red : J →+ _ :=
      ModularCurve.reductionQExpModL A (CohCarrier.GammaH 25 H25)
    change red (σ • Q - Q) = 0
    rw [map_sub red]
    exact sub_eq_zero.mpr
      (ModularCurve.reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
        25 H25 A hred σ hσ Q)
  exact ModularCurve.eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
    25 H25 hℓ25 A hA hred 71 hℓ71' (σ • Q - Q) hkill hzred

end N25
