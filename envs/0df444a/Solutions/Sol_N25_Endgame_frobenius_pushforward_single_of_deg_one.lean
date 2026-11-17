-- Prove2me | solution 1 for N25.Endgame.frobenius_pushforward_single_of_deg_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:20.087835+00:00
-- url     : https://prove2.me/submissions/5a0f7846-2c2c-479f-887c-3b7de4fab156

import Definitions.Def_N25_Endgame

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25.Endgame

theorem _root_.solution
    (K : Type*) [Field K] [PerfectField K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (P : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ))
    (hP : P.deg = 1) (n : ℤ) :
    ModularCurve.qExpFrobeniusDivPushforwardModL K Γ ℓ
        (Finsupp.single P n) =
      Finsupp.single
        (ModularCurve.qExpFrobeniusPlaceModL K Γ ℓ P) n := by
  have h := ModularCurve.degree_qExpFrobeniusDivPushforwardModL K Γ ℓ
    (Finsupp.single P 1)
  rw [ModularCurve.qExpFrobeniusDivPushforwardModL_single,
    AlgebraicCurve.Divisor.degree_single, AlgebraicCurve.Divisor.degree_single,
    hP] at h
  have hprod :
      P.inertiaDegAlong (ModularCurve.qExpFrobeniusModL K Γ ℓ)
          (ModularCurve.qExpFrobeniusModL_isIntegral K Γ ℓ) *
        (ModularCurve.qExpFrobeniusPlaceModL K Γ ℓ P).deg = 1 := by
    exact_mod_cast (show
      (P.inertiaDegAlong (ModularCurve.qExpFrobeniusModL K Γ ℓ)
          (ModularCurve.qExpFrobeniusModL_isIntegral K Γ ℓ) : ℤ) *
        ((ModularCurve.qExpFrobeniusPlaceModL K Γ ℓ P).deg : ℤ) = 1 by
      simpa using h)
  have hinertia :
      P.inertiaDegAlong (ModularCurve.qExpFrobeniusModL K Γ ℓ)
        (ModularCurve.qExpFrobeniusModL_isIntegral K Γ ℓ) = 1 :=
    Nat.eq_one_of_dvd_one ⟨_, hprod.symm⟩
  rw [ModularCurve.qExpFrobeniusDivPushforwardModL_single, hinertia, Nat.cast_one, mul_one]

end N25.Endgame
