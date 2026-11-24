-- Prove2me | solution 1 for MvPolynomial.geomFundamentalGroup_hom_zmod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-24T05:01:32.355317+00:00
-- url     : https://prove2.me/submissions/eb046bcd-fce1-4145-8322-26a58ba4e8d7

import Mathlib
import Definitions.Def_RPLib_FX_EtPi1_01

set_option autoImplicit false

namespace EtPi1Sol

open RamanujanPetersson

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

end EtPi1Sol

open RamanujanPetersson CurveCoh EtPi1 in
theorem solution
    (F : Type) [Field F] [Finite F] (n : ℕ) (K : Type) [Field K]
    [Algebra (MvPolynomial (Fin n) F) K] [IsFractionRing (MvPolynomial (Fin n) F) K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (KU : IntermediateField K (AlgebraicClosure K))
    (hKU : KU = ⨆ L : {L : IntermediateField K (AlgebraicClosure K) //
        FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure (MvPolynomial (Fin n) F) L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
          (∀ b : integralClosure (MvPolynomial (Fin n) F) L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1}, L.1)
    (G : Subgroup (KU ≃ₐ[K] KU))
    (hG : ∀ σ : KU ≃ₐ[K] KU, σ ∈ G ↔ ∀ x : KU, (∃ m : ℕ, 0 < m ∧ x ^ p ^ m = x) → σ x = x)
    (N : ℕ) [NeZero N] (hpN : Nat.Coprime p N)
    (c : G → ZMod N) (hc : IsLocallyConstant c) (hadd : ∀ g h : G, c (g * h) = c g + c h) :
    c = 0 := by
  let _ : Algebra F K := ((algebraMap (MvPolynomial (Fin n) F) K).comp MvPolynomial.C).toAlgebra
  have : IsScalarTower F (MvPolynomial (Fin n) F) K := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  have hset : unramSet (MvPolynomial (Fin n) F) K = {L : IntermediateField K (AlgebraicClosure K) |
      FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure (MvPolynomial (Fin n) F) L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
          (∀ b : integralClosure (MvPolynomial (Fin n) F) L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (EtPi1Sol.unram_iff _ K L))
  have hKU' : KU = maxUnram (MvPolynomial (Fin n) F) K := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have hG' : G = pi1geo (MvPolynomial (Fin n) F) K (p ^ 1) := by
    ext σ
    rw [hG, mem_pi1geo]
    simp only [IsConst, pow_one]
  subst hG'
  exact hom_eq_zero (F := F) (n := n) (K := K) (e := 1) one_pos hpN c hc hadd
