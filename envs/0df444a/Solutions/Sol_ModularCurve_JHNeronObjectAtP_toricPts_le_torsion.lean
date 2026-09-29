-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.toricPts_le_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bb49789f-8d4a-5340-ab57-63e80998c7b7

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_torsion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

namespace ToricTorsion

open WithConv

theorem convPow_eq_one {S B G : Type} [CommRing S] [CommRing B] [Algebra S B] [AddCommGroup G] (m : ℕ)
    (hG : ∀ g : G, m • g = 0) (χ : WithConv (AddMonoidAlgebra S G →ₐ[S] B)) : χ ^ m = 1 := by

  have key : ∀ (n : ℕ) (g : G), (χ ^ n) (AddMonoidAlgebra.single g 1) = (χ (AddMonoidAlgebra.single g 1)) ^ n := by
    intro n g
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]
    | succ n ih =>
      rw [pow_succ, pow_succ, AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
        TensorProduct.map_tmul]
      simp only [AddMonoidAlgebra.lsingle_apply]
      rw [Algebra.TensorProduct.lift_tmul, ih]
  apply WithConv.ext
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  show (χ ^ m) (AddMonoidAlgebra.single g 1) = (1 : WithConv (AddMonoidAlgebra S G →ₐ[S] B)) (AddMonoidAlgebra.single g 1)
  rw [key, AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one, ← map_pow,
    AddMonoidAlgebra.single_pow, one_pow, hG, ← AddMonoidAlgebra.one_def, map_one]

end ToricTorsion

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    O.toricPts m ≤ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m := by
  by_cases hm : 0 < m
  swap
  ·
    unfold JHNeronObjectAtP.toricPts
    rw [dif_neg hm]
    exact bot_le
  obtain ⟨hmul, -, hiff, -⟩ :=
    ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM A hA Λ O m hm
  intro x hx
  obtain ⟨χ, rfl⟩ := (hiff x).mp hx

  let F : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) → JH M H :=
    fun ψ => O.toricPoint m hm ψ.ofConv
  have hF1 : F 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h

    have h' : F 1 + 0 = F 1 + F 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hFpow : ∀ (n : ℕ) (ψ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)),
      F (ψ ^ n) = n • F ψ := by
    intro n ψ
    induction n with
    | zero => rw [pow_zero, zero_nsmul]; exact hF1
    | succ n ih => rw [pow_succ, succ_nsmul, show F (ψ ^ n * ψ) = F (ψ ^ n) + F ψ from hmul _ _, ih]
  have hexp : (WithConv.toConv χ) ^ m = 1 :=
    ToricTorsion.convPow_eq_one m (fun g => by
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]) (WithConv.toConv χ)
  rw [Pic0.mem_torsion, natCast_zsmul]
  have := hFpow m (WithConv.toConv χ)
  rw [hexp, hF1] at this
  exact this.symm

end S_ModularCurve_JHNeronObjectAtP_toricPts_le_torsion
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_torsion (solution)
