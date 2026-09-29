-- Prove2me | solution 1 for ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/75a2df98-3387-589a-a3b9-8fed7b5c5b1e

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinKernelKillsCuspidalClass_heckeModuleBar

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (hT : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → heckeOperatorBar p ℓ (cuspidalClass p) = (1 + ℓ : ℤ) • cuspidalClass p) (hU : heckeOperatorBar p ⟨p, Fact.out⟩ (cuspidalClass p) = cuspidalClass p) : EisensteinKernelKillsCuspidalClass p (heckeModuleBar p) := by
  have hp : p.Prime := Fact.out
  letI := heckeModuleBar p

  have hgen : ∀ ℓ : Nat.Primes,
      heckeGen ℓ • cuspidalClass p = (eisensteinSystem p ℓ) • cuspidalClass p := by
    intro ℓ
    rw [heckeModuleBar_heckeGen_smul hcomm]
    by_cases hℓ : (ℓ : ℕ) = p
    · have hdvd : (ℓ : ℕ) ∣ p := hℓ ▸ dvd_rfl
      have : ℓ = ⟨p, hp⟩ := Subtype.ext hℓ
      rw [eisensteinSystem_of_dvd hdvd, one_smul, this, hU]
    · have hndvd : ¬ (ℓ : ℕ) ∣ p := fun h =>
        hℓ (((Nat.dvd_prime hp).mp h).resolve_left ℓ.2.ne_one)
      rw [eisensteinSystem_of_not_dvd hndvd, hT ℓ hℓ]

  have hall : ∀ t : HeckeAlg,
      t • cuspidalClass p = (MvPolynomial.aeval (eisensteinSystem p) t : ℤ) • cuspidalClass p := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
        rw [heckeModuleBar_C_smul, MvPolynomial.aeval_C]
        rfl
    | add f g hf hg => rw [add_smul, hf, hg, map_add, add_zsmul]
    | mul_X f ℓ hf =>

        have hsc : f • (eisensteinSystem p ℓ • cuspidalClass p) = eisensteinSystem p ℓ • (f • cuspidalClass p) :=
          (smulAddHom HeckeAlg (JZero p) f).map_zsmul (eisensteinSystem p ℓ) (cuspidalClass p)
        rw [mul_smul, show (MvPolynomial.X ℓ : HeckeAlg) = heckeGen ℓ from rfl, hgen ℓ, hsc, hf, smul_smul,
          map_mul]
        congr 1
        rw [show heckeGen ℓ = (MvPolynomial.X ℓ : HeckeAlg) from rfl, MvPolynomial.aeval_X, mul_comm]

  have hI : ∀ i ∈ eisensteinIdeal p, i • cuspidalClass p = 0 := by
    intro i hi
    rw [hall i, show MvPolynomial.aeval (eisensteinSystem p) i = 0 from hi, zero_zsmul]

  intro t ht
  obtain ⟨i, hi, hti⟩ := ht
  have h := hti (cuspidalClass p)
  have e1 : ((1 + i) * t) • cuspidalClass p = t • cuspidalClass p + t • (i • cuspidalClass p) := by
    rw [add_mul, one_mul, add_smul, mul_comm i t, mul_smul]
  rw [e1, hI i hi, (smul_zero t : t • (0 : JZero p) = 0), add_zero] at h
  exact h

end S_ModularCurve_eisensteinKernelKillsCuspidalClass_heckeModuleBar
end P2MW
export P2MW.S_ModularCurve_eisensteinKernelKillsCuspidalClass_heckeModuleBar (solution)
