-- Prove2me | solution 2 for OAI.CirculantHadamard.integer_prime_pow_dvd_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:23:00.966542+00:00
-- url     : https://prove2.me/submissions/a01f8bb3-8092-4a8e-a16a-7c731a486b3b

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/IntegerLocalDivisibility.lean:L20-L41
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.integer_prime_pow_dvd_of_localization. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection

-- ---- from OAI.LinearAlgebra.CirculantHadamard.IntegerLocalDivisibility ----
namespace OAI

universe uA

/-!
# Reflecting prime-power divisibility from the localized integers

A denominator inverted in the localization at `(p)` is not divisible by `p`.
Clearing that denominator and using primality therefore reflects divisibility
by every power of `p` back to the integers. The argument includes the zeroth
power and the zero numerator, without any nonzero numerator hypothesis.
-/

namespace CirculantHadamard

/-- Divisibility by a rational prime power in its actual integer localization
implies the same divisibility in the integers. -/
theorem integer_prime_pow_dvd_of_localization
    {A : Type uA} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) (hx : (p : A) ^ t ∣ algebraMap ℤ A x) :
    (p : ℤ) ^ t ∣ x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl y
  have hinj : Function.Injective (algebraMap ℤ A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  have hclear : x * (s : ℤ) = (p : ℤ) ^ t * a := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_natCast, hy, mul_assoc, hs]
  have hsprime : ¬ (p : ℤ) ∣ (s : ℤ) := by
    intro hdiv
    have hmem : (s : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
      Ideal.mem_span_singleton.mpr hdiv
    exact s.property (hP.symm ▸ hmem)
  exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right t hsprime
    ⟨a, hclear⟩

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard


theorem solution.{uA} : type_of% @_root_.OAI.CirculantHadamard.integer_prime_pow_dvd_of_localization.{uA} := @_root_.OAI.CirculantHadamard.integer_prime_pow_dvd_of_localization.{uA}
