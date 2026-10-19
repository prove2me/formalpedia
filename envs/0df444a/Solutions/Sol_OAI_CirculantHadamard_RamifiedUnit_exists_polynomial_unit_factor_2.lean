-- Prove2me | solution 2 for OAI.CirculantHadamard.RamifiedUnit.exists_polynomial_unit_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:33:01.899432+00:00
-- url     : https://prove2.me/submissions/611b5e08-2102-4332-9000-5059b695f363

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedUnit.lean:L28-L57
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.RamifiedUnit.exists_polynomial_unit_factor. The node keeps its source
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein

-- ---- from OAI.LinearAlgebra.CirculantHadamard.RamifiedUnit ----
namespace OAI

universe uR uS

/-!
# The unit factor in a ramified polynomial relation

The exact constant coefficient, together with divisibility of the other
nonleading coefficients, gives a factor with constant coefficient one.
At a root in the maximal ideal this factor is a unit.
-/

noncomputable section

namespace CirculantHadamard.RamifiedUnit

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [IsDomain R]

/-- The polynomial form of the unit factor in an Eisenstein relation. -/
theorem exists_polynomial_unit_factor (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by
  have hdvd : C a ∣ f.eraseLead := by
    apply (C_dvd_iff_dvd_coeff _ _).2
    intro i
    by_cases hi : i = f.natDegree
    · simp [eraseLead_coeff, hi]
    · rw [eraseLead_coeff_of_ne _ hi]
      by_cases hilt : i < f.natDegree
      · exact hcoeff i hilt
      · rw [coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_ne (Nat.le_of_not_gt hilt) (Ne.symm hi))]
        exact dvd_zero a
  obtain ⟨q, hq⟩ := hdvd
  have hqzero : q.coeff 0 = 1 := by
    apply mul_left_cancel₀ ha
    have hh := congrArg (fun g : R[X] => g.coeff 0) hq
    simpa [eraseLead_coeff_of_ne _ (Nat.ne_of_lt hdeg), hzero] using hh.symm
  have hqrepr : 1 + X * q.divX = q := by
    simpa [hqzero, add_comm] using X_mul_divX_add q
  refine ⟨q.divX, ?_⟩
  calc
    f = f.eraseLead + X ^ f.natDegree := by
      simpa [hf] using (eraseLead_add_C_mul_X_pow f).symm
    _ = X ^ f.natDegree + C a * (1 + X * q.divX) := by
      rw [hq, hqrepr]
      exact add_comm _ _

variable [CommRing S] [Algebra R S] [IsLocalRing S]

end CirculantHadamard.RamifiedUnit

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.RamifiedUnit
open Polynomial


theorem solution.{uR} : type_of% @_root_.OAI.CirculantHadamard.RamifiedUnit.exists_polynomial_unit_factor.{uR} := @_root_.OAI.CirculantHadamard.RamifiedUnit.exists_polynomial_unit_factor.{uR}
