-- Prove2me | solution 2 for OAI.CirculantHadamard.RamifiedUnit.exists_unit_mul_root_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:35:30.663236+00:00
-- url     : https://prove2.me/submissions/be75e4f0-01f8-4b1e-bd20-2346178f84a5

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedUnit.lean:L61-L87
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.RamifiedUnit.exists_unit_mul_root_pow. The node keeps its source
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
import Theorems.Thm_OAI_CirculantHadamard_RamifiedUnit_exists_polynomial_unit_factor

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

variable [CommRing S] [Algebra R S] [IsLocalRing S]

/-- A root in the maximal ideal turns the normalized polynomial factor into
a unit, and therefore expresses the constant coefficient as a unit times
the ramified power. -/
theorem exists_unit_mul_root_pow (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by
  obtain ⟨q, hq⟩ := exists_polynomial_unit_factor f a ha hf hdeg hzero hcoeff
  have hrel : z ^ f.natDegree + algebraMap R S a * (1 + z * aeval z q) = 0 := by
    rw [hq] at hroot
    simpa only [map_add, map_mul, map_pow, aeval_X, map_one, aeval_C] using hroot
  have hn : -(z * aeval z q) ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.maximalIdeal S).neg_mem
      ((IsLocalRing.maximalIdeal S).mul_mem_right _ hz)
  have hu : IsUnit (1 + z * aeval z q) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(z * aeval z q)) hn
  obtain ⟨v, hv⟩ := hu
  have hpow : z ^ f.natDegree = -(algebraMap R S a * (v : S)) := by
    rw [← hv] at hrel
    exact eq_neg_of_add_eq_zero_left hrel
  refine ⟨-v⁻¹, ?_⟩
  rw [Units.val_neg, hpow, neg_mul_neg]
  calc
    algebraMap R S a = algebraMap R S a * ((v : S) * ↑v⁻¹) := by simp
    _ = ↑v⁻¹ * (algebraMap R S a * (v : S)) := by ac_rfl

end CirculantHadamard.RamifiedUnit

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.RamifiedUnit
open Polynomial


theorem solution.{uR,uS} : type_of% @_root_.OAI.CirculantHadamard.RamifiedUnit.exists_unit_mul_root_pow.{uR,uS} := @_root_.OAI.CirculantHadamard.RamifiedUnit.exists_unit_mul_root_pow.{uR,uS}
