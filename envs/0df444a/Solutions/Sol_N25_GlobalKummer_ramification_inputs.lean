-- Prove2me | solution 1 for N25.GlobalKummer.ramification_inputs
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:14.017364+00:00
-- url     : https://prove2.me/submissions/b75b46a0-3830-4e42-8e77-57b13edfb26c

import Definitions.Def_N25_GlobalKummerRamification
import Theorems.Thm_N25_K2Rows_finite_kernel
import Definitions.Def_N25_LocalKummerKernel
import Theorems.Thm_N25_kummer_unramified
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_N25_GlobalKummer_exists_finite_field
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance instL_N25_GlobalKummer_ramification_inputs_23397f_sff16b7 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The literal coefficient representation is finite, smooth, and unramified
outside the two allowed primes. These are the continuous descent inputs. -/
theorem _root_.solution (hPhi : PhiFiveZero) (K2 : K2Rows) :
    FiniteDimensional (ZMod 71) (vRep hPhi) ∧
      (∀ v : vRep hPhi, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧ ∀ s ∈ F.fixingSubgroup, (vRep hPhi).ρ s v = v) ∧
      (∀ q : Nat.Primes, q ∉ ramificationSet →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
          ∀ g ∈ A.inertiaSubgroupIn ℚ, (vRep hPhi).ρ g = 1) := by
  haveI : Finite ↥V := K2.finite_kernel
  haveI : Finite (vRep hPhi) := by change Finite ↥V; infer_instance
  refine ⟨Module.Finite.of_finite, ?_, ?_⟩
  · intro v
    obtain ⟨F, hF, hfix⟩ := exists_finite_field (show ↥V from v).val
    refine ⟨F, hF, ?_⟩
    intro s hs
    apply Subtype.ext
    exact hfix s hs
  · intro q hq A hA g hg
    haveI : Fact (Nat.Prime (q : ℕ)) := ⟨q.property⟩
    have hq5 : (q : ℕ) ≠ 5 := by
      intro h
      have he : q = (⟨5, by decide⟩ : Nat.Primes) := Subtype.ext h
      apply hq
      change q ∈ ({(⟨5, by decide⟩ : Nat.Primes), ⟨71, by decide⟩} : Finset Nat.Primes)
      exact Finset.mem_insert.mpr (Or.inl he)
    have hq71 : (q : ℕ) ≠ 71 := by
      intro h
      have he : q = (⟨71, by decide⟩ : Nat.Primes) := Subtype.ext h
      apply hq
      change q ∈ ({(⟨5, by decide⟩ : Nat.Primes), ⟨71, by decide⟩} : Finset Nat.Primes)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
    apply LinearMap.ext
    intro v
    change ↥V at v
    apply Subtype.ext
    change g • (v : J) = (v : J)
    exact sub_eq_zero.mp (kummer_unramified hPhi 0 (v : J)
      (by intro σ; exact smul_zero (A := J) σ) v.property hq5 hq71 A hA g hg)

end N25.GlobalKummer
