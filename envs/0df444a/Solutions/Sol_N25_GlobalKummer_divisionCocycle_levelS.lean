-- Prove2me | solution 1 for N25.GlobalKummer.divisionCocycle_levelS
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:14.623586+00:00
-- url     : https://prove2.me/submissions/c55fbdc0-eec1-4ddd-a65b-0dfbefac1240

import Theorems.Thm_N25_GlobalKummer_ramification_inputs
import Definitions.Def_N25_GlobalKummerRamification
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
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance instL_N25_GlobalKummer_divisionCocycle_levelS_23397f_s60b155 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The actual division cocycle factors through a finite extension unramified
outside 5 and 71. The finite extension is obtained from its triangular action. -/
theorem _root_.solution (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.IsLevelConstantS₁ ramificationSet (divisionCocycle hPhi P Q hQ) := by
  classical
  let A := vRep hPhi
  let c := divisionCocycle hPhi P Q hQ
  let E := cocycleExtensionRep A c
  obtain ⟨hfin, hsm, hur⟩ := ramification_inputs hPhi K2
  letI : Module.Finite (ZMod 71) A := hfin
  letI : Module.Finite (ZMod 71) E := by
    change Module.Finite (ZMod 71) (A × ZMod 71)
    infer_instance
  have hesm : ∀ x : E, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ ∀ s ∈ F.fixingSubgroup, E.ρ s x = x := by
    intro x
    change A × ZMod 71 at x
    obtain ⟨F, hF, hfirst⟩ := hsm x.1
    obtain ⟨L, hL, hpoint⟩ := exists_finite_field Q
    letI := hF
    letI := hL
    refine ⟨F ⊔ L, F.finiteDimensional_sup L, ?_⟩
    intro s hs
    have hsF := IntermediateField.fixingSubgroup_antitone le_sup_left hs
    have hsL := IntermediateField.fixingSubgroup_antitone le_sup_right hs
    have hc0 : c s = 0 := by
      apply Subtype.ext
      change s • Q - Q = 0
      rw [hpoint s hsL, sub_self]
    change (A.ρ s x.1 + x.2 • c s, x.2) = x
    rw [hc0, smul_zero, add_zero, hfirst s hsF]
  have heur : ∀ q : Nat.Primes, q ∉ ramificationSet →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime (q : ℕ) →
        ∀ g ∈ B.inertiaSubgroupIn ℚ, E.ρ g = 1 := by
    intro q hq B hB g hg
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
    have hc0 : c g = 0 := by
      apply Subtype.ext
      exact kummer_unramified hPhi (P : J) Q P.property hQ hq5 hq71 B hB g hg
    apply LinearMap.ext
    intro x
    change A × ZMod 71 at x
    change (A.ρ g x.1 + x.2 • c g, x.2) = x
    rw [hur q hq B hB g hg, hc0, smul_zero, add_zero]
    rfl
  obtain ⟨F, hF, hfix⟩ :=
    groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
      ramificationSet E hesm heur
  refine ⟨F, hF, ?_⟩
  intro g s hs
  have hc0 : c s = 0 := by
    have he := congrArg (fun f : Module.End (ZMod 71) E =>
      (show A × ZMod 71 from f (0, 1)).1) (hfix s hs)
    change A.ρ s 0 + (1 : ZMod 71) • c s = 0 at he
    simpa using he
  change c (g * s) = c g
  have hc : c (g * s) = A.ρ g (c s) + c g :=
    (groupCohomology.mem_cocycles₁_iff _).mp c.property g s
  rw [hc, hc0, map_zero, zero_add]

end N25.GlobalKummer
