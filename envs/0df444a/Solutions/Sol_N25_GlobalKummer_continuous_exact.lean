-- Prove2me | solution 1 for N25.GlobalKummer.continuous_exact
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:39.541801+00:00
-- url     : https://prove2.me/submissions/731d6fc1-c1b6-4a3c-b29a-bbb7ab3a0c2a

import Theorems.Thm_N25_GlobalKummer_kernel_shortExact
import Theorems.Thm_N25_GlobalKummer_kernel_comp_zero
import Definitions.Def_N25_GlobalKummerSequence
import Theorems.Thm_N25_GlobalKummer_ramification_inputs
import Definitions.Def_N25_GlobalKummerRamification
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace N25.GlobalKummer

local instance instL_N25_GlobalKummer_continuous_exact_23397f_s03e72d : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Continuous S-cohomology is exact at the literal selected kernel, with
both maps identified with the maps induced by the frozen K2 arrows. -/
theorem _root_.solution (hPhi : PhiFiveZero) (K2 : K2Rows) :
    ∃ (i : ↥(groupCohomology.continuousH1S ramificationSet psiRep) →ₗ[ZMod 71]
          ↥(groupCohomology.continuousH1S ramificationSet (vRep hPhi)))
      (q : ↥(groupCohomology.continuousH1S ramificationSet (vRep hPhi)) →ₗ[ZMod 71]
          ↥(groupCohomology.continuousH1S ramificationSet cyclotomicRep)),
      (∀ x, (i x : groupCohomology.H1 (vRep hPhi)) =
        (groupCohomology.map (MonoidHom.id Gal) (kernelInclusion hPhi K2) 1).hom (x : groupCohomology.H1 psiRep)) ∧
      (∀ y, (q y : groupCohomology.H1 cyclotomicRep) =
        (groupCohomology.map (MonoidHom.id Gal) (kernelQuotient hPhi K2) 1).hom (y : groupCohomology.H1 (vRep hPhi))) ∧
      Function.Exact i q := by
  obtain ⟨hfin, hsm, hur⟩ := ramification_inputs hPhi K2
  letI := hfin
  letI : FiniteDimensional (ZMod 71) psiRep := by
    change Module.Finite (ZMod 71) (ZMod 71)
    infer_instance
  letI : FiniteDimensional (ZMod 71) cyclotomicRep := by
    change Module.Finite (ZMod 71) (ZMod 71)
    infer_instance
  have hpS : ExtCitation.pPrime 71 ∈ ramificationSet := by
    change (⟨71, by decide⟩ : Nat.Primes) ∈
      ({(⟨5, by decide⟩ : Nat.Primes), ⟨71, by decide⟩} : Finset Nat.Primes)
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  obtain ⟨i₀, q₀, δ₀, i₁, q₁, δ₁, i₂, q₂,
    hi₀, hq₀, hi₁, hq₁, hδ₀, hi₂, hq₂, hδ₁,
    hinj, hex₀, hex₁, hex₂, hex₃, hex₄, hex₅, hex₆⟩ :=
    groupCohomology.exists_les_continuousHS_of_shortExact_of_isLevelConstant
      ramificationSet hpS psiRep (vRep hPhi) cyclotomicRep
      (kernelInclusion hPhi K2) (kernelQuotient hPhi K2)
      (kernel_comp_zero hPhi K2) (kernel_shortExact hPhi K2) hsm hur
  exact ⟨i₁, q₁, hi₁, hq₁, hex₃⟩

end N25.GlobalKummer
