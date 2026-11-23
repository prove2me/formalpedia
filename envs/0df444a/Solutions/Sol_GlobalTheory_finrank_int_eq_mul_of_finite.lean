-- Prove2me | solution 1 for GlobalTheory.finrank_int_eq_mul_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:28:23.457386+00:00
-- url     : https://prove2.me/submissions/0c616ebe-92a6-4efe-b82e-f8556aef6738

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_finrank_eq
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {O M : Type*} [CommRing O] [IsDomain O] [CharZero O]
    [Module.Free ℤ O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  classical
  let K := FractionRing O
  let N := LocalizedModule O⁰ M
  let f : M →ₗ[O] N := LocalizedModule.mkLinearMap O⁰ M
  let T := Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)
  have hdvd : ∀ s ∈ O⁰, ∃ n : ℤ, n ≠ 0 ∧ s ∣ (n : O) := fun s hs => by
    obtain ⟨r, hr, hd⟩ := IsAlgebraic.exists_nonzero_dvd (R := ℤ)
      (Algebra.IsIntegral.isIntegral (R := ℤ) s).isAlgebraic hs
    exact ⟨r, hr, by simpa using hd⟩
  have hT : ∀ t ∈ T, t ≠ 0 := by
    rintro _ ⟨n, hn, rfl⟩
    simpa using nonZeroDivisors.ne_zero hn
  haveI hTK : IsLocalization T K :=
    { map_units := fun t => IsLocalization.map_units K (M := O⁰)
        ⟨t, mem_nonZeroDivisors_of_ne_zero (hT t t.2)⟩
      surj := fun z => by
        obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj O⁰ z
        obtain ⟨n, hn, t, ht⟩ := hdvd s s.2
        refine ⟨⟨a * t, ⟨(n : O), n, mem_nonZeroDivisors_of_ne_zero hn, by simp⟩⟩, ?_⟩
        simp only [ht, map_mul] at hz ⊢
        rw [← hz]; ring
      exists_of_eq := fun {x y} h => ⟨1, by simpa using IsFractionRing.injective O K h⟩ }
  haveI : IsLocalizedModule T f := by
    rw [isLocalizedModule_iff_isBaseChange T K, ← isLocalizedModule_iff_isBaseChange O⁰ K]
    infer_instance
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars _ f
  have h1 : Module.finrank ℤ N = Module.finrank ℤ M :=
    IsLocalizedModule.finrank_eq _ (f.restrictScalars ℤ) le_rfl
  have h2 : Module.finrank O N = Module.finrank O M := IsLocalizedModule.finrank_eq O⁰ f le_rfl
  have h3 : Module.finrank K N = Module.finrank O N := IsLocalization.finrank_eq K O⁰ le_rfl
  letI : Module ℚ N := Module.compHom N (algebraMap ℚ K)
  haveI : IsScalarTower ℚ K N := ⟨fun q k n => by
    change (q • k) • n = (algebraMap ℚ K q) • (k • n)
    rw [Algebra.smul_def, mul_smul]⟩
  have h4 : Module.finrank ℚ N = Module.finrank ℤ N :=
    IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl
  have h5 : Module.finrank ℚ K * Module.finrank K N = Module.finrank ℚ N :=
    Module.finrank_mul_finrank ℚ K N
  have h6 : Module.finrank ℚ K = Module.finrank ℤ K :=
    IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl
  have h7 : Module.finrank ℤ O * Module.finrank O K = Module.finrank ℤ K := by
    convert Module.finrank_mul_finrank' (R := ℤ) (S := O) K using 2
    all_goals first | rfl | exact Subsingleton.elim _ _
  have h8 : Module.finrank K K = Module.finrank O K := IsLocalization.finrank_eq K O⁰ le_rfl
  rw [Module.finrank_self] at h8
  rw [← h1, ← h4, ← h5, h6, ← h7, ← h8, h3, h2, mul_one]
end _root_.GlobalTheory
end GlobalTheory
