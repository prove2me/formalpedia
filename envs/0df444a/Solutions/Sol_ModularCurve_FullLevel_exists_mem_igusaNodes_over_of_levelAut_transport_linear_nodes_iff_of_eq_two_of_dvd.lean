-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3a3e9832-d9d6-5be1-af82-3410cf2535f5

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_isSeparable
import Theorems.Thm_ModularCurve_exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

p2m_open "ModularCurve~coeffMap_qExpand"

namespace IgusaNodesE121

section CoeffMap

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qTwist (φ : R →+* S) (u : Rˣ) (y : LaurentSeries R) :
    coeffMap φ (qTwist u y) = qTwist (Units.map (φ : R →* S) u) (coeffMap φ y) := by
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul]
  congr 1
  rw [← map_zpow (Units.map (φ : R →* S)) u k, Units.coe_map, MonoidHom.coe_coe]

theorem coeffMap_qExpand (φ : R →+* S) (N : ℕ) [NeZero N] (y : LaurentSeries R) :
    coeffMap φ (qExpand R N y) = qExpand S N (coeffMap φ y) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem qTwist_ne_zero {u : Rˣ} {y : LaurentSeries R} (hy : y ≠ 0) : qTwist u y ≠ 0 := by
  intro h
  apply hy
  have hs := support_qTwist u y
  rw [h, HahnSeries.support_zero] at hs
  exact HahnSeries.support_eq_empty_iff.mp hs.symm

theorem qExpand_ne_zero {N : ℕ} [NeZero N] {y : LaurentSeries R} (hy : y ≠ 0) : qExpand R N y ≠ 0 :=
  fun h => hy (qExpand_injective (R := R) (N := N) (h.trans (map_zero _).symm))

end CoeffMap

section Presentation

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem presentation_qTwist (uA : (↥A)ˣ) {f : LaurentSeries L} {x y : LaurentSeries ↥A}
    (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (h : f * coeffMap A.subtype y = coeffMap A.subtype x) :
    coeffMap (IsLocalRing.residue ↥A) (qTwist uA y) ≠ 0 ∧
      qTwist (Units.map (A.subtype : ↥A →* L) uA) f * coeffMap A.subtype (qTwist uA y) =
        coeffMap A.subtype (qTwist uA x) := by
  refine ⟨?_, ?_⟩
  · rw [coeffMap_qTwist]
    exact qTwist_ne_zero hy
  · rw [coeffMap_qTwist, coeffMap_qTwist, ← map_mul, h]

theorem presentation_qExpand (N : ℕ) [NeZero N] {f : LaurentSeries L} {x y : LaurentSeries ↥A}
    (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (h : f * coeffMap A.subtype y = coeffMap A.subtype x) :
    coeffMap (IsLocalRing.residue ↥A) (qExpand (↥A) N y) ≠ 0 ∧
      qExpand L N f * coeffMap A.subtype (qExpand (↥A) N y) = coeffMap A.subtype (qExpand (↥A) N x) := by
  refine ⟨?_, ?_⟩
  · rw [coeffMap_qExpand]
    exact qExpand_ne_zero hy
  · rw [coeffMap_qExpand, coeffMap_qExpand, ← map_mul, h]

theorem presentation_of_qTwist (uA : (↥A)ˣ) {g : LaurentSeries L} {x y : LaurentSeries ↥A}
    (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (h : qTwist (Units.map (A.subtype : ↥A →* L) uA) g * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ x' y' : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y' ≠ 0 ∧
      g * coeffMap A.subtype y' = coeffMap A.subtype x' := by
  obtain ⟨hy', h'⟩ := presentation_qTwist A uA⁻¹ hy h
  refine ⟨qTwist uA⁻¹ x, qTwist uA⁻¹ y, hy', ?_⟩
  rw [qTwist_qTwist, ← map_mul, inv_mul_cancel, map_one, qTwist_one_apply] at h'
  exact h'

end Presentation

end IgusaNodesE121

set_option autoImplicit false

open IsLocalRing

namespace IgusaNodesE121

section Dominate

variable {κ K₀ K : Type*} [Field κ] [Field K₀] [Field K] [Algebra κ K₀] [Algebra κ K]

theorem exists_valuationSubring_restrict_eq (j : K₀ →ₐ[κ] K) (s : AlgebraicCurve.Place κ K₀) :
    ∃ B : ValuationSubring K, (∀ a : κ, algebraMap κ K a ∈ B) ∧ B ≠ ⊤ ∧
      ∀ g : K₀, g ∈ s.toValuationSubring ↔ j g ∈ B := by

  let f : s.toValuationSubring →+* K := j.toRingHom.comp s.toValuationSubring.subtype
  have hf : ∀ x : s.toValuationSubring, f x = j (x : K₀) := fun _ => rfl
  have hfinj : Function.Injective f := j.toRingHom.injective.comp Subtype.val_injective
  let L : LocalSubring K := LocalSubring.range f
  obtain ⟨B, hB⟩ := L.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hB
  have hmem : ∀ g : K₀, g ∈ s.toValuationSubring → j g ∈ B := by
    intro g hg
    exact hle ⟨⟨g, hg⟩, rfl⟩
  have hiff : ∀ g : K₀, g ∈ s.toValuationSubring ↔ j g ∈ B := by
    intro g
    refine ⟨hmem g, fun hgB => ?_⟩
    by_contra hg

    have hg0 : g ≠ 0 := by rintro rfl; exact hg (zero_mem _)
    have hginv : g⁻¹ ∈ s.toValuationSubring :=
      (s.toValuationSubring.mem_or_inv_mem g).resolve_left hg
    have hnu : ¬ IsUnit (⟨g⁻¹, hginv⟩ : s.toValuationSubring) := by
      intro hu
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have hv' : g⁻¹ * (v : K₀) = 1 := by
        have := congrArg Subtype.val hv
        simpa using this
      have hvg : (v : K₀) = g := by
        rw [← inv_inv g]
        exact (inv_eq_of_mul_eq_one_right hv').symm
      exact hg (hvg ▸ v.2)

    have hnuL : ¬ IsUnit (⟨f ⟨g⁻¹, hginv⟩, ⟨_, rfl⟩⟩ : L.toSubring) := by
      intro hu
      apply hnu

      obtain ⟨v, hv⟩ := hu.exists_left_inv
      obtain ⟨w, hw⟩ := v.2
      refine isUnit_iff_exists_inv'.mpr ⟨w, ?_⟩
      apply hfinj
      rw [map_mul, map_one, hw]
      exact congrArg Subtype.val hv
    have hnuB : ¬ IsUnit (Subring.inclusion hle ⟨f ⟨g⁻¹, hginv⟩, ⟨_, rfl⟩⟩) :=
      fun hu => hnuL ((isUnit_map_iff (Subring.inclusion hle) _).mp hu)

    apply hnuB
    refine isUnit_iff_exists_inv.mpr ⟨⟨j g, hgB⟩, Subtype.ext ?_⟩
    show j (g⁻¹) * j g = 1
    rw [← map_mul, inv_mul_cancel₀ hg0, map_one]
  refine ⟨B, fun a => ?_, ?_, hiff⟩
  · rw [← j.commutes a]
    exact hmem _ (s.algebraMap_mem' a)
  · intro hB
    obtain ⟨g, hg⟩ : ∃ g : K₀, g ∉ s.toValuationSubring := by
      by_contra h
      push Not at h
      exact s.ne_top' (eq_top_iff.mpr fun g _ => h g)
    exact hg ((hiff g).mpr (hB.symm ▸ ValuationSubring.mem_top _))

theorem exists_place_restrict_eq [PerfectField κ] (j : K₀ →ₐ[κ] K)
    (hfg : ∃ x : K, Transcendental κ x ∧ FiniteDimensional (IntermediateField.adjoin κ ({x} : Set K)) K)
    (s : AlgebraicCurve.Place κ K₀) :
    ∃ P : AlgebraicCurve.Place κ K, ∀ g : K₀, g ∈ s.toValuationSubring ↔ j g ∈ P.toValuationSubring := by
  obtain ⟨B, hκ, hB, hiff⟩ := exists_valuationSubring_restrict_eq j s
  obtain ⟨x, hx, hfd⟩ := hfg
  obtain ⟨t, -, hfd', hsep⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField hx hfd
  haveI := hfd'
  haveI := hsep
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_isSeparable t B hκ hB
  exact ⟨v, fun g => by rw [hv]; exact hiff g⟩

theorem exists_place_qExpFunctionFieldC_restrict_eq [PerfectField κ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (j : K₀ →ₐ[κ] ModularCurve.qExpFunctionFieldC κ Γ)
    (htr : ∃ t : ModularCurve.qExpFunctionFieldC κ Γ, Transcendental κ t)
    (s : AlgebraicCurve.Place κ K₀) :
    ∃ P : AlgebraicCurve.Place κ (ModularCurve.qExpFunctionFieldC κ Γ),
      ∀ g : K₀, g ∈ s.toValuationSubring ↔ j g ∈ P.toValuationSubring := by

  have hjmem : ModularCurve.jqModC κ ∈ ModularCurve.qExpFunctionFieldC κ Γ :=
    ModularCurve.intFormRatiosC_subset κ Γ (ModularCurve.jqModC_mem_intFormRatiosC κ Γ)
  obtain ⟨hfd, -⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    κ Γ hT Γ le_rfl (fun γ hγ => Or.inl hγ) ⟨_, hjmem⟩ rfl
  obtain ⟨t, ht⟩ := htr
  haveI := hfd
  have hfdt := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental
    (⟨_, hjmem⟩ : ModularCurve.qExpFunctionFieldC κ Γ) ht
  exact exists_place_restrict_eq j ⟨t, ht, hfdt⟩ s

end Dominate

end IgusaNodesE121

set_option autoImplicit false

p2m_open "ModularCurve~coeffMap_qExpand"

namespace IgusaNodesE133

section Phi

variable (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] (N : ℕ) [NeZero N]

theorem qExpand_prime_jqModC : qExpand K q (jqModC K) = jqModC K ^ q :=
  frobenius_identity_geom_unconditional K

theorem qExpand_sq_jqModC : qExpand K (q ^ 2) (jqModC K) = jqModC K ^ (q ^ 2) := by
  rw [qExpand_congr (pow_two q), ← qExpand_qExpand, qExpand_prime_jqModC, map_pow, qExpand_prime_jqModC,
    ← pow_mul, ← pow_two]

theorem qExpand_sq_jqNModC : qExpand K (q ^ 2) (jqNModC K N) = jqNModC K N ^ (q ^ 2) := by
  unfold jqNModC
  rw [qExpand_qExpand, qExpand_congr (mul_comm (q ^ 2) N), ← qExpand_qExpand, qExpand_sq_jqModC, map_pow]

theorem qExpand_sq_mem {g : LaurentSeries K} (hg : g ∈ modularFunctionFieldC K N) :
    qExpand K (q ^ 2) g ∈ modularFunctionFieldC K N := by
  have hj : jqModC K ∈ modularFunctionFieldC K N := jqModC_mem K N
  have hjN : jqNModC K N ∈ modularFunctionFieldC K N := jqNModC_mem K N
  have h : modularFunctionFieldC K N ≤ (modularFunctionFieldC K N).comap (qExpandAlgC K (q ^ 2)) := by
    conv_lhs => unfold modularFunctionFieldC
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    change qExpandAlgC K (q ^ 2) x ∈ modularFunctionFieldC K N
    rw [qExpandAlgC_apply]
    rcases Set.mem_insert_iff.mp hx with h1 | h2
    · rw [h1, qExpand_sq_jqModC]
      exact pow_mem hj _
    · rw [Set.mem_singleton_iff.mp h2, qExpand_sq_jqNModC]
      exact pow_mem hjN _
  exact h hg

noncomputable def Phi : ↥(modularFunctionFieldC K N) →ₐ[K] ↥(modularFunctionFieldC K N) where
  toFun g := ⟨qExpand K (q ^ 2) (g : LaurentSeries K), qExpand_sq_mem K q N g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by
    show qExpand K (q ^ 2) (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
    exact (qExpandAlgC K (q ^ 2)).commutes r)

@[scoped simp] theorem coe_Phi (g : ↥(modularFunctionFieldC K N)) :
    ((Phi K q N g : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = qExpand K (q ^ 2) (g : LaurentSeries K) := rfl

end Phi

section Ext

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem eq_coe_of_apply_generators (ψ : ↥(modularFunctionFieldC K N) →+* LaurentSeries K)
    (h1 : ∀ c : K, ψ (algebraMap K ↥(modularFunctionFieldC K N) c) = algebraMap K (LaurentSeries K) c)
    (h2 : ψ (jGeomGen K N) = jqModC K) (h3 : ψ (jNGeomGen K N) = jqNModC K N)
    (e : ↥(modularFunctionFieldC K N)) : ψ e = (e : LaurentSeries K) := by
  let φ₁ : ↥(modularFunctionFieldC K N) →ₐ[K] LaurentSeries K := { toRingHom := ψ, commutes' := h1 }
  have key : φ₁ = (modularFunctionFieldC K N).val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K (S := modularFunctionFieldC K N)
      (s := {jqModC K, jqNModC K N}) rfl (fun x hx => ?_)
    rcases hx with rfl | hx
    · exact h2
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h3
  exact congrArg (fun φ : ↥(modularFunctionFieldC K N) →ₐ[K] LaurentSeries K => φ e) key

end Ext

end IgusaNodesE133
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd.IgusaNodesE133"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~coeffMap_qExpand ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace IgusaNodesE133

set_option synthInstance.maxHeartbeats 1600000 in

noncomputable local instance instAlgebraResidueFieldXHE133 {L : Type*} [Field L] (A : ValuationSubring L)
    (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Algebra (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) M H) :=
  inferInstance

section Aux

theorem mem_valuationSubring_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L) {z : L} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) : z ∈ A := by
  by_contra h
  have hinv : z⁻¹ ∈ A := (A.mem_or_inv_mem z).resolve_left h

  have hnu : ¬ IsUnit (⟨z⁻¹, hinv⟩ : A) := by
    intro hu
    apply h
    obtain ⟨u, hu⟩ := hu
    have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = z := by
      have h2 : ((u : ↥A) : L) * ((u⁻¹ : (↥A)ˣ) : ↥A) = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
      rw [hu] at h2
      have h3 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) = (z⁻¹)⁻¹ := (eq_inv_of_mul_eq_one_right h2)
      rw [h3, inv_inv]
    rw [← h1]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  have hmem : (⟨z⁻¹, hinv⟩ : A) ∈ maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hpow : (⟨z⁻¹, hinv⟩ : A) ^ n ∈ maximalIdeal ↥A :=
    Ideal.pow_mem_of_mem _ hmem n (Nat.pos_of_ne_zero hn)
  have hone : (⟨z⁻¹, hinv⟩ : A) ^ n = 1 := Subtype.ext (by
    show (z⁻¹) ^ n = 1
    rw [inv_pow, hz, inv_one])
  rw [hone] at hpow
  exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top (maximalIdeal.isMaximal ↥A)) hpow

theorem residue_eq_one_of_pow_prime_eq_one {L : Type*} [Field L] (A : ValuationSubring L) (q : ℕ) [Fact q.Prime]
    [CharP (ResidueField ↥A) q] (z : ↥A) (hz : (z : L) ^ q = 1) : IsLocalRing.residue ↥A z = 1 := by
  have hz' : z ^ q = 1 := Subtype.ext (by exact_mod_cast hz)
  have h : (IsLocalRing.residue ↥A z) ^ q = 1 := by rw [← map_pow, hz', map_one]
  have h2 : (IsLocalRing.residue ↥A z - 1) ^ q = 0 := by
    rw [sub_pow_char, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : q.Prime).ne_zero |>.mp h2)

theorem finiteDimensional_adjoin_transport {K L : Type*} [Field K] [Field L] [Algebra K L]
    (S S' : IntermediateField K L) (e : S = S') (x : L) (h : x ∈ S)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({(⟨x, h⟩ : ↥S)} : Set ↥S)) ↥S) :
    FiniteDimensional ↥(IntermediateField.adjoin K ({(⟨x, e ▸ h⟩ : ↥S')} : Set ↥S')) ↥S' := by
  subst e
  exact hfd

end Aux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd.IgusaNodesE133"

section TwistData

theorem exists_unit_idx (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) q] (ζ : Idx q) :
    ∃ uA : (↥A)ˣ, ((Units.map (A.subtype : ↥A →* AlgebraicClosure ℚ) uA : (AlgebraicClosure ℚ)ˣ) :
        AlgebraicClosure ℚ) = ζ.val ∧
      ∀ k : ℤ, Units.map (IsLocalRing.residue ↥A : ↥A →* ResidueField ↥A) (uA ^ k) = 1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hprim : IsPrimitiveRoot ζ.val q :=
    isPrimitiveRoot_of_mem_primitiveRoots (show ↥(primitiveRoots q (AlgebraicClosure ℚ)) from ζ).2
  have hζq : ζ.val ^ q = 1 := hprim.pow_eq_one
  have hζ0 : ζ.val ≠ 0 := hprim.ne_zero hq0
  have hζA : ζ.val ∈ A := mem_valuationSubring_of_pow_eq_one A hq0 hζq
  have hζA' : ζ.val⁻¹ ∈ A := mem_valuationSubring_of_pow_eq_one A hq0 (by rw [inv_pow, hζq, inv_one])
  have hmul1 : (⟨ζ.val, hζA⟩ : ↥A) * ⟨ζ.val⁻¹, hζA'⟩ = 1 := by
    apply Subtype.ext
    show ζ.val * ζ.val⁻¹ = 1
    exact mul_inv_cancel₀ hζ0
  refine ⟨Units.mkOfMulEqOne _ _ hmul1, ?_, fun k => ?_⟩
  · rw [Units.coe_map, Units.val_mkOfMulEqOne]
    rfl
  · rw [map_zpow]
    convert one_zpow k
    ext
    rw [Units.coe_map, Units.val_mkOfMulEqOne]
    exact residue_eq_one_of_pow_prime_eq_one A q ⟨ζ.val, hζA⟩ hζq

end TwistData
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd.IgusaNodesE133"

section ExpandData

theorem exists_transcendental_finiteDimensional_modularFunctionFieldC (K : Type*) [Field K] (q : ℕ) [Fact q.Prime]
    [CharP K q] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) :
    ∃ x : ↥(modularFunctionFieldC K N), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N) := by
  have hjm : jqModC K ∈ qExpFunctionFieldC K (Gamma0 N) := intFormRatiosC_subset _ _ (jqModC_mem_intFormRatiosC _ _)
  have hT : ModularGroup.T ∈ Gamma0 N := CohCarrier.GammaH_le_Gamma0 (M := N) ⊤ (translation_mem_GammaH N ⊤)
  obtain ⟨hfd, -⟩ := finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
    (Gamma0 N) hT (Gamma0 N) le_rfl (fun γ hγ => Or.inl hγ) ⟨_, hjm⟩ rfl
  refine ⟨⟨jqModC K, jqModC_mem K N⟩, fun halg => ?_, ?_⟩
  · exact transcendental_jqModC K (by simpa using halg.algebraMap (A := LaurentSeries K))
  · exact finiteDimensional_adjoin_transport _ _ (qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd K N q hqN) _ hjm hfd

end ExpandData
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd.IgusaNodesE133"

section Branches

set_option synthInstance.maxHeartbeats 1600000

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M']
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
  (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
  (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
  (hO : ∀ f : ↥(fieldBar q M'), f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥A,
      coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧ (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
  (red : ↥R.integers →+* LaurentSeries (ResidueField ↥A))
  (hredpres : ∀ (f : ↥R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
      ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
      red f * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x)
  (θ : ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) →+* LaurentSeries (ResidueField ↥A))
  (hθ : ∀ f : ↥R.integers, θ (R.residue f) = red f)
  (j : ↥(modularFunctionFieldC (ResidueField A) M') →+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
  (hj : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩))
  (hfO : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers → IntermediateField.inclusion hle f ∈ R.integers)
  (τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M'))

include hle R₀ R hO red hredpres θ hθ j hj hfO τ

omit [Fact q.Prime] in

theorem twist_compat (v : (↥A)ˣ) (hv : Units.map (IsLocalRing.residue ↥A : ↥A →* ResidueField ↥A) v = 1)
    (hτ : ∀ f : ↥(modularFunctionFieldBar M'),
      ((τ (IntermediateField.inclusion hle f) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        qTwist (Units.map (A.subtype : ↥A →* AlgebraicClosure ℚ) v) (f : LaurentSeries (AlgebraicClosure ℚ)))
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers) :
    ∃ hC : τ (IntermediateField.inclusion hle f) ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩) := by
  obtain ⟨x, y, hy, hxy⟩ := (hO _).mp (hfO f hf)

  have hxyf : (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
    rw [← IntermediateField.coe_inclusion hle f]; exact hxy
  obtain ⟨hy', hxy'⟩ := IgusaNodesE121.presentation_qTwist A v hy hxyf
  have hC : τ (IntermediateField.inclusion hle f) ∈ R.integers := (hO _).mpr ⟨_, _, hy', by rw [hτ]; exact hxy'⟩
  refine ⟨hC, ?_⟩
  obtain ⟨hC0, hjc⟩ := hj f hf
  rw [← hjc]
  apply θ.injective
  rw [hθ, hθ]
  have e1 := hredpres ⟨_, hC⟩ _ _ hy' (by rw [hτ]; exact hxy')
  have e2 := hredpres ⟨_, hC0⟩ x y hy hxy
  rw [IgusaNodesE121.coeffMap_qTwist, IgusaNodesE121.coeffMap_qTwist, hv, qTwist_one_apply,
    qTwist_one_apply, ← e2] at e1
  exact mul_right_cancel₀ hy e1

theorem expand_compat [CharP (ResidueField ↥A) q]
    (hθj : ∀ e : ↥(modularFunctionFieldC (ResidueField ↥A) M'), θ (j e) = (e : LaurentSeries (ResidueField ↥A)))
    (hτ : ∀ f : ↥(modularFunctionFieldBar M'),
      ((τ (IntermediateField.inclusion hle f) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) (q ^ 2) (f : LaurentSeries (AlgebraicClosure ℚ)))
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers) :
    ∃ hC : τ (IntermediateField.inclusion hle f) ∈ R.integers,
      R.residue ⟨_, hC⟩ = (j.comp (Phi (ResidueField ↥A) q M').toRingHom) (R₀.residue ⟨f, hf⟩) := by
  obtain ⟨x, y, hy, hxy⟩ := (hO _).mp (hfO f hf)
  have hxyf : (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
    rw [← IntermediateField.coe_inclusion hle f]; exact hxy
  obtain ⟨hy', hxy'⟩ := IgusaNodesE121.presentation_qExpand A (q ^ 2) hy hxyf
  have hC : τ (IntermediateField.inclusion hle f) ∈ R.integers := (hO _).mpr ⟨_, _, hy', by rw [hτ]; exact hxy'⟩
  refine ⟨hC, ?_⟩
  obtain ⟨hC0, hjc⟩ := hj f hf
  apply θ.injective
  rw [hθ, RingHom.comp_apply, hθj]
  show red ⟨_, hC⟩ = qExpand (ResidueField ↥A) (q ^ 2)
    ((R₀.residue ⟨f, hf⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A))
  rw [← hθj, ← hjc, hθ]
  have e1 := hredpres ⟨_, hC⟩ _ _ hy' (by rw [hτ]; exact hxy')
  have e2 := hredpres ⟨_, hC0⟩ x y hy hxy
  rw [IgusaNodesE121.coeffMap_qExpand, IgusaNodesE121.coeffMap_qExpand, ← e2, map_mul] at e1
  exact mul_right_cancel₀ (IgusaNodesE121.qExpand_ne_zero hy) e1

omit hle R₀ R hO red hredpres θ hθ j hj hfO τ in

theorem expand_places [CharP (ResidueField ↥A) q] [PerfectField (ResidueField ↥A)] (hqM' : ¬ q ∣ M')
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hrat : ∀ s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'), s.IsRational)
    (s : ↥W) :
    ∃ s' : ↥W, ∀ g' : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
      g' ∈ (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring ↔
        Phi (ResidueField ↥A) q M' g' ∈ (s' : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring := by
  have hfdE₀ := exists_transcendental_finiteDimensional_modularFunctionFieldC (ResidueField ↥A) q M' hqM'
  obtain ⟨s', hs'⟩ := IgusaNodesE121.exists_place_restrict_eq (Phi (ResidueField ↥A) q M') hfdE₀
    (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'))
  have hmem : s' ∈ W := by
    rw [hW]
    exact isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand q M' (ResidueField ↥A) 2
      (Phi (ResidueField ↥A) q M').toRingHom (fun g' => rfl) s s' hs' (hrat _) ((hW s).mp s.2)
  exact ⟨⟨s', hmem⟩, hs'⟩

end Branches
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd.IgusaNodesE133"

end IgusaNodesE133
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd.IgusaNodesE133"

section Main

open IgusaNodesE133

set_option synthInstance.maxHeartbeats 1600000 in

noncomputable local instance instAlgebraResidueFieldXHMain {L : Type*} [Field L] (A : ValuationSubring L)
    (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Algebra (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) M H) :=
  inferInstance

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 9600000 in
set_option linter.unusedVariables false in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))
    (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))) (hNcard : NIg.card = W.card)
    (hN : ∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring)
    (g : CuspidalType.ProjLine q → ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')))
    (hg : ∀ ℓ, g ℓ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ} ∧
      ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧ g ℓ = levelAutBar q M' ζ γ) :
    ∃ xs : CuspidalType.ProjLine q → ↥W → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      (∀ ℓ s, xs ℓ s ∈ NIg) ∧
      (∀ ℓ, ∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : g ℓ (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        (∀ (s : ↥W) (g' : modularFunctionFieldC (ResidueField A) M'),
          g' ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g' ∈ (xs ℓ s).toValuationSubring) ∧

        (∀ c : ResidueField A, j (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) M') c) =
          algebraMap (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) c) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g' : modularFunctionFieldC (ResidueField A) M',
          g' ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g' ∈ Q.toValuationSubring) := by
  classical

  haveI hAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hperf : PerfectField (ResidueField ↥A) := inferInstance
  haveI hchar : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  haveI hcurve : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    isCurveOver_modularFunctionFieldC_of_isSeparable_jqNModC _ M' (isSeparable_jqNModC_of_good _ M' q hqM')
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI hfi : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (q ^ 2 * M') (levelH q M'))
  obtain ⟨j, hj, hNIg⟩ := hN

  have hO : ∀ f : ↥(fieldBar q M'), f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥A,
      coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧ (f : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x := by
    intro f; rw [hR]; exact hIg_inf f
  obtain ⟨red, hred0, hredpres⟩ :=
    exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring A (fieldBar q M') R.integers hO
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) →+* LaurentSeries (ResidueField ↥A),
      ∀ f : ↥R.integers, θ (R.residue f) = red f := by
    have hker : RingHom.ker R.residue ≤ RingHom.ker red := by
      intro f hf
      rw [R.ker_residue] at hf
      rw [RingHom.mem_ker, hred0, ValuationSubring.coe_mem_nonunits_iff]
      exact hf
    let e := RingHom.quotientKerEquivOfSurjective R.residue_surjective
    let ψ := Ideal.Quotient.lift (RingHom.ker R.residue) red (fun a ha => (RingHom.mem_ker).mp (hker ha))
    refine ⟨ψ.comp e.symm.toRingHom, fun f => ?_⟩
    have he : e.symm (R.residue f) = Ideal.Quotient.mk (RingHom.ker R.residue) f := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      exact (RingHom.quotientKerEquivOfSurjective_apply_mk R.residue_surjective f).symm
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, Ideal.Quotient.lift_mk]

  have hrat : ∀ s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'), s.IsRational := by
    intro s
    haveI : Module.Finite (ResidueField ↥A) s.ResidueField := IsCurveOver.finiteResidue s
    haveI : Algebra.IsIntegral (ResidueField ↥A) s.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField ↥A) (K := s.ResidueField)).surjective

  have hjalg : ∀ c : ResidueField ↥A, j (algebraMap (ResidueField ↥A) _ c) =
      algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← R₀.residue_algebraMap a, ← R.residue_algebraMap a]
    obtain ⟨hC, hjc⟩ := hj (algebraMap ℚ̄ ↥(modularFunctionFieldBar M') (a : ℚ̄))
      ((R₀.algebraMap_mem_iff (a : ℚ̄)).mpr a.2)
    rw [← hjc]
    have hincl : (IntermediateField.inclusion hle) (algebraMap ℚ̄ ↥(modularFunctionFieldBar M') (a : ℚ̄)) =
        algebraMap ℚ̄ ↥(fieldBar q M') (a : ℚ̄) := (IntermediateField.inclusion hle).commutes (a : ℚ̄)
    exact congrArg R.residue (Subtype.ext hincl)
  let jA : ↥(modularFunctionFieldC (ResidueField ↥A) M') →ₐ[ResidueField ↥A]
      ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) := { toRingHom := j, commutes' := hjalg }

  have hredC : ∀ (a : ↥A) (hC : algebraMap ℚ̄ ↥(fieldBar q M') (a : ℚ̄) ∈ R.integers),
      red ⟨_, hC⟩ = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (IsLocalRing.residue ↥A a) := by
    intro a hC
    have := hredpres ⟨_, hC⟩ (HahnSeries.single 0 a) 1 (by rw [map_one]; exact one_ne_zero) (by
      rw [map_one, mul_one, coeffMap_single]
      show ((algebraMap ℚ̄ ↥(fieldBar q M') (a : ℚ̄) : ↥(fieldBar q M')) : LaurentSeries ℚ̄) = HahnSeries.single 0 (A.subtype a)
      exact algebraMap_laurentSeries_eq_single _ (a : ℚ̄))
    rw [map_one, mul_one, coeffMap_single] at this
    rw [this, algebraMap_laurentSeries_eq_single _ (IsLocalRing.residue ↥A a)]

  have hjmemF₀ : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    have : coeffMap A.subtype (jqModC ↥A) = coeffEmb ℚ̄ jq :=
      (map_jqModC A.subtype).trans (map_jqModC (algebraMap ℚ ℚ̄)).symm
    rw [this]
    exact coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full M' (jq_mem M'))
  have hjNmemF₀ : coeffMap A.subtype (jqNModC ↥A M') ∈ modularFunctionFieldBar M' := by
    have : coeffMap A.subtype (jqNModC ↥A M') = coeffEmb ℚ̄ (qExpand ℚ M' jq) := by
      show coeffMap A.subtype (qExpand ↥A M' (jqModC ↥A)) = coeffMap (algebraMap ℚ ℚ̄) (qExpand ℚ M' jq)
      rw [IgusaNodesE121.coeffMap_qExpand, IgusaNodesE121.coeffMap_qExpand]
      exact congrArg _ ((map_jqModC A.subtype).trans (map_jqModC (algebraMap ℚ ℚ̄)).symm)
    rw [this]
    exact coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full M' (jqN_mem M'))
  have hθj : ∀ e : ↥(modularFunctionFieldC (ResidueField ↥A) M'), θ (j e) = (e : LaurentSeries (ResidueField ↥A)) := by
    refine eq_coe_of_apply_generators (ResidueField ↥A) M' (θ.comp j) (fun c => ?_) ?_ ?_
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      rw [RingHom.comp_apply, hjalg, ← R.residue_algebraMap a, hθ]
      exact hredC a _
    · obtain ⟨h0, hres⟩ := hR₀ (jqModC ↥A) hjmemF₀
      have eJ : R₀.residue ⟨_, h0⟩ = jGeomGen (ResidueField ↥A) M' :=
        Subtype.ext (hres.trans (map_jqModC (IsLocalRing.residue ↥A)))
      obtain ⟨hC, hjc⟩ := hj _ h0
      rw [← eJ, RingHom.comp_apply, ← hjc, hθ]
      have := hredpres ⟨_, hC⟩ (jqModC ↥A) 1 (by rw [map_one]; exact one_ne_zero)
        (by rw [map_one, mul_one, IntermediateField.coe_inclusion])
      rw [map_one, mul_one] at this
      exact this.trans (map_jqModC (IsLocalRing.residue ↥A))
    · obtain ⟨h0, hres⟩ := hR₀ (jqNModC ↥A M') hjNmemF₀
      have eJ : R₀.residue ⟨_, h0⟩ = jNGeomGen (ResidueField ↥A) M' := by
        apply Subtype.ext
        refine hres.trans ?_
        show coeffMap (IsLocalRing.residue ↥A) (qExpand ↥A M' (jqModC ↥A)) = qExpand (ResidueField ↥A) M' (jqModC _)
        rw [IgusaNodesE121.coeffMap_qExpand]
        exact congrArg _ (map_jqModC (IsLocalRing.residue ↥A))
      obtain ⟨hC, hjc⟩ := hj _ h0
      rw [← eJ, RingHom.comp_apply, ← hjc, hθ]
      have := hredpres ⟨_, hC⟩ (jqNModC ↥A M') 1 (by rw [map_one]; exact one_ne_zero)
        (by rw [map_one, mul_one, IntermediateField.coe_inclusion])
      rw [map_one, mul_one] at this
      refine this.trans ?_
      show coeffMap (IsLocalRing.residue ↥A) (qExpand ↥A M' (jqModC ↥A)) = qExpand (ResidueField ↥A) M' (jqModC _)
      rw [IgusaNodesE121.coeffMap_qExpand]
      exact congrArg _ (map_jqModC (IsLocalRing.residue ↥A))

  have chev : ∀ s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'),
      ∃ P : Place (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')),
        ∀ g' : ↥(modularFunctionFieldC (ResidueField ↥A) M'), g' ∈ s.toValuationSubring ↔ j g' ∈ P.toValuationSubring := by
    intro s
    have htr : ∃ t : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))),
        Transcendental (ResidueField ↥A) t := by
      refine ⟨⟨jqModC (ResidueField ↥A), intFormRatiosC_subset _ _ (jqModC_mem_intFormRatiosC _ _)⟩, fun halg => ?_⟩
      exact transcendental_jqModC (ResidueField ↥A) (by simpa using halg.algebraMap (A := LaurentSeries (ResidueField ↥A)))
    exact IgusaNodesE121.exists_place_qExpFunctionFieldC_restrict_eq
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (translation_mem_GammaH (q ^ 2 * M') (levelH q M')) jA htr s

  have memNIg : ∀ (s : ↥W) (P : Place (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))),
      (∀ g' : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
        g' ∈ (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring ↔
          j g' ∈ P.toValuationSubring) → P ∈ NIg := fun s P h => (hNIg P).mpr ⟨s, h⟩

  have hmemF₀ : ∀ f : ↥(modularFunctionFieldBar M'),
      (f : LaurentSeries ℚ̄) ∈ laurentBaseChange ℚ̄ (qExpFunctionFieldC ℚ (Gamma0 M')) := by
    intro f; rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]; exact f.2

  have main : ∀ ℓ : CuspidalType.ProjLine q,
      ∃ (xsℓ : ↥W → Place (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')))
        (jℓ : ↥(modularFunctionFieldC (ResidueField ↥A) M') →+* ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))),
        (∀ s, xsℓ s ∈ NIg) ∧
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : g ℓ (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = jℓ (R₀.residue ⟨f, hf⟩)) ∧
        (∀ (s : ↥W) (g' : ↥(modularFunctionFieldC (ResidueField ↥A) M')),
          g' ∈ (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring ↔
            jℓ g' ∈ (xsℓ s).toValuationSubring) ∧
        (∀ c : ResidueField ↥A, jℓ (algebraMap (ResidueField ↥A) _ c) =
          algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c) ∧
        (∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g' : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
          g' ∈ (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring ↔
            jℓ g' ∈ Q.toValuationSubring) := by
    intro ℓ
    obtain ⟨-, γ, hγ, -, hgℓ⟩ := hg ℓ
    have hfO' : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
        IntermediateField.inclusion hle f ∈ R.integers := fun f hf => by
      rw [hR]; exact (hR₀O f).mp hf
    by_cases ha : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    ·
      have hexp : ∀ f : ↥(modularFunctionFieldBar M'),
          ((g ℓ (IntermediateField.inclusion hle f) : ↥(fieldBar q M')) : LaurentSeries ℚ̄) =
            qExpand ℚ̄ (q ^ 2) (f : LaurentSeries ℚ̄) := by
        intro f
        rw [hgℓ]
        exact coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ γ hγ ha _
          (hmemF₀ f) _ (IntermediateField.coe_inclusion hle f)
      have hc := expand_compat hle R₀ R hO red hredpres θ hθ j hj hfO' (g ℓ) hθj hexp
      have hp := expand_places (q := q) (M' := M') (A := A) hqM' W hW hrat

      have hlinℓ : ∀ c : ResidueField ↥A, (j.comp (Phi (ResidueField ↥A) q M').toRingHom) (algebraMap (ResidueField ↥A) _ c) =
          algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c := by
        intro c
        rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, hjalg]

      have hfW_inj : Function.Injective (fun s : ↥W => (hp s).choose) := by
        intro s₁ s₂ h12
        apply Subtype.ext
        apply Place.ext
        ext g'
        rw [(hp s₁).choose_spec g', (hp s₂).choose_spec g']
        exact Iff.of_eq (congrArg (fun s' : ↥W => Phi (ResidueField ↥A) q M' g' ∈
          (s' : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring) h12)
      have hfW_surj : Function.Surjective (fun s : ↥W => (hp s).choose) := Finite.injective_iff_surjective.mp hfW_inj
      have hNiffℓ : ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g' : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
          g' ∈ (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring ↔
            (j.comp (Phi (ResidueField ↥A) q M').toRingHom) g' ∈ Q.toValuationSubring := by
        intro Q
        constructor
        · intro hQ
          obtain ⟨s', hs'⟩ := (hNIg Q).mp hQ
          obtain ⟨s, hs⟩ := hfW_surj s'
          refine ⟨s, fun g' => ?_⟩
          rw [(hp s).choose_spec g', RingHom.comp_apply]
          rw [show (hp s).choose = s' from hs]
          exact hs' _
        · rintro ⟨s, hs⟩

          let V : ValuationSubring ↥(modularFunctionFieldC (ResidueField ↥A) M') := Q.toValuationSubring.comap j
          have hVmem : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) M'), g ∈ V ↔ j g ∈ Q.toValuationSubring :=
            fun g => ValuationSubring.mem_comap
          have hκV : ∀ a : ResidueField ↥A, algebraMap (ResidueField ↥A) _ a ∈ V := fun a => by
            rw [hVmem, hjalg]; exact Q.algebraMap_mem' a
          have hVtop : V ≠ ⊤ := by
            intro hV
            apply (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).ne_top'
            refine eq_top_iff.mpr fun g' _ => (hs g').mpr ?_
            rw [RingHom.comp_apply]
            exact (hVmem _).mp (hV.symm ▸ ValuationSubring.mem_top _)
          obtain ⟨x₀, hx₀, hfd₀⟩ := exists_transcendental_finiteDimensional_modularFunctionFieldC (ResidueField ↥A) q M' hqM'
          obtain ⟨t₀, -, hfd₀', hsep₀⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField hx₀ hfd₀
          haveI := hfd₀'
          haveI := hsep₀
          obtain ⟨s', hs'V⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_isSeparable t₀ V hκV hVtop
          have hrel : ∀ g' : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
              g' ∈ (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring ↔
                Phi (ResidueField ↥A) q M' g' ∈ s'.toValuationSubring := by
            intro g'
            rw [hs g', hs'V, hVmem, RingHom.comp_apply]
            rfl
          have hss' : s' ∈ W := by
            rw [hW]
            exact isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand q M' (ResidueField ↥A) 2
              (Phi (ResidueField ↥A) q M').toRingHom (fun g' => rfl) s s' hrel (hrat _) ((hW s).mp s.2)
          refine (hNIg Q).mpr ⟨⟨s', hss'⟩, fun g => ?_⟩
          show g ∈ s'.toValuationSubring ↔ _
          rw [hs'V, hVmem]
      exact ⟨fun s => (chev ((hp s).choose : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'))).choose,
        j.comp (Phi (ResidueField ↥A) q M').toRingHom,
        fun s => memNIg (hp s).choose _ (chev _).choose_spec, hc,
        fun s g' => ((hp s).choose_spec g').trans ((chev _).choose_spec (Phi (ResidueField ↥A) q M' g')), hlinℓ, hNiffℓ⟩
    ·
      obtain ⟨uA, huA, hres1⟩ := exists_unit_idx q A ζ
      obtain ⟨k, hk⟩ := exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
        q M' hqM' ζ γ hγ ha (Units.map (A.subtype : ↥A →* ℚ̄) uA) huA
      have htw : ∀ f : ↥(modularFunctionFieldBar M'),
          ((g ℓ (IntermediateField.inclusion hle f) : ↥(fieldBar q M')) : LaurentSeries ℚ̄) =
            qTwist (Units.map (A.subtype : ↥A →* ℚ̄) (uA ^ k)) (f : LaurentSeries ℚ̄) := by
        intro f
        rw [hgℓ, map_zpow]
        exact hk _ (hmemF₀ f) _ (IntermediateField.coe_inclusion hle f)
      have hc := twist_compat hle R₀ R hO red hredpres θ hθ j hj hfO' (g ℓ) (uA ^ k) (hres1 k) htw
      exact ⟨fun s => (chev s).choose, j, fun s => memNIg s _ (chev s).choose_spec, hc,
        fun s g' => (chev s).choose_spec g', hjalg, hNIg⟩
  choose xs jl hxs using main
  exact ⟨xs, fun ℓ s => (hxs ℓ).1 s, fun ℓ => ⟨jl ℓ, (hxs ℓ).2.1, (hxs ℓ).2.2.1, (hxs ℓ).2.2.2.1, (hxs ℓ).2.2.2.2⟩⟩

end Main
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd.IgusaNodesE133"

end S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mem_igusaNodes_over_of_levelAut_transport_linear_nodes_iff_of_eq_two_of_dvd (solution)
