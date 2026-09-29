-- Prove2me | solution 1 for ModularCurve.exists_riemannConstant_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fba649bd-9a21-5557-84c0-c682dfd63fe1

import Definitions.Def_ModularCurve_AtkinLehner
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Mathlib.Algebra.Polynomial.Basis
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_riemannConstant_modularFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

set_option autoImplicit false

open AlgebraicCurve ModularCurve

noncomputable section

open AlgebraicCurve ModularCurve IsDedekindDomain

namespace MWP5

private def rieszSubmodule (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar N) where
  carrier := {f | f = 0 ∨ ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    0 ≤ D v + v.ord f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    by_cases ha0 : a = 0
    · subst ha0; simpa using hb
    by_cases hb0 : b = 0
    · subst hb0; simpa using ha
    by_cases hab : a + b = 0
    · exact Or.inl hab
    rcases ha with h | ha; · exact absurd h ha0
    rcases hb with h | hb; · exact absurd h hb0
    refine Or.inr fun v => ?_
    have hmin := v.min_ord_le_ord_add ha0 hb0 hab
    have h1 := ha v
    have h2 := hb v
    rcases le_total (v.ord a) (v.ord b) with hor | hor
    · rw [min_eq_left hor] at hmin; omega
    · rw [min_eq_right hor] at hmin; omega
  smul_mem' := by
    intro c a ha
    by_cases hc : c = 0
    · subst hc; exact Or.inl (by rw [zero_smul])
    by_cases ha0 : a = 0
    · subst ha0; exact Or.inl (by rw [smul_zero])
    rcases ha with h | ha; · exact absurd h ha0
    refine Or.inr fun v => ?_
    have halg : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 :=
      fun h0 => hc ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
        (by rw [h0, map_zero]))
    rw [Algebra.smul_def, v.ord_mul halg ha0, v.ord_algebraMap c]
    have := ha v
    omega

private theorem mem_rieszSubmodule_iff (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {f : modularFunctionFieldBar N} :
    f ∈ rieszSubmodule N D ↔
      (f = 0 ∨ ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ D v + v.ord f) :=
  Iff.rfl

private theorem rieszSubmodule_mono (N : ℕ) [NeZero N]
    {D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D w ≤ E w) :
    rieszSubmodule N D ≤ rieszSubmodule N E := by
  intro f hf
  rcases (mem_rieszSubmodule_iff N D).mp hf with rfl | hall
  · exact zero_mem _
  · refine (mem_rieszSubmodule_iff N E).mpr (Or.inr fun w => ?_)
    have h1 := hall w
    have h2 := h w
    omega

private theorem mul_mem_riesz_of_mem_add (N : ℕ) [NeZero N]
    {D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    {f g : modularFunctionFieldBar N} (hf : f ≠ 0)
    (hE : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), E v = v.ord f)
    (hg : g ∈ rieszSubmodule N (D + E)) : f * g ∈ rieszSubmodule N D := by
  rw [mem_rieszSubmodule_iff]
  by_cases hg0 : g = 0
  · subst hg0; exact Or.inl (mul_zero f)
  rcases (mem_rieszSubmodule_iff N _).mp hg with h | hall; · exact absurd h hg0
  refine Or.inr fun v => ?_
  have h1 := hall v
  rw [Finsupp.add_apply, hE v] at h1
  rw [v.ord_mul hf hg0]
  omega

private theorem inv_mul_mem_riesz_add (N : ℕ) [NeZero N]
    {D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    {f h : modularFunctionFieldBar N} (hf : f ≠ 0)
    (hE : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), E v = v.ord f)
    (hh : h ∈ rieszSubmodule N D) : f⁻¹ * h ∈ rieszSubmodule N (D + E) := by
  rw [mem_rieszSubmodule_iff]
  by_cases hh0 : h = 0
  · subst hh0; exact Or.inl (mul_zero f⁻¹)
  rcases (mem_rieszSubmodule_iff N D).mp hh with h0 | hall; · exact absurd h0 hh0
  refine Or.inr fun v => ?_
  have h1 := hall v
  rw [Finsupp.add_apply, hE v, v.ord_mul (inv_ne_zero hf) hh0, v.ord_inv]
  omega

private theorem exists_linearEquiv_rieszSubmodule_add (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {f : modularFunctionFieldBar N} (hf : f ≠ 0)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hE : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), E v = v.ord f) :
    ∃ e : (rieszSubmodule N (D + E)) ≃ₗ[AlgebraicClosure ℚ] (rieszSubmodule N D),
      ∀ g : rieszSubmodule N (D + E), (e g : modularFunctionFieldBar N) = f * g := by
  refine ⟨{ toFun := fun g => ⟨f * g, mul_mem_riesz_of_mem_add N hf hE g.2⟩
            map_add' := fun a b => Subtype.ext ?_
            map_smul' := fun c a => Subtype.ext ?_
            invFun := fun h => ⟨f⁻¹ * h, inv_mul_mem_riesz_add N hf hE h.2⟩
            left_inv := fun g => Subtype.ext (inv_mul_cancel_left₀ hf _)
            right_inv := fun h => Subtype.ext (mul_inv_cancel_left₀ hf _) },
    fun g => rfl⟩
  · push_cast
    ring
  · simp only [SetLike.val_smul, RingHom.id_apply, mul_smul_comm]

private theorem finrank_rieszSubmodule_add_eq (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {f : modularFunctionFieldBar N} (hf : f ≠ 0)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hE : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), E v = v.ord f) :
    Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N (D + E))
      = Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N D) := by
  obtain ⟨e, -⟩ := exists_linearEquiv_rieszSubmodule_add N D hf E hE
  exact e.finrank_eq

private theorem mul_zpow_mem (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {π : v.toValuationSubring} (hπ : Irreducible π) {f : modularFunctionFieldBar N}
    (hf : f ∈ rieszSubmodule N (D + Finsupp.single v 1)) :
    f * (π : modularFunctionFieldBar N) ^ (D v + 1) ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · subst hf0; rw [zero_mul]; exact zero_mem _
  rcases (mem_rieszSubmodule_iff N _).mp hf with h | hall; · exact absurd h hf0
  have hπF : ((π : v.toValuationSubring) : modularFunctionFieldBar N) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hord : 0 ≤ v.ord (f * (π : modularFunctionFieldBar N) ^ (D v + 1)) := by
    rw [v.ord_mul hf0 (zpow_ne_zero _ hπF), v.ord_zpow, v.ord_coe_irreducible hπ, mul_one]
    have h1 := hall v
    rw [Finsupp.add_apply, Finsupp.single_eq_same] at h1
    omega
  exact v.mem_of_ord_nonneg (mul_ne_zero hf0 (zpow_ne_zero _ hπF)) hord

private def residueShiftToRing (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {π : v.toValuationSubring} (hπ : Irreducible π) :
    (rieszSubmodule N (D + Finsupp.single v 1)) →ₗ[AlgebraicClosure ℚ]
      v.toValuationSubring where
  toFun g := ⟨(g : modularFunctionFieldBar N)
    * (π : modularFunctionFieldBar N) ^ (D v + 1), mul_zpow_mem N D v hπ g.2⟩
  map_add' a b := Subtype.ext (by push_cast; ring)
  map_smul' c a := Subtype.ext (by
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def,
      MulMemClass.coe_mul, Place.coe_algebraMap, mul_assoc])

private def residueShift (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {π : v.toValuationSubring} (hπ : Irreducible π) :
    (rieszSubmodule N (D + Finsupp.single v 1)) →ₗ[AlgebraicClosure ℚ] v.ResidueField :=
  (Ideal.Quotient.mkₐ (AlgebraicClosure ℚ)
      (IsLocalRing.maximalIdeal v.toValuationSubring)).toLinearMap.comp
    (residueShiftToRing N D v hπ)

private theorem residueShift_apply (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {π : v.toValuationSubring} (hπ : Irreducible π)
    (g : rieszSubmodule N (D + Finsupp.single v 1)) :
    residueShift N D v hπ g = IsLocalRing.residue v.toValuationSubring
      ⟨(g : modularFunctionFieldBar N) * (π : modularFunctionFieldBar N) ^ (D v + 1),
        mul_zpow_mem N D v hπ g.2⟩ := by
  simp only [residueShift, residueShiftToRing]
  rfl

set_option maxHeartbeats 3200000 in

private theorem exists_linearMap_residueField_ker_eq (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ φ : (rieszSubmodule N (D + Finsupp.single v 1)) →ₗ[AlgebraicClosure ℚ] v.ResidueField,
      LinearMap.ker φ = Submodule.comap
        (rieszSubmodule N (D + Finsupp.single v 1)).subtype (rieszSubmodule N D) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  refine ⟨residueShift N D v hπ, ?_⟩
  ext g
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  by_cases h0 : (g : modularFunctionFieldBar N) = 0
  · constructor
    · intro _
      rw [h0]; exact zero_mem _
    · intro _
      rw [residueShift_apply]
      have hz : (⟨(g : modularFunctionFieldBar N)
          * (π : modularFunctionFieldBar N) ^ (D v + 1),
          mul_zpow_mem N D v hπ g.2⟩ : v.toValuationSubring) = 0 := by
        refine Subtype.ext ?_
        show (g : modularFunctionFieldBar N)
          * (π : modularFunctionFieldBar N) ^ (D v + 1) = 0
        rw [h0, zero_mul]
      rw [hz, map_zero]
  ·
    have hπF : ((π : v.toValuationSubring) : modularFunctionFieldBar N) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    have hgπ : (g : modularFunctionFieldBar N)
        * (π : modularFunctionFieldBar N) ^ (D v + 1) ≠ 0 :=
      mul_ne_zero h0 (zpow_ne_zero _ hπF)
    have hordg : v.ord ((g : modularFunctionFieldBar N)
        * (π : modularFunctionFieldBar N) ^ (D v + 1)) = v.ord (g : modularFunctionFieldBar N) + (D v + 1) := by
      rw [v.ord_mul h0 (zpow_ne_zero _ hπF), v.ord_zpow, v.ord_coe_irreducible hπ, mul_one]
    have hle : v.adicValuation ((g : modularFunctionFieldBar N)
        * (π : modularFunctionFieldBar N) ^ (D v + 1)) ≤ 1 := by
      have h1 : v.adicValuation (((⟨(g : modularFunctionFieldBar N)
          * (π : modularFunctionFieldBar N) ^ (D v + 1),
          mul_zpow_mem N D v hπ g.2⟩ : v.toValuationSubring)) : modularFunctionFieldBar N) ≤ 1 := by
        rw [v.adicValuation_coe]
        exact v.heightOneSpectrum.intValuation_le_one _
      exact h1
    have hne0 : v.adicValuation ((g : modularFunctionFieldBar N)
        * (π : modularFunctionFieldBar N) ^ (D v + 1)) ≠ 0 :=
      v.adicValuation_ne_zero hgπ
    have key : ¬(v.adicValuation ((g : modularFunctionFieldBar N)
        * (π : modularFunctionFieldBar N) ^ (D v + 1)) = 1)
        ↔ 0 ≤ D v + v.ord (g : modularFunctionFieldBar N) := by
      constructor
      · intro hne
        have hlt := lt_of_le_of_ne hle hne
        have hlog : WithZero.log (v.adicValuation ((g : modularFunctionFieldBar N)
            * (π : modularFunctionFieldBar N) ^ (D v + 1))) < WithZero.log 1 :=
          (WithZero.log_lt_log hne0 one_ne_zero).mpr hlt
        rw [WithZero.log_one] at hlog
        have h1 : 1 ≤ v.ord ((g : modularFunctionFieldBar N)
            * (π : modularFunctionFieldBar N) ^ (D v + 1)) := by
          show (1 : ℤ) ≤ -(WithZero.log (v.adicValuation ((g : modularFunctionFieldBar N)
            * (π : modularFunctionFieldBar N) ^ (D v + 1))))
          omega
        rw [hordg] at h1
        omega
      · intro hDv heq
        have hz : v.ord ((g : modularFunctionFieldBar N)
            * (π : modularFunctionFieldBar N) ^ (D v + 1)) = 0 := by
          show -(WithZero.log (v.adicValuation ((g : modularFunctionFieldBar N)
            * (π : modularFunctionFieldBar N) ^ (D v + 1)))) = 0
          rw [heq, WithZero.log_one, neg_zero]
        rw [hordg] at hz
        omega
    constructor
    · intro hker

      rw [residueShift_apply] at hker
      have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hker
      have hnu : ¬IsUnit (⟨(g : modularFunctionFieldBar N)
          * (π : modularFunctionFieldBar N) ^ (D v + 1),
          mul_zpow_mem N D v hπ g.2⟩ : v.toValuationSubring) :=
        mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
      have hDv := key.mp (fun heq => hnu ((v.adicValuation_coe_eq_one_iff _).mp heq))
      refine (mem_rieszSubmodule_iff N D).mpr (Or.inr fun w => ?_)
      by_cases hwv : w = v
      · subst hwv; exact hDv
      · rcases (mem_rieszSubmodule_iff N _).mp g.2 with h | hall; · exact absurd h h0
        have h1 := hall w
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hwv] at h1
        omega
    · intro hmem
      rcases (mem_rieszSubmodule_iff N D).mp hmem with h | hall; · exact absurd h h0
      have hDv := hall v
      have hne := key.mpr hDv
      have hnu : ¬IsUnit (⟨(g : modularFunctionFieldBar N)
          * (π : modularFunctionFieldBar N) ^ (D v + 1),
          mul_zpow_mem N D v hπ g.2⟩ : v.toValuationSubring) :=
        fun hu => hne ((v.adicValuation_coe_eq_one_iff
          (⟨(g : modularFunctionFieldBar N)
            * (π : modularFunctionFieldBar N) ^ (D v + 1),
            mul_zpow_mem N D v hπ g.2⟩ : v.toValuationSubring)).mpr hu)
      have hmm : (⟨(g : modularFunctionFieldBar N)
          * (π : modularFunctionFieldBar N) ^ (D v + 1),
          mul_zpow_mem N D v hπ g.2⟩ : v.toValuationSubring)
          ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      rw [residueShift_apply]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hmm

private theorem finrank_rieszSubmodule_add_single_le (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N (D + Finsupp.single v 1))
      ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N D) + 1 := by
  obtain ⟨φ, hker⟩ := exists_linearMap_residueField_ker_eq N D v
  have hmono : rieszSubmodule N D ≤ rieszSubmodule N (D + Finsupp.single v 1) := by
    refine rieszSubmodule_mono N fun w => ?_
    rw [Finsupp.add_apply]
    by_cases hwv : v = w
    · subst hwv; rw [Finsupp.single_eq_same]; omega
    · rw [Finsupp.single_eq_of_ne fun h => hwv h.symm]; omega
  by_cases hfd : FiniteDimensional (AlgebraicClosure ℚ)
      (rieszSubmodule N (D + Finsupp.single v 1))
  · haveI := hfd
    have hfr : Module.finrank (AlgebraicClosure ℚ) v.ResidueField = 1 :=
      ModularCurve.deg_eq_one_modularFunctionFieldBar N v
    haveI hfdκ : FiniteDimensional (AlgebraicClosure ℚ) v.ResidueField :=
      FiniteDimensional.of_finrank_pos (by rw [hfr]; omega)
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hrange : Module.finrank (AlgebraicClosure ℚ) (LinearMap.range φ) ≤ 1 := by
      have h1 := Submodule.finrank_le (LinearMap.range φ)
      omega
    have hkerfr : Module.finrank (AlgebraicClosure ℚ) (LinearMap.ker φ)
        = Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N D) := by
      rw [hker]
      exact (Submodule.comapSubtypeEquivOfLe hmono).finrank_eq
    omega
  · rw [Module.finrank_of_not_finite hfd]
    omega

private theorem exists_algebraMap_eq_of_forall_ord_nonneg (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N)
    (hf : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ v.ord f) :
    ∃ c : AlgebraicClosure ℚ,
      f = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, map_zero]⟩
  obtain ⟨Df, hDf, hdeg⟩ :=
    (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor
      f hf0
  have hall0 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord f = 0 := by
    have hsum : ∑ w ∈ Df.support, Df w * (w.deg : ℤ) = 0 := by
      rw [← AlgebraicCurve.Divisor.degree_eq_sum]; exact hdeg
    have hnn : ∀ w ∈ Df.support, 0 ≤ Df w * (w.deg : ℤ) := by
      intro w _
      rw [hDf w, ModularCurve.deg_eq_one_modularFunctionFieldBar N w]
      simpa using hf w
    have hterm : ∀ w ∈ Df.support, Df w * (w.deg : ℤ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    intro v
    by_cases hv : v ∈ Df.support
    · have h1 := hterm v hv
      rw [hDf v, ModularCurve.deg_eq_one_modularFunctionFieldBar N v] at h1
      simpa using h1
    · have h1 : Df v = 0 := Finsupp.notMem_support_iff.mp hv
      rw [← hDf v]
      exact h1
  have hj : Transcendental (AlgebraicClosure ℚ)
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)) :=
    ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩} :
        Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
  have hx := AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero
    ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
      modularFunctionFieldBar N)) hj hall0
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp hx
  exact ⟨c, hc.symm⟩

private theorem rieszSubmodule_zero_eq_span_one (N : ℕ) [NeZero N] :
    rieszSubmodule N 0
      = Submodule.span (AlgebraicClosure ℚ) {(1 : modularFunctionFieldBar N)} := by
  apply le_antisymm
  · intro f hf
    rcases (mem_rieszSubmodule_iff N 0).mp hf with rfl | hall
    · exact zero_mem _
    · obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_ord_nonneg N f
        (fun v => by simpa using hall v)
      exact Submodule.mem_span_singleton.mpr
        ⟨c, by rw [Algebra.smul_def, mul_one, ← hc]⟩
  · rw [Submodule.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (mem_rieszSubmodule_iff N 0).mpr (Or.inr fun v => by simp)

private theorem finrank_rieszSubmodule_zero (N : ℕ) [NeZero N] :
    Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N 0) = 1 := by
  rw [rieszSubmodule_zero_eq_span_one]
  exact finrank_span_singleton one_ne_zero

end MWP5

end

noncomputable section

open AlgebraicCurve ModularCurve

namespace MWP5

private abbrev jb (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩

end MWP5

end

noncomputable section

open AlgebraicCurve ModularCurve

namespace MWP5

private theorem ord_prod (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {ι : Type*} (s : Finset ι) (f : ι → modularFunctionFieldBar N)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        v.ord_mul (hf a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private theorem fd_riesz_zero (N : ℕ) [NeZero N] :
    FiniteDimensional (AlgebraicClosure ℚ) (rieszSubmodule N 0) :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_rieszSubmodule_zero]; omega)

private theorem fd_riesz_add_single (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hfd : FiniteDimensional (AlgebraicClosure ℚ) (rieszSubmodule N D)) :
    FiniteDimensional (AlgebraicClosure ℚ)
      (rieszSubmodule N (D + Finsupp.single v 1)) := by
  obtain ⟨φ, hker⟩ := exists_linearMap_residueField_ker_eq N D v
  haveI hκ : FiniteDimensional (AlgebraicClosure ℚ) v.ResidueField := by
    have hfr : Module.finrank (AlgebraicClosure ℚ) v.ResidueField = 1 :=
      ModularCurve.deg_eq_one_modularFunctionFieldBar N v
    exact FiniteDimensional.of_finrank_pos (by omega)
  have hmono : rieszSubmodule N D ≤ rieszSubmodule N (D + Finsupp.single v 1) := by
    refine rieszSubmodule_mono N fun w => ?_
    rw [Finsupp.add_apply]
    by_cases hwv : v = w
    · subst hwv; rw [Finsupp.single_eq_same]; omega
    · rw [Finsupp.single_eq_of_ne fun h => hwv h.symm]; omega
  haveI := hfd
  haveI hfdker : FiniteDimensional (AlgebraicClosure ℚ)
      (Submodule.comap (rieszSubmodule N (D + Finsupp.single v 1)).subtype
        (rieszSubmodule N D)) :=
    (Submodule.comapSubtypeEquivOfLe hmono).symm.finiteDimensional
  have h1 : (Submodule.map φ (⊤ : Submodule (AlgebraicClosure ℚ)
      (rieszSubmodule N (D + Finsupp.single v 1)))).FG := by
    rw [Submodule.map_top]
    exact Module.Finite.iff_fg.mp inferInstance
  have h2 : ((⊤ : Submodule (AlgebraicClosure ℚ)
      (rieszSubmodule N (D + Finsupp.single v 1))) ⊓ LinearMap.ker φ).FG := by
    rw [top_inf_eq, hker]
    exact Module.Finite.iff_fg.mp hfdker
  exact Module.finite_def.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker φ h1 h2)

private theorem degree_nonneg_of_effective (N : ℕ) [NeZero N]
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hE : ∀ v, 0 ≤ E v) : 0 ≤ Divisor.degree E := by
  rw [AlgebraicCurve.Divisor.degree_eq_sum]
  refine Finset.sum_nonneg fun w _ => ?_
  rw [ModularCurve.deg_eq_one_modularFunctionFieldBar N w]
  simpa using hE w

private theorem eq_zero_of_effective_of_degree_eq_zero (N : ℕ) [NeZero N]
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hE : ∀ v, 0 ≤ E v) (h0 : Divisor.degree E = 0) : E = 0 := by
  rw [AlgebraicCurve.Divisor.degree_eq_sum] at h0
  have hterm : ∀ w ∈ E.support, E w * (w.deg : ℤ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun w _ => by
      rw [ModularCurve.deg_eq_one_modularFunctionFieldBar N w]; simpa using hE w).mp h0
  ext w
  rw [Finsupp.zero_apply]
  by_cases hw : w ∈ E.support
  · have h1 := hterm w hw
    rw [ModularCurve.deg_eq_one_modularFunctionFieldBar N w] at h1
    simpa using h1
  · exact Finsupp.notMem_support_iff.mp hw

private theorem fd_riesz_of_effective_aux (N : ℕ) [NeZero N] (k : ℕ) :
    ∀ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, 0 ≤ E v) → Divisor.degree E = (k : ℤ) →
      FiniteDimensional (AlgebraicClosure ℚ) (rieszSubmodule N E) := by
  induction k with
  | zero =>
      intro E hE hk
      rw [eq_zero_of_effective_of_degree_eq_zero N E hE (by simpa using hk)]
      exact fd_riesz_zero N
  | succ k ih =>
      intro E hE hk
      obtain ⟨v, hv⟩ : ∃ v, 0 < E v := by
        by_contra hno
        simp only [not_exists, not_lt] at hno
        have hE0 : E = 0 := by
          ext w; rw [Finsupp.zero_apply]; exact le_antisymm (hno w) (hE w)
        rw [hE0, map_zero] at hk
        omega
      set E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
        E - Finsupp.single v 1 with hE'def
      have hE' : ∀ w, 0 ≤ E' w := by
        intro w
        rw [hE'def, Finsupp.sub_apply]
        by_cases hwv : v = w
        · subst hwv; rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne fun h => hwv h.symm]
          have := hE w; omega
      have hdeg' : Divisor.degree E' = (k : ℤ) := by
        rw [hE'def, map_sub, Divisor.degree_single,
          ModularCurve.deg_eq_one_modularFunctionFieldBar N v]
        push_cast at hk ⊢
        omega
      have hsplit : E = E' + Finsupp.single v 1 := by
        rw [hE'def]
        ext w
        rw [Finsupp.add_apply, Finsupp.sub_apply]
        ring
      rw [hsplit]
      exact fd_riesz_add_single N _ v (ih _ hE' hdeg')

private theorem fd_riesz_of_effective (N : ℕ) [NeZero N]
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hE : ∀ v, 0 ≤ E v) :
    FiniteDimensional (AlgebraicClosure ℚ) (rieszSubmodule N E) :=
  fd_riesz_of_effective_aux N (Divisor.degree E).toNat E hE
    (Int.toNat_of_nonneg (degree_nonneg_of_effective N E hE)).symm

private theorem fd_riesz (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    FiniteDimensional (AlgebraicClosure ℚ) (rieszSubmodule N D) := by
  have hle : rieszSubmodule N D
      ≤ rieszSubmodule N (D.mapRange (fun k => max k 0) (by simp)) :=
    rieszSubmodule_mono N fun w => by
      rw [Finsupp.mapRange_apply]; exact le_max_left _ _
  haveI := fd_riesz_of_effective N (D.mapRange (fun k => max k 0) (by simp))
    (fun v => by rw [Finsupp.mapRange_apply]; exact le_max_right _ _)
  exact Submodule.finiteDimensional_of_le hle

private theorem li_pow_of_transcendental {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {x : A} (hx : Transcendental K x) :
    LinearIndependent K fun n : ℕ => x ^ n := by
  have h := (Polynomial.basisMonomials K).linearIndependent.map'
    (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot.mpr (by simpa using transcendental_iff_injective.mp hx))
  have heq : (⇑(Polynomial.aeval x).toLinearMap ∘ ⇑(Polynomial.basisMonomials K))
      = fun n : ℕ => x ^ n := by
    funext n
    simp [Polynomial.coe_basisMonomials, Polynomial.aeval_monomial]
  rwa [heq] at h

private theorem transcendental_gen (N : ℕ) [NeZero N] :
    Transcendental (AlgebraicClosure ℚ)
      (IntermediateField.AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N)) := by
  have htr : Transcendental (AlgebraicClosure ℚ) (jb N) :=
    ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have hinj : Function.Injective
      (algebraMap (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
        (modularFunctionFieldBar N)) :=
    RingHom.injective
      (algebraMap (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
        (modularFunctionFieldBar N))
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen (AlgebraicClosure ℚ) (jb N)] at htr
  exact (transcendental_algebraMap_iff hinj).mp htr

private theorem exists_mul_adjoin_ord_nonneg (N : ℕ) [NeZero N]
    (y : modularFunctionFieldBar N) (hy : y ≠ 0) :
    ∃ g : modularFunctionFieldBar N, g ≠ 0 ∧
      g ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N} ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ v.ord (jb N) → 0 ≤ v.ord (g * y) := by
  classical
  have htr : Transcendental (AlgebraicClosure ℚ) (jb N) :=
    ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have hjb0 : jb N ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  obtain ⟨Dy, hDy, -⟩ :=
    (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor
      y hy
  have hch : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ c : AlgebraicClosure ℚ, 0 ≤ v.ord (jb N) →
        0 < v.ord (jb N
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
    intro v
    by_cases hv : 0 ≤ v.ord (jb N)
    · obtain ⟨c, hc, -⟩ := (ModularCurve.jCoordinate_spec_modularFunctionFieldBar N).1 v hv
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose cf hcf using hch
  set P : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    Dy.support.filter (fun v => 0 ≤ v.ord (jb N)) with hPdef
  set g : modularFunctionFieldBar N :=
    ∏ u ∈ P, (jb N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (cf u)) ^ (-Dy u).toNat
    with hgdef
  have hfac : ∀ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      jb N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (cf u) ≠ 0 := by
    intro u h
    rw [sub_eq_zero] at h
    exact htr (h ▸ isAlgebraic_algebraMap (cf u))
  have hg0 : g ≠ 0 := by
    rw [hgdef]
    exact Finset.prod_ne_zero_iff.mpr fun u _ => pow_ne_zero _ (hfac u)
  have hgmem : g ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N} := by
    rw [hgdef]
    refine prod_mem fun u _ => pow_mem (sub_mem ?_ ?_) _
    · exact IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) (jb N)
    · exact (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N}).algebraMap_mem (cf u)
  refine ⟨g, hg0, hgmem, ?_⟩
  intro v hv
  have hfacord : ∀ u ∈ P,
      0 ≤ v.ord (jb N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (cf u)) := by
    intro u _
    by_cases hcu : cf u = 0
    · rw [hcu, map_zero, sub_zero]; exact hv
    · have halg : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (cf u) ≠ 0 :=
        fun h0 => hcu ((algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar N)).injective (by rw [h0, map_zero]))
      have hmin := v.min_ord_le_ord_add hjb0 (neg_ne_zero.mpr halg)
        (by rw [← sub_eq_add_neg]; exact hfac u)
      rw [← sub_eq_add_neg] at hmin
      have hordneg : v.ord (-(algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar N) (cf u))) = 0 := by
        rw [← map_neg]; exact v.ord_algebraMap (-(cf u))
      rw [hordneg, min_eq_right hv] at hmin
      exact hmin
  have hordg : v.ord g = ∑ u ∈ P, ((-Dy u).toNat : ℤ)
      * v.ord (jb N - algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar N) (cf u)) := by
    rw [hgdef, ord_prod N v P _ (fun u _ => pow_ne_zero _ (hfac u))]
    exact Finset.sum_congr rfl fun u _ => by rw [← zpow_natCast, Place.ord_zpow]
  have hmul : v.ord (g * y) = v.ord g + v.ord y := v.ord_mul hg0 hy
  by_cases hvP : v ∈ P
  · have hordy : v.ord y = Dy v := (hDy v).symm
    have hone : 0 < v.ord (jb N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (cf v)) := hcf v hv
    have hterm : ((-Dy v).toNat : ℤ) * 1 ≤ ((-Dy v).toNat : ℤ)
        * v.ord (jb N - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar N) (cf v)) :=
      mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
    have hkey : ((-Dy v).toNat : ℤ) ≤ v.ord g := by
      rw [hordg]
      calc ((-Dy v).toNat : ℤ) = ((-Dy v).toNat : ℤ) * 1 := by ring
        _ ≤ _ := hterm
        _ ≤ _ := Finset.single_le_sum
            (f := fun u => ((-Dy u).toNat : ℤ) * v.ord (jb N
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (cf u)))
            (fun u hu => mul_nonneg (Int.natCast_nonneg _) (hfacord u hu)) hvP
    rw [hmul, hordy]
    omega
  · have hDyv : Dy v = 0 := by
      by_contra hne
      exact hvP (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hv⟩)
    have hordy : v.ord y = 0 := by rw [← hDy v]; exact hDyv
    have hgnn : 0 ≤ v.ord g := by
      rw [hordg]
      exact Finset.sum_nonneg fun u hu =>
        mul_nonneg (Int.natCast_nonneg _) (hfacord u hu)
    rw [hmul, hordy]
    omega

private theorem exists_massaged_li_family (N : ℕ) [NeZero N] :
    ∃ z : Fin (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
        (modularFunctionFieldBar N)) → modularFunctionFieldBar N,
      LinearIndependent (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N}) z ∧
      ∀ (i : Fin (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
          (modularFunctionFieldBar N)))
        (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        0 ≤ v.ord (jb N) → 0 ≤ v.ord (z i) := by
  classical
  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
      (modularFunctionFieldBar N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
  let b := Module.finBasis (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
    (modularFunctionFieldBar N)
  have hma := fun i => exists_mul_adjoin_ord_nonneg N (b i) (b.ne_zero i)
  choose gf hg0 hgmem hgord using hma
  let u : Fin (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
      (modularFunctionFieldBar N)) →
      (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})ˣ :=
    fun i => Units.mk0 ⟨gf i, hgmem i⟩
      (fun h => hg0 i (by simpa using congrArg Subtype.val h))
  have hz : ∀ i, (u • ⇑b) i = gf i * b i := by
    intro i
    rw [Pi.smul_apply', Units.smul_def, IntermediateField.smul_def, smul_eq_mul]
    rfl
  refine ⟨u • ⇑b, b.linearIndependent.units_smul u, fun i v hv => ?_⟩
  rw [hz i]
  exact hgord i v hv

private theorem li_tower_pow_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
    {S : IntermediateField K F} {x : ↥S} (hx : Transcendental K x)
    {ι : Type*} {z : ι → F} (hz : LinearIndependent (↥S) z) (n' : ℕ) :
    LinearIndependent K fun p : Fin n' × ι => (x ^ (p.1 : ℕ)) • z p.2 := by
  have hpows : LinearIndependent K fun a : Fin n' => x ^ (a : ℕ) :=
    (li_pow_of_transcendental hx).comp (fun a : Fin n' => (a : ℕ)) Fin.val_injective
  exact linearIndependent_smul hpows hz

private theorem card_le_finrank_of_li_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {W : Submodule K F} [FiniteDimensional K W]
    {ι : Type*} [Fintype ι] {g : ι → F}
    (hli : LinearIndependent K g) (hmem : ∀ i, g i ∈ W) :
    Fintype.card ι ≤ Module.finrank K W := by
  have h : LinearIndependent K fun i => (⟨g i, hmem i⟩ : W) :=
    LinearIndependent.of_comp W.subtype hli
  exact h.fintype_card_le_finrank

private theorem coe_pow_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
    {S : IntermediateField K F} (x : ↥S) (a : ℕ) (y : F) :
    (x ^ a) • y = (x : F) ^ a * y := by
  rw [IntermediateField.smul_def, smul_eq_mul, SubmonoidClass.coe_pow]

set_option maxHeartbeats 3200000 in

private theorem staircase_finrank_riesz_zsmul (N : ℕ) [NeZero N]
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB0 : ∀ v, 0 ≤ B v)
    (hBpole : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      v.ord (jb N) < 0 → B v = -v.ord (jb N))
    (hBoff : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 ≤ v.ord (jb N) → B v = 0) :
    ∃ m : ℕ, ∀ l : ℕ, m ≤ l →
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
          (modularFunctionFieldBar N) * (l + 1 - m)
        ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N ((l : ℤ) • B)) := by
  classical
  have htr : Transcendental (AlgebraicClosure ℚ) (jb N) :=
    ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have hjb0 : jb N ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  obtain ⟨z, hzli, hzord⟩ := exists_massaged_li_family N
  have hz0 : ∀ i, z i ≠ 0 := fun i => hzli.ne_zero i
  have hdiv := fun i =>
    (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor
      (z i) (hz0 i)
  choose Dz hDz _hdegz using hdiv
  set m := Finset.univ.sup (fun i => (Dz i).support.sup fun v => (-(Dz i) v).toNat)
    with hmdef
  refine ⟨m, ?_⟩
  intro l hl
  have hzB : ∀ (i : Fin (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
      (modularFunctionFieldBar N)))
      (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      -((m : ℤ) * B v) ≤ v.ord (z i) := by
    intro i v
    by_cases hv : 0 ≤ v.ord (jb N)
    · have h1 := hzord i v hv
      have h2 : 0 ≤ (m : ℤ) * B v := mul_nonneg (Int.natCast_nonneg _) (hB0 v)
      linarith [h1, h2]
    · rw [not_le] at hv
      by_cases hzv : 0 ≤ v.ord (z i)
      · have h2 : 0 ≤ (m : ℤ) * B v := mul_nonneg (Int.natCast_nonneg _) (hB0 v)
        linarith [hzv, h2]
      · rw [not_le] at hzv
        have hvsupp : v ∈ (Dz i).support :=
          Finsupp.mem_support_iff.mpr (by rw [hDz i v]; omega)
        have hle1 : ((-(Dz i) v).toNat : ℤ) ≤ (m : ℤ) := by
          have h1 : (-(Dz i) v).toNat ≤ (Dz i).support.sup fun v => (-(Dz i) v).toNat :=
            Finset.le_sup (f := fun w => (-(Dz i) w).toNat) hvsupp
          have h2 : ((Dz i).support.sup fun v => (-(Dz i) v).toNat) ≤ m := by
            rw [hmdef]
            exact Finset.le_sup
              (f := fun i => (Dz i).support.sup fun v => (-(Dz i) v).toNat)
              (Finset.mem_univ i)
          omega
        have hBv : B v = -v.ord (jb N) := hBpole v hv
        have hordzi : v.ord (z i) = (Dz i) v := (hDz i v).symm
        have hBv1 : 1 ≤ B v := by omega
        have hmB : (m : ℤ) ≤ (m : ℤ) * B v :=
          le_mul_of_one_le_right (Int.natCast_nonneg _) hBv1
        have h3 : -(Dz i) v ≤ (m : ℤ) := by omega
        rw [hordzi]
        linarith [hmB, h3]
  have hfam : LinearIndependent (AlgebraicClosure ℚ)
      (fun p : Fin (l + 1 - m) × Fin (Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
          (modularFunctionFieldBar N)) =>
        (IntermediateField.AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N) ^ (p.1 : ℕ)) • z p.2) :=
    li_tower_pow_smul (transcendental_gen N) hzli (l + 1 - m)
  have hmem : ∀ (a : ℕ), a ≤ l - m →
      ∀ (i : Fin (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
          (modularFunctionFieldBar N)))
        (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      0 ≤ ((l : ℤ) • B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v
        + v.ord (jb N ^ a * z i) := by
    intro a ha i v
    have hordm : v.ord (jb N ^ a * z i) = (a : ℤ) * v.ord (jb N) + v.ord (z i) := by
      rw [v.ord_mul (pow_ne_zero a hjb0) (hz0 i), ← zpow_natCast, Place.ord_zpow]
    rw [Finsupp.smul_apply, smul_eq_mul, hordm]
    by_cases hv : 0 ≤ v.ord (jb N)
    · have h1 := hzord i v hv
      have h2 : B v = 0 := hBoff v hv
      have h3 : 0 ≤ (a : ℤ) * v.ord (jb N) := mul_nonneg (Int.natCast_nonneg _) hv
      rw [h2]
      linarith [h1, h3]
    · rw [not_le] at hv
      have hBv : B v = -v.ord (jb N) := hBpole v hv
      have hzb := hzB i v
      have hml : (a : ℤ) + (m : ℤ) ≤ (l : ℤ) := by
        have h4 : a + m ≤ l := by omega
        exact_mod_cast h4
      have hkey : 0 ≤ ((l : ℤ) - (a : ℤ) - (m : ℤ)) * (-v.ord (jb N)) :=
        mul_nonneg (by omega) (by omega)
      rw [hBv] at hzb ⊢
      nlinarith [hzb, hkey]
  haveI hWfd := fd_riesz_of_effective N ((l : ℤ) • B)
    (fun v => by
      rw [Finsupp.smul_apply, smul_eq_mul]
      exact mul_nonneg (Int.natCast_nonneg _) (hB0 v))
  have hmemW : ∀ p : Fin (l + 1 - m) × Fin (Module.finrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N}) (modularFunctionFieldBar N)),
      (IntermediateField.AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N) ^ (p.1 : ℕ)) • z p.2
        ∈ rieszSubmodule N ((l : ℤ) • B) := by
    intro p
    rw [coe_pow_smul, IntermediateField.AdjoinSimple.coe_gen]
    refine (mem_rieszSubmodule_iff N _).mpr (Or.inr fun v => ?_)
    exact hmem (p.1 : ℕ) (by have := p.1.isLt; omega) p.2 v
  have hcount := card_le_finrank_of_li_mem hfam hmemW
  rw [Nat.mul_comm]
  simpa using hcount

end MWP5

end

noncomputable section

open AlgebraicCurve ModularCurve IsDedekindDomain IntermediateField

namespace MWP5

private theorem jb_transcendental (N : ℕ) [NeZero N] :
    Transcendental (AlgebraicClosure ℚ) (jb N) :=
  ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N

private theorem jb_ne_zero (N : ℕ) [NeZero N] : jb N ≠ 0 :=
  fun h => jb_transcendental N (h ▸ isAlgebraic_zero)

private def poleDivisor (N : ℕ) [NeZero N] : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  (Classical.choose
      ((ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor
        (jb N) (jb_ne_zero N))).mapRange (fun z => max 0 (-z)) (by simp)

private theorem poleDivisor_apply (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    poleDivisor N v = max 0 (-v.ord (jb N)) := by
  rw [poleDivisor, Finsupp.mapRange_apply]
  congr 2
  exact (Classical.choose_spec
    ((ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor
      (jb N) (jb_ne_zero N))).1 v

private theorem poleDivisor_nonneg (N : ℕ) [NeZero N] :
    ∀ v, 0 ≤ poleDivisor N v := fun v => by rw [poleDivisor_apply]; exact le_max_left 0 _

private theorem poleDivisor_apply_of_neg (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h : v.ord (jb N) < 0) : poleDivisor N v = -v.ord (jb N) := by
  rw [poleDivisor_apply]; omega

private theorem poleDivisor_apply_of_nonneg (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h : 0 ≤ v.ord (jb N)) : poleDivisor N v = 0 := by
  rw [poleDivisor_apply]; omega

private theorem mem_support_poleDivisor_iff (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    v ∈ (poleDivisor N).support ↔ v.ord (jb N) < 0 := by
  rw [Finsupp.mem_support_iff, poleDivisor_apply]; omega

private abbrev KJ (N : ℕ) [NeZero N] : IntermediateField (AlgebraicClosure ℚ)
    (modularFunctionFieldBar N) := IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N}

private scoped instance instCharZeroKJ (N : ℕ) [NeZero N] : CharZero (KJ N) :=
  charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (KJ N)).injective

private scoped instance instFDKJ (N : ℕ) [NeZero N] :
    FiniteDimensional (KJ N) (modularFunctionFieldBar N) :=
  ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N

private scoped instance instSepKJ (N : ℕ) [NeZero N] :
    Algebra.IsSeparable (KJ N) (modularFunctionFieldBar N) :=
  Algebra.IsSeparable.of_integral (KJ N) (modularFunctionFieldBar N)

private theorem ord_aeval_jb_eq (N : ℕ) [NeZero N]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : w.ord (jb N) < 0)
    (p : Polynomial (AlgebraicClosure ℚ)) (hp : p ≠ 0) :
    w.ord (Polynomial.aeval (jb N) p) = (p.natDegree : ℤ) * w.ord (jb N) := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    have htr : Transcendental (AlgebraicClosure ℚ) (jb N) :=
      ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
    have hinj := transcendental_iff_injective.mp htr
    have hjb0 : jb N ≠ 0 := by
      intro h
      rw [h, Place.ord_zero] at hw
      exact lt_irrefl _ hw
    have hlc : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) p.leadingCoeff ≠ 0 :=
      fun h0 => (Polynomial.leadingCoeff_ne_zero.mpr hp)
        ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
          (by rw [h0, map_zero]))
    have hlead_ne : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) p.leadingCoeff
        * (jb N) ^ p.natDegree ≠ 0 := mul_ne_zero hlc (pow_ne_zero _ hjb0)
    have hlead : w.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        p.leadingCoeff * (jb N) ^ p.natDegree) = (p.natDegree : ℤ) * w.ord (jb N) := by
      rw [w.ord_mul hlc (pow_ne_zero _ hjb0), w.ord_algebraMap, zero_add, ← zpow_natCast,
        w.ord_zpow]
    have key : Polynomial.aeval (jb N) p = Polynomial.aeval (jb N) p.eraseLead
        + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) p.leadingCoeff
          * (jb N) ^ p.natDegree := by
      conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow p]
      rw [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    by_cases h0 : p.eraseLead = 0
    · rw [key, h0, map_zero, zero_add, hlead, hd]
    · have hlt : p.eraseLead.natDegree < p.natDegree :=
        (Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero p).resolve_right h0
      have hih := ih p.eraseLead.natDegree (hd ▸ hlt) p.eraseLead h0 rfl
      have hne : Polynomial.aeval (jb N) p.eraseLead ≠ 0 :=
        fun h => h0 (hinj (by rw [h, map_zero]))
      have hord_lt : w.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          p.leadingCoeff * (jb N) ^ p.natDegree)
            < w.ord (Polynomial.aeval (jb N) p.eraseLead) := by
        rw [hlead, hih]
        exact mul_lt_mul_of_neg_right (by exact_mod_cast hlt) hw
      rw [key, add_comm, w.ord_add_eq_of_lt hlead_ne hne hord_lt, hlead, hd]

private theorem ord_aeval_div_aeval_jb_eq (N : ℕ) [NeZero N]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : w.ord (jb N) < 0)
    (p q : Polynomial (AlgebraicClosure ℚ)) (hp : p ≠ 0) (hq : q ≠ 0) :
    w.ord (Polynomial.aeval (jb N) p / Polynomial.aeval (jb N) q)
      = ((p.natDegree : ℤ) - q.natDegree) * w.ord (jb N) := by
  have htr : Transcendental (AlgebraicClosure ℚ) (jb N) :=
    ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have hinj := transcendental_iff_injective.mp htr
  have hp' : Polynomial.aeval (jb N) p ≠ 0 := fun h => hp (hinj (by rw [h, map_zero]))
  have hq' : Polynomial.aeval (jb N) q ≠ 0 := fun h => hq (hinj (by rw [h, map_zero]))
  rw [div_eq_mul_inv, w.ord_mul hp' (inv_ne_zero hq'), w.ord_inv, ord_aeval_jb_eq N w hw p hp,
    ord_aeval_jb_eq N w hw q hq]
  ring

private theorem mem_toValuationSubring_iff_of_pole (N : ℕ) [NeZero N]
    (w w' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.ord (jb N) < 0) (hw' : w'.ord (jb N) < 0)
    {f : modularFunctionFieldBar N}
    (hf : f ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N}) :
    f ∈ w.toValuationSubring ↔ f ∈ w'.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ) f).mp hf
  have hp : p ≠ 0 := by
    rintro rfl
    apply hf0
    rw [hpq, map_zero, zero_div]
  have hq : q ≠ 0 := by
    rintro rfl
    apply hf0
    rw [hpq, map_zero, div_zero]
  rw [w.mem_iff_ord_nonneg hf0, w'.mem_iff_ord_nonneg hf0, hpq,
    ord_aeval_div_aeval_jb_eq N w hw p q hp hq, ord_aeval_div_aeval_jb_eq N w' hw' p q hp hq]
  rcases le_or_gt (((p.natDegree : ℤ) - q.natDegree)) 0 with hΔ | hΔ
  · exact ⟨fun _ => mul_nonneg_of_nonpos_of_nonpos hΔ hw'.le,
      fun _ => mul_nonneg_of_nonpos_of_nonpos hΔ hw.le⟩
  · exact ⟨fun h => absurd h (not_le.mpr (mul_neg_of_pos_of_neg hΔ hw)),
      fun h => absurd h (not_le.mpr (mul_neg_of_pos_of_neg hΔ hw'))⟩

private theorem restrict_adjoin_eq_of_pole (N : ℕ) [NeZero N]
    (w w' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.ord (jb N) < 0) (hw' : w'.ord (jb N) < 0) :
    w.restrict (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
      = w'.restrict (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N}) := by
  apply Place.toValuationSubring_injective
  ext f
  rw [Place.mem_restrict_iff, Place.mem_restrict_iff, IntermediateField.algebraMap_apply]
  exact mem_toValuationSubring_iff_of_pole N w w' hw hw' f.2

private theorem restrict_ord_gen_eq_neg_one (N : ℕ) [NeZero N]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.ord (jb N) < 0) :
    (w.restrict (F := ↥(KJ N))).ord (AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N)) = -1 := by
  have hepos : (0 : ℤ) < (w.ramificationIndex (F := ↥(KJ N)) : ℤ) := by
    exact_mod_cast w.ramificationIndex_pos (F := ↥(KJ N))

  have hstar : w.ord (jb N) = (w.ramificationIndex (F := ↥(KJ N)) : ℤ)
      * (w.restrict (F := ↥(KJ N))).ord (AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N)) := by
    have hR := w.ord_restrict (F := ↥(KJ N))
      (AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N))
    rw [AdjoinSimple.algebraMap_gen] at hR
    exact hR
  have hvneg : (w.restrict (F := ↥(KJ N))).ord
      (AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N)) < 0 := by
    by_contra hge
    rw [not_lt] at hge
    rw [hstar] at hw
    nlinarith

  obtain ⟨t, htord⟩ := (w.restrict (F := ↥(KJ N))).exists_ord_eq_one
  have hne : (t : modularFunctionFieldBar N) ≠ 0 := by
    intro h0
    have h0' : t = 0 := Subtype.ext h0
    rw [h0', Place.ord_zero] at htord
    exact one_ne_zero htord.symm

  obtain ⟨r, s, hrs⟩ :=
    (IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ)
      (t : modularFunctionFieldBar N)).mp (SetLike.coe_mem t)
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [map_zero, div_zero] at hrs; exact hne hrs
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [map_zero, zero_div] at hrs; exact hne hrs

  have halg : algebraMap (↥(KJ N)) (modularFunctionFieldBar N) t
      = (t : modularFunctionFieldBar N) := rfl
  have hordt : w.ord (algebraMap (↥(KJ N)) (modularFunctionFieldBar N) t)
      = (w.ramificationIndex (F := ↥(KJ N)) : ℤ) := by
    rw [w.ord_restrict (F := ↥(KJ N)) t, htord, mul_one]
  have hordt' : w.ord (algebraMap (↥(KJ N)) (modularFunctionFieldBar N) t)
      = ((r.natDegree : ℤ) - s.natDegree) * w.ord (jb N) := by
    rw [halg, hrs]
    exact ord_aeval_div_aeval_jb_eq N w hw r s hr0 hs0

  rw [hordt, hstar, ← mul_assoc, mul_comm _ (w.ramificationIndex (F := ↥(KJ N)) : ℤ),
    mul_assoc] at hordt'
  have hdiv : ((r.natDegree : ℤ) - s.natDegree)
      * (w.restrict (F := ↥(KJ N))).ord (AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N)) = 1 := by
    have hne_e : (w.ramificationIndex (F := ↥(KJ N)) : ℤ) ≠ 0 := by omega
    have := mul_left_cancel₀ hne_e (hordt'.symm.trans (mul_one _).symm)
    linarith
  have hdvd : (w.restrict (F := ↥(KJ N))).ord
      (AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N)) ∣ 1 :=
    ⟨(r.natDegree : ℤ) - s.natDegree, by linarith [hdiv]⟩
  have hunit := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
  omega

private theorem ramificationIndex_eq_neg_ord_of_pole (N : ℕ) [NeZero N]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.ord (jb N) < 0) :
    (w.ramificationIndex (F := ↥(KJ N)) : ℤ) = -w.ord (jb N) := by
  have hR := w.ord_restrict (F := ↥(KJ N)) (AdjoinSimple.gen (AlgebraicClosure ℚ) (jb N))
  rw [AdjoinSimple.algebraMap_gen, restrict_ord_gen_eq_neg_one N w hw] at hR
  linarith

private theorem degree_poleDivisor_le_finrank (N : ℕ) [NeZero N] :
    Divisor.degree (poleDivisor N)
      ≤ (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
          (modularFunctionFieldBar N) : ℤ) := by
  rcases (poleDivisor N).support.eq_empty_or_nonempty with hemp | ⟨w₀, hw₀⟩
  · rw [AlgebraicCurve.Divisor.degree_eq_sum, hemp, Finset.sum_empty]
    exact Int.natCast_nonneg _
  ·
    have hw₀ord : w₀.ord (jb N) < 0 := (mem_support_poleDivisor_iff N w₀).mp hw₀
    set v := w₀.restrict (F := ↥(KJ N)) with hv
    have hrestr : ∀ w ∈ (poleDivisor N).support, w.restrict (F := ↥(KJ N)) = v := by
      intro w hw
      exact restrict_adjoin_eq_of_pole N w w₀
        ((mem_support_poleDivisor_iff N w).mp hw) hw₀ord

    have hle := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank
      (K := AlgebraicClosure ℚ) (F := ↥(KJ N)) (F' := ↥(modularFunctionFieldBar N))
      v (poleDivisor N).support hrestr
    calc Divisor.degree (poleDivisor N)
        = ∑ w ∈ (poleDivisor N).support, poleDivisor N w * (w.deg : ℤ) :=
          AlgebraicCurve.Divisor.degree_eq_sum (poleDivisor N)
      _ = ∑ w ∈ (poleDivisor N).support, poleDivisor N w := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [ModularCurve.deg_eq_one_modularFunctionFieldBar N w, Nat.cast_one, mul_one]
      _ ≤ ∑ w ∈ (poleDivisor N).support,
            (w.ramificationIndex (F := ↥(KJ N)) : ℤ)
              * (Place.inertiaDeg (F := ↥(KJ N)) w : ℤ) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hword := (mem_support_poleDivisor_iff N w).mp hw
          rw [poleDivisor_apply_of_neg N w hword,
            ← ramificationIndex_eq_neg_ord_of_pole N w hword]
          have hfpos := Place.inertiaDeg_pos_of_finiteDimensional
            (K := AlgebraicClosure ℚ) (F := ↥(KJ N)) (F' := ↥(modularFunctionFieldBar N)) w
          have hepos := w.ramificationIndex_pos (F := ↥(KJ N))
          nlinarith
      _ ≤ _ := hle

end MWP5
p2m_reactivate "P2MW.S_ModularCurve_exists_riemannConstant_modularFunctionFieldBar.MWP5"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_riemannConstant_modularFunctionFieldBar.MWP5"

noncomputable section

open AlgebraicCurve ModularCurve IsDedekindDomain

namespace MWP5

private theorem degree_single_bar (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n := by
  rw [Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar N v]
  simp

private theorem finrank_rieszSubmodule_add_single_natCast_le (N : ℕ) [NeZero N]
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (b : ℕ) :
    Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N (E + Finsupp.single v (b : ℤ)))
      ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) + b := by
  induction b with
  | zero => rw [Nat.cast_zero, Finsupp.single_zero, add_zero, add_zero]
  | succ b ih =>
    have h := finrank_rieszSubmodule_add_single_le N (E + Finsupp.single v (b : ℤ)) v
    rw [Nat.cast_succ, Finsupp.single_add, ← add_assoc]
    omega

private theorem finrank_rieszSubmodule_add_le_of_nonneg (N : ℕ) [NeZero N]
    (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hA : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ A v)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N (E + A)) : ℤ)
      ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) + Divisor.degree A := by
  induction A using Finsupp.induction generalizing E with
  | zero => rw [add_zero, map_zero, add_zero]
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have hb0 : 0 ≤ b := by
      have h := hA a
      rwa [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h
    have hf : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ f v := by
      intro v
      by_cases hva : v = a
      · rw [hva, hfa]
      · have h := hA v
        rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hva, zero_add] at h
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
    have h1 := finrank_rieszSubmodule_add_single_natCast_le N E a n
    have h2 := ih hf (E + Finsupp.single a (n : ℤ))
    rw [map_add, degree_single_bar, ← add_assoc]
    omega

private theorem exists_ne_zero_of_finrank_rieszSubmodule_pos (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h : 0 < Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N D)) :
    ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f := by
  haveI := Module.nontrivial_of_finrank_pos h
  obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (0 : rieszSubmodule N D)
  have hf0 : f ≠ 0 := fun h0 => hne (Subtype.ext h0)
  rcases (mem_rieszSubmodule_iff N D).mp hf with h0 | hall
  · exact absurd h0 hf0
  · exact ⟨f, hf0, hall⟩

private theorem exists_ne_zero_of_defect_bounded (N : ℕ) [NeZero N] (C : ℕ)
    (h : ∀ k : ℕ, ∃ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (k : ℤ) ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) ∧
      Divisor.degree E ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) + C)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ((C + 1 : ℕ) : ℤ) ≤ Divisor.degree D) :
    ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f := by

  obtain ⟨Dp, hDp0, hDDp⟩ : ∃ Dp : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ Dp v) ∧
      (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D v ≤ Dp v) :=
    ⟨Finsupp.mapRange (fun n : ℤ => max n 0) (by simp) D, fun v => by simp, fun v => by simp⟩

  obtain ⟨E, hkE, hdefE⟩ := h ((Divisor.degree Dp).toNat + 1)
  have hB1 := finrank_rieszSubmodule_add_le_of_nonneg N Dp hDp0 (E - Dp)
  rw [sub_add_cancel] at hB1
  have hpos1 : 0 < Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N (E - Dp)) := by
    have h3 := Int.self_le_toNat (Divisor.degree Dp)
    push_cast at hkE
    omega
  obtain ⟨f₁, hf₁0, hf₁⟩ := exists_ne_zero_of_finrank_rieszSubmodule_pos N (E - Dp) hpos1

  obtain ⟨P, hP, hPdeg⟩ :=
    (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor
      f₁ hf₁0

  have heff : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 ≤ (E - (D - P)) v := by
    intro v
    have h1 := hf₁ v
    have h2 := hDDp v
    simp only [Finsupp.sub_apply] at h1 ⊢
    rw [hP v]
    omega
  have hB2 := finrank_rieszSubmodule_add_le_of_nonneg N (E - (D - P)) heff (D - P)
  rw [add_sub_cancel, map_sub, map_sub, hPdeg, sub_zero] at hB2

  have hR1 := finrank_rieszSubmodule_add_eq N (D - P) hf₁0 P hP
  rw [sub_add_cancel] at hR1
  apply exists_ne_zero_of_finrank_rieszSubmodule_pos N D
  push_cast at hD
  omega

private theorem exists_defect_bounded_of_staircase (N : ℕ) [NeZero N]
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (n m : ℕ) (hn : 1 ≤ n)
    (hdeg : Divisor.degree B ≤ n)
    (hstair : ∀ l : ℕ, m ≤ l →
      n * (l + 1 - m) ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N ((l : ℤ) • B))) :
    ∀ k : ℕ, ∃ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (k : ℤ) ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) ∧
      Divisor.degree E ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) + (n * m : ℕ) := by
  intro k
  have h := hstair (m + k) (Nat.le_add_right m k)
  rw [show m + k + 1 - m = k + 1 by omega] at h
  refine ⟨((m + k : ℕ) : ℤ) • B, ?_, ?_⟩
  · have h1 : k ≤ n * (k + 1) := by nlinarith
    exact_mod_cast h1.trans h
  · rw [map_zsmul, smul_eq_mul]
    have h1 : ((m + k : ℕ) : ℤ) * Divisor.degree B ≤ ((m + k : ℕ) : ℤ) * (n : ℤ) :=
      mul_le_mul_of_nonneg_left hdeg (by positivity)
    have h2 : ((n * (k + 1) : ℕ) : ℤ)
        ≤ (Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N (((m + k : ℕ) : ℤ) • B)) : ℤ) := by
      exact_mod_cast h
    push_cast at h1 h2 ⊢
    nlinarith

private theorem one_le_finrank_adjoin_jb (N : ℕ) [NeZero N] :
    1 ≤ Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) {jb N})
      (modularFunctionFieldBar N) :=
  Module.finrank_pos

private theorem exists_defect_bounded (N : ℕ) [NeZero N] :
    ∃ C : ℕ, ∀ k : ℕ, ∃ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (k : ℤ) ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) ∧
      Divisor.degree E ≤ Module.finrank (AlgebraicClosure ℚ) (rieszSubmodule N E) + C := by
  obtain ⟨m, hm⟩ := staircase_finrank_riesz_zsmul N (poleDivisor N) (poleDivisor_nonneg N)
    (poleDivisor_apply_of_neg N) (poleDivisor_apply_of_nonneg N)
  exact ⟨_, exists_defect_bounded_of_staircase N (poleDivisor N) _ m (one_le_finrank_adjoin_jb N)
    (degree_poleDivisor_le_finrank N) hm⟩

end MWP5
p2m_reactivate "P2MW.S_ModularCurve_exists_riemannConstant_modularFunctionFieldBar.MWP5"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_riemannConstant_modularFunctionFieldBar.MWP5"

theorem solution (N : ℕ) [NeZero N] :
    ∃ g' : ℕ, ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f := by
  obtain ⟨C, hC⟩ := MWP5.exists_defect_bounded N
  exact ⟨C + 1, fun D hD => MWP5.exists_ne_zero_of_defect_bounded N C hC D hD⟩

end S_ModularCurve_exists_riemannConstant_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_exists_riemannConstant_modularFunctionFieldBar (solution)
