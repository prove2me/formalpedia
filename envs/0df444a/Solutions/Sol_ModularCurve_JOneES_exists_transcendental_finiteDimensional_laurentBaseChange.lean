-- Prove2me | solution 1 for ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b8e3d605-22f9-51a1-a0b2-870f8c8c1969

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange

set_option autoImplicit false

namespace JOneESAlgBC

open HahnSeries Polynomial

section A1

variable {K : Type*} [Field K]

theorem valuation_algebraMap_le_one (d : K) :
    Valued.v (algebraMap K (LaurentSeries K) d) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [show algebraMap K (LaurentSeries K) d = ((PowerSeries.C d : PowerSeries K) : LaurentSeries K) by
    rw [LaurentSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]]
  rw [LaurentSeries.valuation_def, ← LaurentSeries.coe_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _

theorem valuation_le_one_of_isAlgebraic {y : LaurentSeries K} (hy : IsAlgebraic K y) :
    Valued.v y ≤ (1 : WithZero (Multiplicative ℤ)) := by
  have hint : IsIntegral K y := hy.isIntegral
  let v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ)) := Valued.v
  let O : Subring (LaurentSeries K) := v.integer
  have hInt : v.Integers O := Valuation.integer.integers _
  have hcoef : ∀ c : K, algebraMap K (LaurentSeries K) c ∈ O := fun c =>
    (Valuation.mem_integer_iff _ _).2 (valuation_algebraMap_le_one c)
  have hint' : IsIntegral O y := by
    obtain ⟨p, hp, hpy⟩ := hint
    let φ : K →+* O := (algebraMap K (LaurentSeries K)).codRestrict O hcoef
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap O (LaurentSeries K)).comp φ = algebraMap K (LaurentSeries K) := by
      ext c; rfl
    rw [hcomp]
    exact hpy
  exact (Valuation.mem_integer_iff _ _).1 (hInt.mem_of_integral hint')

theorem eq_C_of_isAlgebraic {y : LaurentSeries K} (hy : IsAlgebraic K y) :
    ∃ c : K, y = HahnSeries.C c := by
  refine ⟨y.coeff 0, ?_⟩
  set z : LaurentSeries K := y - HahnSeries.C (y.coeff 0) with hz
  have hzalg : IsAlgebraic K z := by
    have h2 : IsAlgebraic K (algebraMap K (LaurentSeries K) (y.coeff 0)) := isAlgebraic_algebraMap _
    rw [LaurentSeries.algebraMap_apply] at h2
    exact hy.sub h2

  have hy1 := valuation_le_one_of_isAlgebraic hy
  have hy0 : ∀ m < (0 : ℤ), y.coeff m = 0 :=
    (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K (D := 0) (f := y)).1 (by simpa using hy1)
  have hcoef : ∀ n < (1 : ℤ), z.coeff n = 0 := by
    intro n hn
    rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp (by simpa using hn) : n ≤ 0) with h | h
    · simp [hz, HahnSeries.coeff_sub, hy0 n h, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h.ne]
    · subst h; simp [hz, HahnSeries.C_apply]
  have hzval : Valued.v z ≤ WithZero.exp (-(1 : ℤ)) :=
    (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).2 hcoef

  by_cases hz0 : z = 0
  · exact (sub_eq_zero.mp hz0)
  · exfalso
    have h2 := valuation_le_one_of_isAlgebraic hzalg.inv
    have hprod : Valued.v z * Valued.v z⁻¹ = (1 : WithZero (Multiplicative ℤ)) := by
      rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
    have hlt : Valued.v z < (1 : WithZero (Multiplicative ℤ)) :=
      lt_of_le_of_lt hzval (by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    have := mul_lt_one_of_lt_of_le hlt h2
    rw [hprod] at this
    exact lt_irrefl _ this

theorem transcendental_of_coeff_ne_zero {y : LaurentSeries K} {n : ℤ} (hn : n ≠ 0)
    (hy : y.coeff n ≠ 0) : Transcendental K y := by
  intro halg
  obtain ⟨c, hc⟩ := eq_C_of_isAlgebraic halg
  apply hy
  rw [hc, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn]

end A1

end JOneESAlgBC

namespace JOneESBC

open ModularCurve HahnSeries Polynomial IntermediateField

variable (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

omit [Algebra ℚ L] in

theorem eq_C_of_forall_coeff_eq_zero {x : LaurentSeries ℚ} (h : ∀ n : ℤ, n ≠ 0 → x.coeff n = 0) :
    x = HahnSeries.C (x.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst hn; rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
  · rw [h n hn, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn]

theorem charZero_L : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ L).injective

theorem transcendental_coeffEmb {x : LaurentSeries ℚ} (hx : Transcendental ℚ x) :
    Transcendental L (coeffEmb L x) := by

  have hC : ∀ c : ℚ, algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.C c :=
    fun c => RingHom.congr_fun (Subsingleton.elim _ _) c
  have hne : ∃ n : ℤ, n ≠ 0 ∧ x.coeff n ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx
    refine ⟨X - Polynomial.C (x.coeff 0), X_sub_C_ne_zero _, ?_⟩
    rw [map_sub, aeval_X, aeval_C, hC, ← eq_C_of_forall_coeff_eq_zero (fun n hn => hall n hn), sub_self]
  obtain ⟨n, hn, hxn⟩ := hne
  refine JOneESAlgBC.transcendental_of_coeff_ne_zero hn ?_
  rw [coeffEmb_coeff]
  exact (map_ne_zero_iff _ (algebraMap ℚ L).injective).mpr hxn

omit [Algebra ℚ L] in

theorem algebraMap_rat_eq_C : algebraMap ℚ (LaurentSeries ℚ) = HahnSeries.C := Subsingleton.elim _ _

theorem coeffEmb_C (c : ℚ) : coeffEmb L (HahnSeries.C c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single]
  ext n
  rw [coeffEmb_coeff, HahnSeries.C_apply]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [HahnSeries.coeff_single_of_ne hn, HahnSeries.coeff_single_of_ne hn, map_zero]

theorem coeffEmb_mem_adjoin_of_mem_adjoin (x : LaurentSeries ℚ) {z : LaurentSeries ℚ}
    (hz : z ∈ ℚ⟮x⟯) : coeffEmb L z ∈ L⟮coeffEmb L x⟯ := by
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact IntermediateField.mem_adjoin_simple_self L _
  | algebraMap c =>
    rw [algebraMap_rat_eq_C, coeffEmb_C]
    exact IntermediateField.algebraMap_mem _ _
  | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y w _ _ hy hw => rw [map_mul]; exact mul_mem hy hw

omit [Algebra ℚ L] in

theorem finiteDimensional_adjoin_of_extendScalars {A : Type*} [Field A] [Algebra L A]
    (E : IntermediateField L A) (Y : E) (hle : L⟮(Y : A)⟯ ≤ E)
    (hfin : Module.Finite L⟮(Y : A)⟯ (IntermediateField.extendScalars hle)) :
    FiniteDimensional L⟮Y⟯ E := by
  let e₁ : L⟮(Y : A)⟯ ≃+* L⟮Y⟯ :=
    ((IntermediateField.liftAlgEquiv L⟮Y⟯).trans
      (IntermediateField.equivOfEq (IntermediateField.lift_adjoin_simple L E Y))).symm.toRingEquiv
  let e₂ : IntermediateField.extendScalars hle ≃+* E :=
    { toFun := fun z => ⟨z.1, z.2⟩
      invFun := fun z => ⟨z.1, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  refine Module.Finite.of_equiv_equiv e₁ e₂ ?_
  ext r
  rfl

omit [Algebra ℚ L] in
theorem finite_adjoin_of_le {A : Type*} [Field A] [Algebra L A] (K₁ : IntermediateField L A)
    (S T : Set A) [FiniteDimensional K₁ (IntermediateField.adjoin K₁ T)]
    (hle : IntermediateField.adjoin K₁ S ≤ IntermediateField.adjoin K₁ T) :
    FiniteDimensional K₁ (IntermediateField.adjoin K₁ S) :=
  Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

omit [Algebra ℚ L] in
theorem finite_extendScalars_of_adjoin {A : Type*} [Field A] [Algebra L A] (K₁ : IntermediateField L A)
    (S : Set A) (hle : K₁ ≤ IntermediateField.adjoin L S)
    [FiniteDimensional K₁ (IntermediateField.adjoin K₁ S)] :
    Module.Finite K₁ (IntermediateField.extendScalars hle) :=
  Module.Finite.equiv
    (IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin hle)).symm.toLinearEquiv

theorem finite_extendScalars (X₀ : F₀) [FiniteDimensional ℚ⟮X₀⟯ F₀]
    (hle : L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ ≤
      IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) :
    Module.Finite L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ (IntermediateField.extendScalars hle) := by
  classical
  haveI := charZero_L L

  haveI : Module.Free ℚ⟮X₀⟯ F₀ := Module.Free.of_divisionRing _ _
  let bF := Module.finBasis ℚ⟮X₀⟯ F₀
  let T : Set (LaurentSeries L) := Set.range fun j => coeffEmb L ((bF j : F₀) : LaurentSeries ℚ)
  haveI : Finite T := Set.finite_range _ |>.to_subtype

  have hcoeQ : ∀ c : ℚ, ((algebraMap ℚ F₀ c : F₀) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) c :=
    fun c => RingHom.congr_fun (Subsingleton.elim
      ((algebraMap F₀ (LaurentSeries ℚ)).comp (algebraMap ℚ F₀)) (algebraMap ℚ (LaurentSeries ℚ))) c
  have hval : ∀ z : F₀, z ∈ ℚ⟮X₀⟯ → (z : LaurentSeries ℚ) ∈ ℚ⟮(X₀ : LaurentSeries ℚ)⟯ := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self ℚ _
    | algebraMap c =>
      rw [hcoeQ]
      exact IntermediateField.algebraMap_mem _ _
    | add y w _ _ hy hw => rw [AddMemClass.coe_add]; exact add_mem hy hw
    | inv y _ hy =>
      rw [show ((y⁻¹ : F₀) : LaurentSeries ℚ) = ((y : F₀) : LaurentSeries ℚ)⁻¹ from rfl]
      exact inv_mem hy
    | mul y w _ _ hy hw => rw [MulMemClass.coe_mul]; exact mul_mem hy hw
  have hmemK₁ : ∀ r : ℚ⟮X₀⟯, coeffEmb L ((r : F₀) : LaurentSeries ℚ) ∈ L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ :=
    fun r => coeffEmb_mem_adjoin_of_mem_adjoin L _ (hval r r.2)

  let ψ : ℚ⟮X₀⟯ →+* L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ :=
    { toFun := fun r => ⟨coeffEmb L ((r : F₀) : LaurentSeries ℚ), hmemK₁ r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

  let Φ : F₀ →+* LaurentSeries L := (coeffEmb L).comp (algebraMap F₀ (LaurentSeries ℚ))
  have hΦψ : Φ.comp (algebraMap ℚ⟮X₀⟯ F₀) =
      (algebraMap L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ (LaurentSeries L)).comp ψ :=
    RingHom.ext fun _ => rfl
  have hint : ∀ t ∈ T, IsIntegral L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ t := by
    rintro _ ⟨j, rfl⟩
    have hb : IsIntegral ℚ⟮X₀⟯ (bF j) := IsIntegral.of_finite _ _
    obtain ⟨P, hPm, hP⟩ := hb
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, ← hΦψ]
    have := Polynomial.hom_eval₂ P (algebraMap ℚ⟮X₀⟯ F₀) Φ (bF j)
    rw [hP, map_zero] at this
    exact this.symm
  haveI hfinT : FiniteDimensional L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯
      (IntermediateField.adjoin L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ T) :=
    IntermediateField.finiteDimensional_adjoin hint

  have hST : (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) ⊆
      (IntermediateField.adjoin L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ T : Set _) := by
    rintro _ ⟨y, hy, rfl⟩
    have hrepr := bF.sum_repr ⟨y, hy⟩
    have hy' : coeffEmb L y = ∑ j, coeffEmb L (((bF.repr ⟨y, hy⟩ j : ℚ⟮X₀⟯) : F₀) : LaurentSeries ℚ) *
        coeffEmb L ((bF j : F₀) : LaurentSeries ℚ) := by
      have := congrArg (fun w : F₀ => coeffEmb L (w : LaurentSeries ℚ)) hrepr
      simp only at this
      rw [← this, IntermediateField.coe_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, MulMemClass.coe_mul, IntermediateField.algebraMap_apply, map_mul]
    rw [SetLike.mem_coe, hy']
    refine sum_mem fun j _ => ?_
    refine mul_mem ?_ (IntermediateField.subset_adjoin _ T ⟨j, rfl⟩)
    exact IntermediateField.algebraMap_mem
      (IntermediateField.adjoin L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ T) (ψ (bF.repr ⟨y, hy⟩ j))
  have hle' : IntermediateField.adjoin L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯
        (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) ≤
      IntermediateField.adjoin L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ T :=
    IntermediateField.adjoin_le_iff.mpr hST
  haveI hfinS : FiniteDimensional L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯
      (IntermediateField.adjoin L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯
        (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) :=
    finite_adjoin_of_le L _ _ T hle'

  exact finite_extendScalars_of_adjoin L _ _ hle

theorem exists_transcendental_finiteDimensional_laurentBaseChange
    (h : ∃ x : F₀, Transcendental ℚ x ∧ FiniteDimensional ℚ⟮x⟯ F₀) :
    ∃ y : laurentBaseChange L F₀, Transcendental L y ∧
      FiniteDimensional L⟮y⟯ (laurentBaseChange L F₀) := by
  classical
  haveI := charZero_L L
  obtain ⟨X₀, hX₀, hfin⟩ := h
  haveI := hfin
  have hxE : coeffEmb L (X₀ : LaurentSeries ℚ) ∈ laurentBaseChange L F₀ :=
    coeffEmb_mem_laurentBaseChange L X₀.2
  let Y : laurentBaseChange L F₀ := ⟨coeffEmb L (X₀ : LaurentSeries ℚ), hxE⟩

  have hxtr : Transcendental ℚ (X₀ : LaurentSeries ℚ) := by
    rintro ⟨r, hr0, hr⟩
    refine hX₀ ⟨r, hr0, ?_⟩
    apply Subtype.val_injective
    have := Polynomial.hom_eval₂ r (algebraMap ℚ F₀) (algebraMap F₀ (LaurentSeries ℚ)) X₀
    rw [Polynomial.aeval_def, ZeroMemClass.coe_zero, ← IntermediateField.algebraMap_apply, this,
      Subsingleton.elim ((algebraMap F₀ (LaurentSeries ℚ)).comp (algebraMap ℚ F₀))
        (algebraMap ℚ (LaurentSeries ℚ)), ← Polynomial.aeval_def]
    exact hr
  have hYtr : Transcendental L Y := by
    rintro ⟨r, hr0, hr⟩
    refine transcendental_coeffEmb L hxtr ⟨r, hr0, ?_⟩
    have := Polynomial.hom_eval₂ r (algebraMap L (laurentBaseChange L F₀))
      (algebraMap (laurentBaseChange L F₀) (LaurentSeries L)) Y
    rw [← IsScalarTower.algebraMap_eq] at this
    rw [Polynomial.aeval_def, show coeffEmb L (X₀ : LaurentSeries ℚ) =
      algebraMap (laurentBaseChange L F₀) (LaurentSeries L) Y from rfl, ← this,
      ← Polynomial.aeval_def, hr, map_zero]
  refine ⟨Y, hYtr, ?_⟩
  have hle : L⟮coeffEmb L (X₀ : LaurentSeries ℚ)⟯ ≤ laurentBaseChange L F₀ :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxE)
  exact finiteDimensional_adjoin_of_extendScalars L (laurentBaseChange L F₀) Y hle
    (finite_extendScalars L F₀ X₀ hle)

end JOneESBC

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
      Transcendental L x ∧
      FiniteDimensional
        (IntermediateField.adjoin L
          ({x} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
  JOneESBC.exists_transcendental_finiteDimensional_laurentBaseChange L _
    (ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC Γ hT)

end S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange (solution)
