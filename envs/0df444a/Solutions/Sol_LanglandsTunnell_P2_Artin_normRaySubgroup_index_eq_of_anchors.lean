-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.normRaySubgroup_index_eq_of_anchors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2ee33e6f-17f0-583f-b07d-ffc672eddbfb

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField"

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

private noncomputable def idealMultiplicity (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors

end HeckeCharacter

section Fold_SUnitBasic

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles"
p2m_open "M4aHerbrand"

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal WithZero

open scoped nonZeroDivisors

noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDedekindDomain R] in

private theorem spanSingleton_units_ne_zero (x : Kˣ) : spanSingleton R⁰ (x : K) ≠ 0 :=
  spanSingleton_ne_zero_iff.mpr x.ne_zero

private theorem count_spanSingleton_units_mul (v : HeightOneSpectrum R) (x y : Kˣ) :
    count K v (spanSingleton R⁰ ((x * y : Kˣ) : K)) =
      count K v (spanSingleton R⁰ (x : K)) + count K v (spanSingleton R⁰ (y : K)) := by
  rw [Units.val_mul, ← spanSingleton_mul_spanSingleton]
  exact count_mul K v (spanSingleton_units_ne_zero x) (spanSingleton_units_ne_zero y)

private theorem count_spanSingleton_mk' (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) (s : R⁰) :
    count K v (spanSingleton R⁰ (IsLocalization.mk' K r s)) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)
        - ((Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(s : R)} : Ideal R)).factors : ℤ) := by
  have hmk : IsLocalization.mk' K r s ≠ 0 := by
    rw [IsFractionRing.mk'_eq_div]
    exact div_ne_zero (by rwa [Ne, IsFractionRing.to_map_eq_zero_iff])
      (by rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact nonZeroDivisors.coe_ne_zero s)
  have hrep : spanSingleton R⁰ (IsLocalization.mk' K r s) =
      spanSingleton R⁰ ((algebraMap R K) (s : R))⁻¹ * ↑(Ideal.span {r} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, inv_mul_eq_div,
      ← IsFractionRing.mk'_eq_div]
  exact count_well_defined K v (spanSingleton_ne_zero_iff.mpr hmk) hrep

private theorem valuation_eq_one_iff_count_eq_zero (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuation K (x : K) = 1 ↔ count K v (spanSingleton R⁰ (x : K)) = 0 := by
  obtain ⟨⟨r, s⟩, hx⟩ := IsLocalization.mk'_surjective (M := R⁰) (S := K) (x : K)
  change IsLocalization.mk' K r s = (x : K) at hx
  have hr : r ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hx
    exact x.ne_zero hx.symm
  rw [← hx, valuation_of_mk', count_spanSingleton_mk' v hr s,
    intValuation_if_neg v hr, intValuation_if_neg v (nonZeroDivisors.coe_ne_zero s),
    ← exp_sub, show (1 : ℤᵐ⁰) = exp 0 by rw [exp_zero], exp_inj]
  omega

private theorem mem_unit_iff_count {T : Set (HeightOneSpectrum R)} {x : Kˣ} :
    x ∈ T.unit K ↔ ∀ v ∉ T, count K v (spanSingleton R⁰ (x : K)) = 0 := by
  have hmem : x ∈ T.unit K ↔
      ∀ v : HeightOneSpectrum R, v ∉ T → v.valuation K (x : K) = 1 := Iff.rfl
  rw [hmem]
  exact forall_congr' fun v => forall_congr' fun _ => valuation_eq_one_iff_count_eq_zero v x

private def sUnitCountHom (T : Set (HeightOneSpectrum R)) :
    Additive ↥(T.unit K) →+ (↥T → ℤ) where
  toFun x v := count K (v : HeightOneSpectrum R)
    (spanSingleton R⁰ (((x.toMul : ↥(T.unit K)) : Kˣ) : K))
  map_zero' := by
    funext v
    show count K (v : HeightOneSpectrum R) (spanSingleton R⁰ ((1 : Kˣ) : K)) = 0
    rw [Units.val_one, spanSingleton_one, count_one]
  map_add' x y := by
    funext v
    show count K (v : HeightOneSpectrum R)
        (spanSingleton R⁰ (((x.toMul * y.toMul : ↥(T.unit K)) : Kˣ) : K)) = _
    have hco : ((x.toMul * y.toMul : ↥(T.unit K)) : Kˣ)
        = ((x.toMul : ↥(T.unit K)) : Kˣ) * ((y.toMul : ↥(T.unit K)) : Kˣ) := rfl
    rw [hco, count_spanSingleton_units_mul]
    rfl

@[scoped simp] private theorem sUnitCountHom_apply (T : Set (HeightOneSpectrum R))
    (x : ↥(T.unit K)) (v : ↥T) :
    sUnitCountHom T (Additive.ofMul x) v
      = count K (v : HeightOneSpectrum R) (spanSingleton R⁰ ((x : Kˣ) : K)) :=
  rfl

private theorem sUnitCountHom_apply' (T : Set (HeightOneSpectrum R))
    (x : Additive ↥(T.unit K)) (v : ↥T) :
    sUnitCountHom T x v
      = count K (v : HeightOneSpectrum R)
          (spanSingleton R⁰ (((x.toMul : ↥(T.unit K)) : Kˣ) : K)) :=
  rfl

private theorem valuation_algebraMap_units_eq_one (v : HeightOneSpectrum R) (u : Rˣ) :
    v.valuation K (algebraMap R K (u : R)) = 1 := by
  have h1 : v.valuation K (algebraMap R K (u : R)) ≤ 1 := by
    rw [valuation_of_algebraMap]; exact v.intValuation_le_one _
  have h2 : v.valuation K (algebraMap R K ((u⁻¹ : Rˣ) : R)) ≤ 1 := by
    rw [valuation_of_algebraMap]; exact v.intValuation_le_one _
  have h3 : v.valuation K (algebraMap R K (u : R))
      * v.valuation K (algebraMap R K ((u⁻¹ : Rˣ) : R)) = 1 := by
    rw [← map_mul (v.valuation K), ← map_mul (algebraMap R K), Units.mul_inv, map_one, map_one]
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

private def ringUnitsUnitHom (T : Set (HeightOneSpectrum R)) : Rˣ →* ↥(T.unit K) where
  toFun u := ⟨Units.map (algebraMap R K : R →* K) u, fun v _ => by
    show v.valuation K ((Units.map (algebraMap R K : R →* K) u : Kˣ) : K) = 1
    exact valuation_algebraMap_units_eq_one v u⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

private theorem ringUnitsUnitHom_injective (T : Set (HeightOneSpectrum R)) :
    Function.Injective (ringUnitsUnitHom (K := K) (R := R) T) := fun _ _ h =>
  Units.map_injective (f := (algebraMap R K : R →* K))
    (IsFractionRing.injective R K) (Subtype.ext_iff.mp h)

private theorem exists_ringUnits_eq_of_forall_valuation_eq_one {x : Kˣ}
    (h : ∀ v : HeightOneSpectrum R, v.valuation K (x : K) = 1) :
    ∃ u : Rˣ, Units.map (algebraMap R K : R →* K) u = x := by
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := R) K (x : K) fun v => (h v).le
  obtain ⟨s, hs⟩ := mem_integers_of_valuation_le_one (R := R) K ((x⁻¹ : Kˣ) : K) fun v =>
    le_of_eq (by rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one])
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_one, hr, hs, Units.val_inv_eq_inv_val, mul_inv_cancel₀ x.ne_zero]
  exact ⟨⟨r, s, hrs, by rwa [mul_comm] at hrs⟩, Units.ext hr⟩

private noncomputable def ringUnitsAddEquivCountHomKer (T : Set (HeightOneSpectrum R)) :
    Additive Rˣ ≃+ ↥(sUnitCountHom (K := K) (R := R) T).ker := by
  refine AddEquiv.ofBijective
    (AddMonoidHom.codRestrict
      (MonoidHom.toAdditive (ringUnitsUnitHom (K := K) T)) _ ?_)
    ⟨?_, ?_⟩
  ·
    intro u
    show sUnitCountHom T (Additive.ofMul (ringUnitsUnitHom (K := K) T u.toMul)) = 0
    funext v
    rw [sUnitCountHom_apply, Pi.zero_apply]
    refine (valuation_eq_one_iff_count_eq_zero (v : HeightOneSpectrum R) _).mp ?_
    show (v : HeightOneSpectrum R).valuation K
        ((Units.map (algebraMap R K : R →* K) u.toMul : Kˣ) : K) = 1
    exact valuation_algebraMap_units_eq_one _ _
  ·
    intro a b h
    have h' := Subtype.ext_iff.mp h
    exact Additive.toMul.injective
      (ringUnitsUnitHom_injective (K := K) T (Additive.toMul.injective h'))
  ·
    rintro ⟨x, hx⟩
    set xm : ↥(T.unit K) := x.toMul with hxm
    have hall : ∀ v : HeightOneSpectrum R,
        count K v (spanSingleton R⁰ ((xm : Kˣ) : K)) = 0 := by
      intro v
      by_cases hvT : v ∈ T
      · have := congrFun hx ⟨v, hvT⟩
        rwa [sUnitCountHom_apply', Pi.zero_apply] at this
      · exact mem_unit_iff_count.mp xm.2 v hvT
    have hval : ∀ v : HeightOneSpectrum R, v.valuation K ((xm : Kˣ) : K) = 1 := fun v =>
      (valuation_eq_one_iff_count_eq_zero v _).mpr (hall v)
    obtain ⟨u, hu⟩ := exists_ringUnits_eq_of_forall_valuation_eq_one hval
    refine ⟨Additive.ofMul u, Subtype.ext ?_⟩
    show Additive.ofMul (ringUnitsUnitHom (K := K) T u) = x
    apply Additive.toMul.injective
    exact Subtype.ext hu

private theorem moduleFinite_additive_unit (T : Set (HeightOneSpectrum R)) [Finite T]
    (hRu : Module.Finite ℤ (Additive Rˣ)) :
    Module.Finite ℤ (Additive ↥(T.unit K)) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (sUnitCountHom (K := K) (R := R) T).toIntLinearMap ?_ ?_
  · haveI : Fintype ↥T := Fintype.ofFinite ↥T
    have : Module.Finite ℤ (↥T → ℤ) := inferInstance
    exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv
      (ringUnitsAddEquivCountHomKer (K := K) (R := R) T).toIntLinearEquiv

end

end M4aHerbrand
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section NumberFieldInstance

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField"

private noncomputable scoped instance (K : Type*) [Field K] [NumberField K]
    (T : Set (IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K))) [Finite T] :
    Module.Finite ℤ (Additive ↥(T.unit K)) :=
  M4aHerbrand.moduleFinite_additive_unit T inferInstance

end NumberFieldInstance
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_SUnitBasic
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_SUnitDirichlet

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles"
p2m_open "M4aHerbrand"

p2m_open "IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField Module"

open scoped nonZeroDivisors

noncomputable section

private theorem finrank_eq_zero_of_finite (G : Type*) [AddCommGroup G] [Finite G] :
    finrank ℤ G = 0 := by
  apply finrank_eq_zero_of_rank_eq_zero
  rw [rank_eq_zero_iff]
  exact fun x => ⟨Nat.card G, Nat.cast_ne_zero.mpr Nat.card_pos.ne',
    by simp [card_nsmul_eq_zero']⟩

variable (K : Type*) [Field K] [NumberField K]

private theorem finrank_additive_ringOfIntegers_units :
    finrank ℤ (Additive (RingOfIntegers K)ˣ) = NumberField.Units.rank K := by
  set N : Submodule ℤ (Additive (RingOfIntegers K)ˣ) :=
    AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup (NumberField.Units.torsion K)) with hN
  have hsplit := Submodule.finrank_quotient_add_finrank N
  have hN0 : finrank ℤ (↥N) = 0 := by
    have : Finite (↥N) := (inferInstance : Finite (NumberField.Units.torsion K))
    exact finrank_eq_zero_of_finite _
  have hquot : finrank ℤ (Additive (RingOfIntegers K)ˣ ⧸ N) = NumberField.Units.rank K := by
    have := NumberField.Units.rank_modTorsion K
    convert this using 2
    rfl
    rfl
    rfl
  rw [← hsplit, hN0, add_zero]
  exact hquot

private theorem finrank_unit_le (T : Set (HeightOneSpectrum (RingOfIntegers K))) [Finite T] :
    finrank ℤ (Additive ↥(T.unit K)) ≤ Nat.card T + NumberField.Units.rank K := by
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  set f := (sUnitCountHom (R := RingOfIntegers K) (K := K) T).toIntLinearMap with hf
  have hsplit := Submodule.finrank_quotient_add_finrank (R := ℤ) (LinearMap.ker f)
  have hquot : finrank ℤ (Additive ↥(T.unit K) ⧸ LinearMap.ker f) ≤ Nat.card T := by
    calc finrank ℤ (Additive ↥(T.unit K) ⧸ LinearMap.ker f)
        = finrank ℤ ↥(LinearMap.range f) := LinearEquiv.finrank_eq f.quotKerEquivRange
      _ ≤ finrank ℤ (↥T → ℤ) := Submodule.finrank_le _
      _ = Nat.card T := by rw [Module.finrank_pi, Nat.card_eq_fintype_card]
  have hker : finrank ℤ ↥(LinearMap.ker f) = NumberField.Units.rank K := by
    have e : Additive (RingOfIntegers K)ˣ ≃+ ↥(LinearMap.ker f) :=
      ringUnitsAddEquivCountHomKer T
    rw [← LinearEquiv.finrank_eq e.toIntLinearEquiv]
    exact finrank_additive_ringOfIntegers_units K
  rw [← hsplit, hker]
  exact Nat.add_le_add_right hquot _

private theorem isPrincipal_asIdeal_pow_classNumber (v : HeightOneSpectrum (RingOfIntegers K)) :
    (v.asIdeal ^ classNumber K : Ideal (RingOfIntegers K)).IsPrincipal := by
  have hv : v.asIdeal ∈ (Ideal (RingOfIntegers K))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (by simpa using v.ne_bot)
  have hpow : v.asIdeal ^ classNumber K ∈ (Ideal (RingOfIntegers K))⁰ := pow_mem hv _
  have h1 : ClassGroup.mk0 (⟨v.asIdeal ^ classNumber K, hpow⟩ : (Ideal (RingOfIntegers K))⁰)
      = 1 := by
    have hrw : (⟨v.asIdeal ^ classNumber K, hpow⟩ : (Ideal (RingOfIntegers K))⁰)
        = (⟨v.asIdeal, hv⟩ : (Ideal (RingOfIntegers K))⁰) ^ classNumber K := rfl
    rw [hrw, map_pow]
    exact pow_card_eq_one
  exact (ClassGroup.mk0_eq_one_iff hpow).mp h1

open scoped Classical in

private theorem exists_sUnitCountHom_eq_classNumber_smul_single
    (T : Set (HeightOneSpectrum (RingOfIntegers K))) (v : ↥T) :
    ∃ x : Additive ↥(T.unit K),
      sUnitCountHom (R := RingOfIntegers K) (K := K) T x
        = (classNumber K : ℤ) • Pi.single v 1 := by
  classical
  obtain ⟨g, hg⟩ :=
    (isPrincipal_asIdeal_pow_classNumber K (v : HeightOneSpectrum (RingOfIntegers K))).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hpow0 : (v : HeightOneSpectrum (RingOfIntegers K)).asIdeal ^ classNumber K ≠ 0 :=
      pow_ne_zero _ (by simpa using (v : HeightOneSpectrum (RingOfIntegers K)).ne_bot)
    rw [hg] at hpow0
    simp at hpow0
  have hK0 : algebraMap (RingOfIntegers K) K g ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  set xu : Kˣ := Units.mk0 _ hK0 with hxu
  have hspan : spanSingleton (RingOfIntegers K)⁰ ((xu : Kˣ) : K)
      = ((v : HeightOneSpectrum (RingOfIntegers K)).asIdeal
          : FractionalIdeal (RingOfIntegers K)⁰ K) ^ classNumber K := by
    show spanSingleton (RingOfIntegers K)⁰ (algebraMap (RingOfIntegers K) K g) = _
    rw [← coeIdeal_span_singleton, show Ideal.span {g}
        = (v : HeightOneSpectrum (RingOfIntegers K)).asIdeal ^ classNumber K from hg.symm,
      coeIdeal_pow]
  have hprofile : ∀ w : HeightOneSpectrum (RingOfIntegers K),
      count K w (spanSingleton (RingOfIntegers K)⁰ ((xu : Kˣ) : K))
        = if w = (v : HeightOneSpectrum (RingOfIntegers K)) then (classNumber K : ℤ) else 0 := by
    intro w
    rw [hspan]
    by_cases hwv : w = (v : HeightOneSpectrum (RingOfIntegers K))
    · subst hwv
      rw [if_pos rfl, count_pow_self]
    · rw [if_neg hwv, count_pow, count_maximal_coprime K w (Ne.symm hwv), mul_zero]
  have hmem : xu ∈ T.unit K := by
    refine mem_unit_iff_count.mpr fun w hw => ?_
    rw [hprofile w, if_neg]
    rintro rfl
    exact hw v.2
  refine ⟨Additive.ofMul (⟨xu, hmem⟩ : ↥(T.unit K)), ?_⟩
  funext w
  rw [sUnitCountHom_apply, hprofile (w : HeightOneSpectrum (RingOfIntegers K))]
  by_cases hwv : w = v
  · subst hwv
    rw [if_pos rfl]
    simp
  · rw [if_neg (fun h => hwv (Subtype.ext h))]
    have : Pi.single (M := fun _ : ↥T => ℤ) v 1 w = 0 := by
      rw [Pi.single_apply, if_neg hwv]
    simp [this]

open scoped Classical in

private theorem classNumber_smul_mem_range_sUnitCountHom
    (T : Set (HeightOneSpectrum (RingOfIntegers K))) [Finite T] (y : ↥T → ℤ) :
    (classNumber K : ℤ) • y ∈ LinearMap.range
      (sUnitCountHom (R := RingOfIntegers K) (K := K) T).toIntLinearMap := by
  classical
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  have hsum : (classNumber K : ℤ) • y
      = ∑ v : ↥T, y v • ((classNumber K : ℤ) • Pi.single v 1) := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_apply, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_univ, mul_comm]
  rw [hsum]
  refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ ?_
  obtain ⟨x, hx⟩ := exists_sUnitCountHom_eq_classNumber_smul_single K T v
  exact ⟨x, hx⟩

private theorem finrank_unit_eq (T : Set (HeightOneSpectrum (RingOfIntegers K))) [Finite T] :
    finrank ℤ (Additive ↥(T.unit K)) = Nat.card T + NumberField.Units.rank K := by
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  refine le_antisymm (finrank_unit_le K T) ?_
  set f := (sUnitCountHom (R := RingOfIntegers K) (K := K) T).toIntLinearMap with hf
  have hker : finrank ℤ ↥(LinearMap.ker f) = NumberField.Units.rank K := by
    have e : Additive (RingOfIntegers K)ˣ ≃+ ↥(LinearMap.ker f) :=
      ringUnitsAddEquivCountHomKer T
    rw [← LinearEquiv.finrank_eq e.toIntLinearEquiv]
    exact finrank_additive_ringOfIntegers_units K
  have hrange_ge : Nat.card T ≤ finrank ℤ ↥(LinearMap.range f) := by
    let g : (↥T → ℤ) →ₗ[ℤ] ↥(LinearMap.range f) :=
      LinearMap.codRestrict (LinearMap.range f) ((classNumber K : ℤ) • LinearMap.id)
        fun y => classNumber_smul_mem_range_sUnitCountHom K T y
    have hg_inj : Function.Injective g := fun a b hab => by
      have h := congrArg Subtype.val hab
      simp only [g, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
      ext w
      have hw : a w = b w ∨ (classNumber K : ℤ) = 0 := by
        have h' := congrFun h w
        simp only [Pi.smul_apply, smul_eq_mul] at h'
        rcases mul_eq_mul_left_iff.mp h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr h''
      refine hw.resolve_right ?_
      exact_mod_cast (classNumber_pos K).ne'
    haveI : Module.Finite ℤ ↥(LinearMap.range f) := by
      rw [Module.Finite.iff_fg]; exact IsNoetherian.noetherian _
    calc Nat.card T = finrank ℤ (↥T → ℤ) := by
          rw [Module.finrank_pi, Nat.card_eq_fintype_card]
      _ ≤ finrank ℤ ↥(LinearMap.range f) := LinearMap.finrank_le_finrank_of_injective hg_inj
  have hsplit := Submodule.finrank_quotient_add_finrank (R := ℤ) (LinearMap.ker f)
  rw [← hsplit, hker]
  refine Nat.add_le_add_right ?_ _
  exact le_of_le_of_eq hrange_ge (LinearEquiv.finrank_eq f.quotKerEquivRange).symm

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end M4aHerbrand
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_SUnitDirichlet
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_SqIndexFG

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles"
p2m_open "M4aHerbrand"

open Submodule LinearMap

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

private abbrev twoSMul (M : Type*) [AddCommGroup M] [Module ℤ M] : Submodule ℤ M :=
  LinearMap.range (LinearMap.lsmul ℤ M 2)

private theorem lsmul_comp_equiv {N : Type*} [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) :
    (e : M →ₗ[ℤ] N) ∘ₗ LinearMap.lsmul ℤ M 2
      = LinearMap.lsmul ℤ N 2 ∘ₗ (e : M →ₗ[ℤ] N) := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply,
    LinearEquiv.coe_coe]
  exact e.map_smul 2 x

private theorem twoSMul_map_equiv {N : Type*} [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) :
    (twoSMul M).map (e : M →ₗ[ℤ] N) = twoSMul N := by
  rw [twoSMul, ← LinearMap.range_comp, lsmul_comp_equiv, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr e.surjective, Submodule.map_top]

private theorem card_quotient_twoSMul_congr {N : Type*} [AddCommGroup N] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) :
    Nat.card (M ⧸ twoSMul M) = Nat.card (N ⧸ twoSMul N) :=
  Nat.card_congr (Submodule.Quotient.equiv _ _ e (twoSMul_map_equiv e)).toEquiv

private def torsionByTwoCongr {N : Type*} [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) :
    torsionBy ℤ M 2 ≃ torsionBy ℤ N 2 where
  toFun x := ⟨e x, by
    rw [mem_torsionBy_iff, ← e.map_smul (2 : ℤ) (x : M),
      (mem_torsionBy_iff _ _).mp x.2, map_zero]⟩
  invFun y := ⟨e.symm y, by
    rw [mem_torsionBy_iff, ← e.symm.map_smul (2 : ℤ) (y : N),
      (mem_torsionBy_iff _ _).mp y.2, map_zero]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

private theorem card_quotient_twoSMul_pi (n : ℕ) :
    Nat.card ((Fin n → ℤ) ⧸ twoSMul (Fin n → ℤ)) = 2 ^ n := by
  have hpi : twoSMul (Fin n → ℤ)
      = Submodule.pi Set.univ (fun _ : Fin n => span ℤ {(2 : ℤ)}) := by
    ext f
    simp only [twoSMul, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ,
      forall_const, mem_span_singleton]
    constructor
    · rintro ⟨g, rfl⟩ i
      exact ⟨g i, by simp [mul_comm]⟩
    · intro hf
      choose c hc using hf
      refine ⟨c, funext fun i => ?_⟩
      simpa [smul_eq_mul, mul_comm] using hc i
  rw [hpi]
  have e1 := Submodule.quotientPi (fun _ : Fin n => span ℤ {(2 : ℤ)})
  rw [Nat.card_congr e1.toEquiv, Nat.card_pi]
  have e2 : Nat.card (ℤ ⧸ span ℤ {(2 : ℤ)}) = 2 := by
    rw [Nat.card_congr (Int.quotientSpanEquivZMod 2).toEquiv, Nat.card_zmod]
    decide
  simp only [e2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem card_quotient_twoSMul_eq_card_torsionBy_of_finite
    (T : Type*) [AddCommGroup T] [Module ℤ T] [Finite T] :
    Nat.card (T ⧸ twoSMul T) = Nat.card (torsionBy ℤ T 2) := by
  classical

  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range (lsmul ℤ T 2))
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (lsmul ℤ T 2))
  have h3 : Nat.card (T ⧸ LinearMap.ker (lsmul ℤ T 2))
      = Nat.card (LinearMap.range (lsmul ℤ T 2)) :=
    Nat.card_congr (lsmul ℤ T 2).quotKerEquivRange.toEquiv
  have h4 : Nat.card (torsionBy ℤ T 2) = Nat.card (LinearMap.ker (lsmul ℤ T 2)) :=
    Nat.card_congr (Equiv.setCongr (by
      ext x; simp [LinearMap.mem_ker]))
  have hrange_pos : 0 < Nat.card (LinearMap.range (lsmul ℤ T 2)) := Nat.card_pos
  rw [h3] at h2
  rw [mul_comm] at h2

  have key := h1.symm.trans h2
  rw [h4]
  exact Nat.eq_of_mul_eq_mul_left hrange_pos key

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end M4aHerbrand
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_SqIndexFG
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_SqIndexMain

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles"
p2m_open "M4aHerbrand"

open Submodule LinearMap

p2m_attr_erase "instance" "AddCommGroup.toIntModule"

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

private theorem twoSMul_prod (A B : Type*) [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] :
    twoSMul (A × B) = (twoSMul A).prod (twoSMul B) := by
  ext x
  simp only [twoSMul, LinearMap.mem_range, Submodule.mem_prod]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), ?_⟩
    have : (LinearMap.lsmul ℤ (A × B) 2) (a, b) = ((lsmul ℤ A 2) a, (lsmul ℤ B 2) b) := rfl
    rw [this, ha, hb]

private def quotientProdEquivProd {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (p : Submodule ℤ A) (q : Submodule ℤ B) :
    ((A × B) ⧸ p.prod q) ≃ₗ[ℤ] (A ⧸ p) × (B ⧸ q) := by
  refine (Submodule.quotEquivOfEq _ _ ?_).trans
    ((p.mkQ.prodMap q.mkQ).quotKerEquivOfSurjective ?_)
  · ext ⟨a, b⟩
    simp only [Submodule.mem_prod, LinearMap.mem_ker, LinearMap.prodMap_apply,
      Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mkQ_apply]
  · rintro ⟨⟨a⟩, ⟨b⟩⟩
    exact ⟨(a, b), rfl⟩

private theorem card_torsionBy_prod (A B : Type*) [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] :
    Nat.card (torsionBy ℤ (A × B) 2)
      = Nat.card (torsionBy ℤ A 2) * Nat.card (torsionBy ℤ B 2) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun x => (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩), fun y => ⟨(y.1, y.2), ?_⟩,
    fun x => rfl, fun y => rfl⟩
  · have := (mem_torsionBy_iff _ _).mp x.2
    rw [mem_torsionBy_iff]
    exact congrArg Prod.fst this
  · have := (mem_torsionBy_iff _ _).mp x.2
    rw [mem_torsionBy_iff]
    exact congrArg Prod.snd this
  · rw [mem_torsionBy_iff]
    exact Prod.ext ((mem_torsionBy_iff _ _).mp y.1.2) ((mem_torsionBy_iff _ _).mp y.2.2)

private theorem card_quotient_twoSMul_of_free (F : Type*) [AddCommGroup F] [Module ℤ F]
    [Module.Finite ℤ F] [Module.Free ℤ F] :
    Nat.card (F ⧸ twoSMul F) = 2 ^ Module.finrank ℤ F := by
  classical
  let b := Module.Free.chooseBasis ℤ F
  let e : F ≃ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ F → ℤ) := b.equivFun
  let i := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ F)
  let e2 : (Module.Free.ChooseBasisIndex ℤ F → ℤ) ≃ₗ[ℤ]
      (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ F)) → ℤ) :=
    LinearEquiv.funCongrLeft ℤ ℤ i.symm
  rw [card_quotient_twoSMul_congr (e.trans e2), card_quotient_twoSMul_pi,
    Module.finrank_eq_card_chooseBasisIndex ℤ F]

private theorem card_quotient_twoSMul_eq_card_torsionBy_mul_pow
    (M : Type*) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] :
    Nat.card (M ⧸ twoSMul M)
      = Nat.card (torsionBy ℤ M 2) * 2 ^ Module.finrank ℤ M := by
  classical
  set T := torsion ℤ M with hT
  haveI hfinF : Module.Finite ℤ (M ⧸ T) :=
    Module.Finite.of_surjective T.mkQ T.mkQ_surjective
  haveI hfreeF : Module.Free ℤ (M ⧸ T) := Module.free_of_finite_type_torsion_free'

  obtain ⟨f, hf⟩ := Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective
  have hfmk : ∀ y, T.mkQ (f y) = y := fun y => by
    have := congrArg (fun g : (M ⧸ T) →ₗ[ℤ] (M ⧸ T) => g y) hf
    simpa using this
  have hmem : ∀ x : M, x - f (T.mkQ x) ∈ T := by
    intro x
    have : T.mkQ (x - f (T.mkQ x)) = 0 := by
      rw [map_sub, hfmk, sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  let π : M →ₗ[ℤ] T :=
    LinearMap.codRestrict T (LinearMap.id - f ∘ₗ T.mkQ) fun x => by
      simpa using hmem x
  let φ : M →ₗ[ℤ] (M ⧸ T) × T := T.mkQ.prod π
  let ψ : (M ⧸ T) × T →ₗ[ℤ] M :=
    f ∘ₗ LinearMap.fst ℤ (M ⧸ T) T + T.subtype ∘ₗ LinearMap.snd ℤ (M ⧸ T) T
  have hψφ : ψ ∘ₗ φ = LinearMap.id := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
      LinearMap.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      Submodule.coe_subtype, LinearMap.id_coe, id_eq, φ, ψ, π, Function.prod,
      LinearMap.codRestrict_apply, LinearMap.sub_apply]
    abel
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, t⟩
    have ht0 : T.mkQ (t : M) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact t.2
    have h1 : T.mkQ (f y + (t : M)) = y := by
      rw [map_add, hfmk, ht0, add_zero]
    have happ : ψ (y, t) = f y + (t : M) := by
      simp [ψ]
    refine Prod.ext ?_ ?_
    · simpa [φ, happ] using h1
    · show π (ψ (y, t)) = t
      ext
      simp only [π, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.coe_comp, Function.comp_apply]
      rw [happ, h1]
      abel
  let e : M ≃ₗ[ℤ] (M ⧸ T) × T := LinearEquiv.ofLinear φ ψ hφψ hψφ

  haveI hnoeth : IsNoetherian ℤ M := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  haveI hfinT : Module.Finite ℤ T :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian T)
  haveI : Finite T := Module.finite_of_fg_torsion T (Submodule.torsion_isTorsion)

  have hcard : Nat.card (M ⧸ twoSMul M)
      = Nat.card ((M ⧸ T) ⧸ twoSMul (M ⧸ T)) * Nat.card (T ⧸ twoSMul T) := by
    rw [card_quotient_twoSMul_congr e, twoSMul_prod,
      Nat.card_congr (quotientProdEquivProd _ _).toEquiv, Nat.card_prod]
  have hbot : torsionBy ℤ (M ⧸ T) 2 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h2 : x ∈ torsion ℤ (M ⧸ T) :=
      ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, (mem_torsionBy_iff _ _).mp hx⟩
    rwa [Submodule.QuotientTorsion.torsion_eq_bot] at h2
  have htors : Nat.card (torsionBy ℤ M 2) = Nat.card (torsionBy ℤ T 2) := by
    rw [Nat.card_congr (torsionByTwoCongr e), card_torsionBy_prod, hbot]
    simp
  have hrankT : Module.rank ℤ T = 0 :=
    rank_eq_zero_iff_isTorsion.mpr Submodule.torsion_isTorsion
  have hrank : Module.finrank ℤ (M ⧸ T) = Module.finrank ℤ M := by
    have hq := rank_quotient_add_rank T
    rw [hrankT, add_zero] at hq
    show (Module.rank ℤ (M ⧸ T)).toNat = (Module.rank ℤ M).toNat
    rw [hq]
  rw [hcard, htors, card_quotient_twoSMul_of_free,
    card_quotient_twoSMul_eq_card_torsionBy_of_finite, hrank, mul_comm]

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end M4aHerbrand
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_SqIndexMain
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_SqClassSUnit

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles"
p2m_open "M4aHerbrand"

p2m_open "Submodule IsDedekindDomain NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField"

noncomputable section

section Bridge

variable {G : Type*} [CommGroup G]

private theorem mem_powTwoRange_iff_additive (x : G) :
    x ∈ (powMonoidHom 2 : G →* G).range
      ↔ Additive.ofMul x ∈ twoSMul (Additive G) := by
  simp only [MonoidHom.mem_range, powMonoidHom_apply, twoSMul, LinearMap.mem_range,
    LinearMap.lsmul_apply]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Additive.ofMul y, ?_⟩
    show (2 : ℤ) • Additive.ofMul y = Additive.ofMul (y ^ 2)
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, natCast_zsmul, ← ofMul_pow]
  · rintro ⟨y, hy⟩
    refine ⟨Additive.toMul y, Additive.ofMul.injective ?_⟩
    have hy' : ((2 : ℕ) : ℤ) • y = Additive.ofMul x := by
      rw [show (((2 : ℕ)) : ℤ) = (2 : ℤ) from rfl]
      exact hy
    rw [natCast_zsmul] at hy'
    rw [ofMul_pow, ofMul_toMul]
    exact hy'

private def quotientPowTwoEquivQuotientTwoSMul :
    (G ⧸ (powMonoidHom 2 : G →* G).range) ≃ Additive G ⧸ twoSMul (Additive G) :=
  Quotient.congrRight fun a b => by
    rw [QuotientGroup.leftRel_apply]
    show _ ↔ QuotientAddGroup.leftRel (twoSMul (Additive G)).toAddSubgroup a b
    rw [QuotientAddGroup.leftRel_apply]
    exact mem_powTwoRange_iff_additive _

private theorem card_quotient_powTwo_eq_additive :
    Nat.card (G ⧸ (powMonoidHom 2 : G →* G).range)
      = Nat.card (Additive G ⧸ twoSMul (Additive G)) :=
  Nat.card_congr quotientPowTwoEquivQuotientTwoSMul

private theorem card_torsionBy_additive_eq_sq_roots :
    Nat.card (torsionBy ℤ (Additive G) 2) = Nat.card {x : G // x ^ 2 = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Additive.toMul) fun a => ?_)
  rw [mem_torsionBy_iff]
  constructor
  · intro h
    have : Additive.toMul ((2 : ℤ) • a) = Additive.toMul (0 : Additive G) := by rw [h]
    simpa [toMul_zsmul, zpow_ofNat] using this
  · intro h
    have : Additive.toMul ((2 : ℤ) • a) = (1 : G) := by
      simpa [toMul_zsmul, zpow_ofNat] using h
    exact Additive.toMul.injective (by simpa using this)

private theorem card_quotient_powTwo_range [Module.Finite ℤ (Additive G)] :
    Nat.card (G ⧸ (powMonoidHom 2 : G →* G).range)
      = Nat.card {x : G // x ^ 2 = 1} * 2 ^ Module.finrank ℤ (Additive G) := by
  rw [card_quotient_powTwo_eq_additive,
    card_quotient_twoSMul_eq_card_torsionBy_mul_pow,
    card_torsionBy_additive_eq_sq_roots]

end Bridge
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section SqRoots

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

private theorem neg_one_mem_unit : (-1 : Kˣ) ∈ S.unit K := by
  have := (ringUnitsUnitHom (K := K) S (-1 : (𝓞 K)ˣ)).2
  convert this using 1
  rfl

private theorem sq_eq_one_iff_val (x : ↥(S.unit K)) :
    x ^ 2 = 1 ↔ ((x : Kˣ) : K) = 1 ∨ ((x : Kˣ) : K) = -1 := by
  constructor
  · intro h
    have hx : (((x : Kˣ) : K) - 1) * (((x : Kˣ) : K) + 1) = 0 := by
      have h2 : ((x : Kˣ) : K) ^ 2 = 1 := by
        have := congrArg (fun u : ↥(S.unit K) => ((u : Kˣ) : K)) h
        push_cast at this
        simpa using this
      ring_nf
      linear_combination h2
    rcases mul_eq_zero.mp hx with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  · intro h
    have : ((x : Kˣ) : K) ^ 2 = 1 := by
      rcases h with h | h <;> rw [h] <;> ring
    ext
    push_cast
    exact this

private theorem card_sq_roots_unit : Nat.card {x : ↥(S.unit K) // x ^ 2 = 1} = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, one_pow 2⟩, ⟨⟨⟨(-1 : Kˣ), neg_one_mem_unit S⟩, ?_⟩, ?_, ?_⟩⟩
  · ext
    push_cast
    ring
  · intro h
    have := congrArg (fun z : {x : ↥(S.unit K) // x ^ 2 = 1} => (((z : ↥(S.unit K)) : Kˣ) : K)) h
    simp only at this
    norm_num at this
  · ext z
    simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (sq_eq_one_iff_val S (z : ↥(S.unit K))).mp z.2 with h | h
    · left
      ext
      push_cast
      simpa using h
    · right
      ext
      push_cast
      simpa using h

end SqRoots
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

private theorem sUnit_card_quotient_sq (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    Nat.card (↥(S.unit K) ⧸ (powMonoidHom 2 : ↥(S.unit K) →* ↥(S.unit K)).range)
      = 2 ^ (Nat.card S + NumberField.Units.rank K + 1) := by
  rw [card_quotient_powTwo_range, card_sq_roots_unit, finrank_unit_eq (K := K) S,
    mul_comm, ← pow_succ]

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end M4aHerbrand
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_SqClassSUnit
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_FadContent

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply WithZero"

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageA

private theorem fadContentHom_apply (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v) :=
  rfl

end StageA
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section StageB

private theorem coe_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (placeOrd K u v) := by
  rw [fadContentHom_apply, ← Units.coeHom_apply,
    (Units.coeHom _).map_finprod_of_preimage_one (fun _ h => Units.ext h)
      (fun v => primeUnit K v ^ placeOrd K u v)]
  refine finprod_congr fun v => ?_
  rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, primeUnit_val]

private theorem count_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = placeOrd K u w := by
  rw [coe_fadContentHom]
  exact FractionalIdeal.count_finprod K w (placeOrd K u) (by
    rw [Filter.eventually_cofinite]
    exact finite_support_placeOrd K u)

private theorem fadContentHom_mem_coprimeToModulus_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (𝔣 : Ideal (𝓞 K)) :
    fadContentHom K u ∈ coprimeToModulus K 𝔣 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  rw [mem_coprimeToModulus_iff]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [count_fadContentHom, placeOrd_eq_zero_iff]

private theorem placeOrd_unitEmbedding (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K)) := by
  classical

  have hLHS : placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = -WithZero.log (v.valuation K (α : K)) := by
    unfold placeOrd
    rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
      FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (α : K)]
  rw [hLHS]

  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (M := (𝓞 K)⁰) (S := K) (α : K)
  have hnd' : IsLocalization.mk' K n d = (α : K) := hnd
  have hn0 : n ≠ 0 := by
    rintro rfl; simp only [IsLocalization.mk'_zero] at hnd'; exact α.ne_zero hnd'.symm
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  rw [← hnd', HeightOneSpectrum.valuation_of_mk',
    HeightOneSpectrum.intValuation_if_neg _ hn0, HeightOneSpectrum.intValuation_if_neg _ hd0,
    ← WithZero.exp_sub, WithZero.log_exp, neg_sub_neg,
    IsFractionRing.mk'_eq_div, div_eq_mul_inv,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0)
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, inv_eq_zero]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0),
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn0),
    show FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d)⁻¹
        = (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d))⁻¹ by
        rw [← one_div, ← FractionalIdeal.spanSingleton_div_spanSingleton,
          FractionalIdeal.spanSingleton_one, one_div],
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd0)]
  ring

private theorem coe_fadContentHom_principal (α : Kˣ) :
    ((fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K) := by
  rw [coe_fadContentHom]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K))
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr α.ne_zero)]
  exact finprod_congr fun v => by rw [placeOrd_unitEmbedding]

private theorem fadContentHom_unitEmbedding (α : Kˣ) :
    fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) = toPrincipalIdeal (𝓞 K) K α :=
  Units.ext <| (coe_fadContentHom_principal K α).trans (coe_toPrincipalIdeal α).symm

end StageB
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_FadContent
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_IdeleContentBuild

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply WithZero"

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageC

private theorem projFin_val (u : (AdeleRing (𝓞 K) K)ˣ) :
    ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) =
      (u : AdeleRing (𝓞 K) K).2 := rfl

private theorem projFin_principal (α : Kˣ) :
    projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)
      = FiniteAdeleRing.unitEmbedding (𝓞 K) K α := by
  apply Units.ext; rfl

omit [NumberField K] in

omit [NumberField K] in

omit [NumberField K] in

private theorem embedding_of_isReal_placeOf (τ : K →+* ℝ) :
    InfinitePlace.embedding_of_isReal (isReal_placeOf K τ) = τ := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, show (placeOf K τ).embedding
      = Complex.ofRealHom.comp τ from
    InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

private theorem archSign_principal (τ : K →+* ℝ) (α : Kˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) ↔ 0 < τ (α : K) := by
  unfold archSign archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe,
    embedding_of_isReal_placeOf K τ]
  rfl

namespace IsAdjuster p2m_export "HeckeCharacter.IsAdjuster" "mk cong sign" end IsAdjuster
namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.coprime {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ}
    (h : IsAdjuster K 𝔣 u α) :
    fadContentHom K (projFin K (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹))
      ∈ coprimeToModulus K 𝔣 := by
  rw [fadContentHom_mem_coprimeToModulus_iff]
  intro v hv
  rw [projFin_val]
  exact (h.cong v hv).1

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.coprime"
private theorem isAdjuster_one_one (𝔣 : Ideal (𝓞 K)) : IsAdjuster K 𝔣 1 1 := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · simp only [map_one, inv_one, mul_one]
    refine ⟨?_, ?_⟩
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
      rw [fad_one_apply]; exact map_one _
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
      rw [fad_one_apply, sub_self, map_zero]; exact zero_le'
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one K τ rfl

private abbrev adjFinV (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem four_comm {G : Type*} [CommMonoid G] (a b c d : G) :
    a * b * (d * c) = a * c * (b * d) := by
  simp only [mul_comm, mul_left_comm]

private abbrev pK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K))

private theorem adj_adele_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    u * u' * (pK K (α * α'))⁻¹ = (u * (pK K α)⁻¹) * (u' * (pK K α')⁻¹) := by
  rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _

private theorem adj_adele_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    (u * (pK K α)⁻¹)⁻¹ * (u * (pK K α')⁻¹) = pK K (α * α'⁻¹) := by
  rw [mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc, ← mul_assoc u⁻¹, inv_mul_cancel,
    one_mul]

private theorem adjFinV_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    adjFinV K (u * u') (α * α') v = adjFinV K u α v * adjFinV K u' α' v := by
  unfold adjFinV
  rw [show u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) from by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _]
  exact fad_mul_apply K _ _ v

namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.mul {𝔣 : Ideal (𝓞 K)} {u u' : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u' α') :
    IsAdjuster K 𝔣 (u * u') (α * α') := by
  have hfac : u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) := by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _
  refine ⟨fun v hv𝔣 => ?_, fun τ => ?_⟩
  · show Valued.v (adjFinV K (u * u') (α * α') v) = 1 ∧
      Valued.v (adjFinV K (u * u') (α * α') v - 1) ≤ _
    rw [adjFinV_mul]
    exact unit_cong_mul K (hα.cong v hv𝔣).1 (hα.cong v hv𝔣).2 (hα'.cong v hv𝔣).1
      (hα'.cong v hv𝔣).2
  · rw [hfac, archSign_mul K τ]
    exact iff_of_true (hα.sign τ) (hα'.sign τ)

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.mul"
private theorem isAdjuster_principal_self (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    IsAdjuster K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · have h1 : adjFinV K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α v = 1 := by
      unfold adjFinV; simp only [mul_inv_cancel, Units.val_one]
      exact fad_one_apply K v
    show Valued.v (adjFinV K _ α v) = 1 ∧ Valued.v (adjFinV K _ α v - 1) ≤ _
    rw [h1]
    exact ⟨map_one _, by rw [sub_self, map_zero]; exact zero_le'⟩
  · have h1 : (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α : (AdeleRing (𝓞 K) K)ˣ)
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ = 1 := mul_inv_cancel _
    rw [h1]; exact archSign_one K τ

private theorem adjFinV_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K)
      = adjFinV K u α' v * (adjFinV K u α v)⁻¹ := by
  have hkey := congrArg (fun x : (FiniteAdeleRing (𝓞 K) K)ˣ =>
    ((x : FiniteAdeleRing (𝓞 K) K) : FiniteAdeleRing (𝓞 K) K) v)
    (congrArg (projFin K) (adj_adele_ratio K u α α'))
  rw [map_mul, map_inv, projFin_principal] at hkey
  simp only [Units.val_mul, fad_mul_apply, fad_units_inv_apply, projFin_val] at hkey
  rw [show ((FiniteAdeleRing.unitEmbedding (𝓞 K) K (α * α'⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) from by
    rw [FiniteAdeleRing.unitEmbedding_apply]; exact FiniteAdeleRing.algebraMap_apply ..] at hkey
  rw [← hkey, mul_comm]; rfl

private theorem valuation_ratio_sub_one_le {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α')
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K (((α * α'⁻¹ : Kˣ) : K) - 1)
      ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
  rw [← v.valuedAdicCompletion_eq_valuation']
  have hcoe : ((((α * α'⁻¹ : Kˣ) : K) - 1 : K) : v.adicCompletion K)
      = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) - 1 := by
    have h := map_sub (algebraMap K (v.adicCompletion K)) ((α * α'⁻¹ : Kˣ) : K) 1
    rw [map_one] at h
    exact h
  rw [hcoe, adjFinV_ratio K u α α']
  exact unit_cong_div K (hα'.cong v hv).2 (hα.cong v hv).1 (hα.cong v hv).2

private theorem ratio_totally_positive {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') (τ : K →+* ℝ) :
    0 < τ ((α * α'⁻¹ : Kˣ) : K) := by
  rw [← archSign_principal K τ, show Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'⁻¹)
    = pK K (α * α'⁻¹) from rfl, map_mul, map_inv, archSign_mul K τ, archSign_inv K τ]
  have h1 : archSign K τ u ↔ archSign K τ (pK K α) := by
    have := hα.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  have h2 : archSign K τ u ↔ archSign K τ (pK K α') := by
    have := hα'.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  exact h1.symm.trans h2

private theorem valuation_eq_one_of_cong {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {β : K}
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (β - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K β = 1 := by
  have hm1 : 1 ≤ idealMultiplicity K v 𝔣 := by
    unfold idealMultiplicity
    rwa [Nat.one_le_iff_ne_zero, Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible]
  have hlt : v.valuation K (β - 1) < 1 :=
    lt_of_le_of_lt (hcong v hv) (by
      rw [show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
        WithZero.exp_lt_exp]
      omega)
  have hβ : β = (β - 1) + 1 := (sub_add_cancel β 1).symm
  rw [hβ, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

private theorem count_spanSingleton_eq_zero_of_valuation_eq_one {β : Kˣ}
    (v : HeightOneSpectrum (𝓞 K)) (h : v.valuation K (β : K) = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 := by
  rw [← placeOrd_unitEmbedding]
  unfold placeOrd
  rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
    FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (β : K), h,
    WithZero.log_one, neg_zero]

private theorem mem_modulus_of_forall_valuation_le {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {x : 𝓞 K}
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (algebraMap (𝓞 K) K x) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    x ∈ 𝔣 := by
  have h𝔣0 : (𝔣 : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [← Ideal.iInf_maxPowDividing_eq h𝔣0, Submodule.mem_iInf]
  intro v
  show x ∈ v.asIdeal ^ (idealMultiplicity K v 𝔣)
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := K)]
    exact hx v hv
  · have hm0 : idealMultiplicity K v 𝔣 = 0 := by
      unfold idealMultiplicity
      by_contra hne
      exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp hne)
    simp [hm0]

private theorem toPrincipalIdeal_mem_narrowRaySubgroup {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (β : Kˣ)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (hsign : ∀ τ : K →+* ℝ, 0 < τ (β : K)) :
    toPrincipalIdeal (𝓞 K) K β ∈ narrowRaySubgroup K 𝔣 := by

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 :=
    fun v hv => count_spanSingleton_eq_zero_of_valuation_eq_one K v
      (valuation_eq_one_of_cong K h𝔣 hcong v hv)

  obtain ⟨d, hd0, hd1, n, hn⟩ := movingLemma K h𝔣 (β : K) β.ne_zero hloc

  have hd0' : (algebraMap (𝓞 K) K) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [map_zero] at hn
    exact β.ne_zero ((mul_eq_zero.mp hn.symm).resolve_left hd0')

  have hnd1 : n - d ∈ 𝔣 := by
    refine mem_modulus_of_forall_valuation_le K h𝔣 fun v hv => ?_
    have hval_d : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      rw [v.valuation_of_algebraMap (K := K)]
      refine le_antisymm (v.intValuation_le_one d) ?_
      rw [← not_lt, v.intValuation_lt_one_iff_mem]
      intro hmem
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr
        (show (1 : 𝓞 K) ∈ v.asIdeal from by
          have : (d : 𝓞 K) - (d - 1) ∈ v.asIdeal := sub_mem hmem
            ((Ideal.dvd_iff_le.mp hv) hd1)
          simpa using this))
    have hsplit : (algebraMap (𝓞 K) K) (n - d)
        = algebraMap (𝓞 K) K d * ((β : K) - 1) := by
      rw [map_sub, hn]; ring
    rw [hsplit, map_mul, hval_d, one_mul]
    exact hcong v hv
  have hn1 : n - 1 ∈ 𝔣 := by
    have : n - 1 = (n - d) + (d - 1) := by ring
    rw [this]; exact add_mem hnd1 hd1

  have hn0' : (algebraMap (𝓞 K) K) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0
  have hsgn : ∀ τ : K →+* ℝ, (0 < τ (algebraMap (𝓞 K) K n))
      ↔ (0 < τ (algebraMap (𝓞 K) K d)) := by
    intro τ
    have hτβ : 0 < τ (β : K) := hsign τ
    rw [show (algebraMap (𝓞 K) K) n = (algebraMap (𝓞 K) K) d * (β : K) from hn,
      map_mul]
    refine ⟨fun h => ?_, fun h => mul_pos h hτβ⟩
    exact ((mul_pos_iff.mp h).resolve_right fun ⟨_, hb⟩ => hb.not_gt hτβ).1

  set yn : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K n hn0, principalUnit_mem_coprimeToModulus K hn0 hn1⟩ with hyn_def
  set yd : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K d hd0, principalUnit_mem_coprimeToModulus K hd0 hd1⟩ with hyd_def
  have hyn_val : ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {n} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K n hn0
  have hyd_val : ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K d hd0

  have hyd2 : ((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hd0 hd1 hyd_val hd0 hd1 hyd_val
      fun _ => Iff.rfl)
  have hynyd : ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hn0 hn1 hyn_val hd0 hd1 hyd_val
      hsgn)

  have hβnd' : toPrincipalIdeal (𝓞 K) K β * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    refine Units.ext ?_
    rw [Units.val_mul, hyn_val, hyd_val, coe_toPrincipalIdeal,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm, hn]
  have hβnd : toPrincipalIdeal (𝓞 K) K β
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹ :=
    eq_mul_inv_of_mul_eq hβnd'

  rw [hβnd]
  have hrw : (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹
      = (((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
        * ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc,
      show ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
          * ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))
        = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) from by
          rw [mul_comm (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) _, ← mul_assoc, inv_mul_cancel,
            one_mul],
      mul_comm]
  rw [hrw]
  exact mul_mem (inv_mem hyd2) hynyd

private theorem mk_eq_mk_of_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') :
    NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩
      = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα'.coprime⟩ := by
  rw [NarrowRayClassGroup.mk_eq_mk_iff]
  show (fadContentHom K (projFin K _))⁻¹ * fadContentHom K (projFin K _) ∈ _
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, adj_adele_ratio K u α α',
    projFin_principal, fadContentHom_unitEmbedding]
  exact toPrincipalIdeal_mem_narrowRaySubgroup K h𝔣 (α * α'⁻¹)
    (fun v hv => valuation_ratio_sub_one_le K hα hα' v hv)
    (fun τ => ratio_totally_positive K hα hα' τ)

end StageC
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_IdeleContentBuild
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_MixedApprox

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain AbsoluteValue"

open Filter Topology

namespace NumberField
p2m_export "NumberField" "FinitePlace ComplexEmbedding.isReal_iff classNumber_pos FinitePlace.norm_lt_one_iff_mem FinitePlace.mk InfinitePlace.embedding_of_isReal_apply RingOfIntegers.mapRingHom InfinitePlace.map_natCast Units.rank mk InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe place FinitePlace.norm_eq_one_iff_notMem InfinitePlace.embedding_mk_eq_of_isReal InfinitePlace.mk AdeleRing.algebraMap_fst_apply InfinitePlace.Completion FinitePlace.norm_embedding InfinitePlace.embedding_of_isReal InfinitePlace.eq_iff_isEquiv RingOfIntegers mixedEmbedding RingOfIntegers.coe_injective HeightOneSpectrum.adicAbv_natCast_le_one Units.rank_modTorsion InfinitePlace.apply ComplexEmbedding.IsReal InfinitePlace Units.torsion AdeleRing FinitePlace.embedding_apply InfinitePlace.Completion.ringEquivRealOfIsReal_apply InfinitePlace.isNontrivial InfinitePlace.coe_apply RingOfIntegers.ext FinitePlace.embedding classNumber ComplexEmbedding.conjugate_coe_eq"
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

namespace FinitePlace p2m_export "NumberField.FinitePlace" "norm_lt_one_iff_mem mk coe_apply norm_eq_one_iff_notMem pos_iff norm_embedding embedding_apply embedding" end FinitePlace
namespace FinitePlace
p2m_open_scoped "NumberField.FinitePlace" in
private theorem _root_.NumberField.FinitePlace.isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (FinitePlace.mk v).1.IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ v.asIdeal, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr v.ne_bot)
    exact ⟨x, hx, fun h => hx0 (h ▸ Ideal.zero_mem _)⟩
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hx0
  · show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x) ≠ 1
    rw [show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x)
        = ‖FinitePlace.embedding v (algebraMap (𝓞 K) K x)‖ from rfl]
    exact ((FinitePlace.norm_lt_one_iff_mem K v x).mpr hx).ne

end FinitePlace
p2m_export "NumberField" "FinitePlace.isNontrivial"
p2m_open_scoped "NumberField.FinitePlace" in
private theorem FinitePlace.not_isEquiv_of_ne {v₁ v₂ : HeightOneSpectrum (𝓞 K)} (h : v₁ ≠ v₂) :
    ¬ (FinitePlace.mk v₁).1.IsEquiv (FinitePlace.mk v₂).1 := by
  rw [isEquiv_iff_lt_one_iff]
  push Not
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h (HeightOneSpectrum.ext_iff.mpr
      (Ideal.IsMaximal.eq_of_le (HeightOneSpectrum.isMaximal v₁) Ideal.IsPrime.ne_top' H))
  refine ⟨algebraMap (𝓞 K) K x, ?_⟩
  rw [show ((FinitePlace.mk v₁).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₁ y‖ from rfl,
    show ((FinitePlace.mk v₂).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₂ y‖ from rfl]
  simp only
  exact Or.inl ⟨(FinitePlace.norm_lt_one_iff_mem K v₁ x).mpr hx1,
    ((FinitePlace.norm_eq_one_iff_notMem K v₂ x).mpr hx2).ge⟩

namespace InfinitePlace p2m_export "NumberField.InfinitePlace" "embedding_of_isReal_apply IsReal smul_apply Completion.extensionEmbeddingOfIsReal_coe embedding_mk_eq_of_isReal mk Completion embedding_of_isReal eq_iff_isEquiv ext comap pos_iff isReal_iff apply embedding Completion.ringEquivRealOfIsReal_apply isNontrivial coe_apply" end InfinitePlace
p2m_open_scoped "NumberField.InfinitePlace" in
private theorem InfinitePlace.not_isEquiv_finitePlace (w : InfinitePlace K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ w.1.IsEquiv (FinitePlace.mk v).1 := by
  intro hequiv
  have hw2 : ¬ w.1 (2 : K) ≤ 1 := by
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [← InfinitePlace.coe_apply, this, InfinitePlace.map_natCast w 2]
    norm_num
  have hv2 : (FinitePlace.mk v).1 (2 : K) ≤ 1 := by
    show ‖FinitePlace.embedding v (2 : K)‖ ≤ 1
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [FinitePlace.norm_embedding, this]
    exact HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  exact hw2 (hequiv.le_one_iff.mpr hv2)

private noncomputable def mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ ↥S → AbsoluteValue K ℝ :=
  Sum.elim (·.1) (fun v => (FinitePlace.mk v.1).1)

private theorem mixedAbs_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : InfinitePlace K ⊕ ↥S) : (mixedAbs K S i).IsNontrivial := by
  rcases i with w | v
  · exact InfinitePlace.isNontrivial w
  · exact FinitePlace.isNontrivial K v.1

private theorem mixedAbs_pairwise_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise fun i j => ¬ (mixedAbs K S i).IsEquiv (mixedAbs K S j) := by
  intro i j hij
  match i, j with
  | Sum.inl w, Sum.inl w' =>
    exact (InfinitePlace.eq_iff_isEquiv (K := K)).not.mp (by simpa using hij)
  | Sum.inl w, Sum.inr v => exact InfinitePlace.not_isEquiv_finitePlace K w v.1
  | Sum.inr v, Sum.inl w =>
    exact fun h => InfinitePlace.not_isEquiv_finitePlace K w v.1 h.symm
  | Sum.inr v, Sum.inr v' =>
    exact FinitePlace.not_isEquiv_of_ne K (by simpa using hij)

private theorem denseRange_algebraMap_pi_mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (algebraMap K ((i : InfinitePlace K ⊕ ↥S) → WithAbs (mixedAbs K S i))) := by
  classical
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (mixedAbs_isNontrivial K S) (mixedAbs_pairwise_not_isEquiv K S)
  let y := fun n ↦
    ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (mixedAbs K S i) (z i)
  have htend : Filter.atTop.Tendsto
      (fun n i ↦ (WithAbs.equiv (mixedAbs K S i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have : mixedAbs K S u (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (mixedAbs K S i)) hw (z w)]
      have haw0 : a w ≠ 0 := fun ha => by
        have := (hx w).1; rw [ha, map_zero] at this; linarith
      have hu : 1 < mixedAbs K S u (a w)⁻¹ := by
        rw [map_inv₀, one_lt_inv_iff₀]
        exact ⟨(mixedAbs K S u).pos_iff.2 haw0, (hx w).2 u hw⟩
      have := (mixedAbs K S u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (mixedAbs K S u)).symm (WithAbs.equiv (mixedAbs K S w) (z w)))
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 htend r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

end NumberField
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_MixedApprox
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_ExistsAdjuster

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private theorem sign_eq_of_withAbs_dist_lt (τ : K →+* ℝ) (α t : K) (ht : t ≠ 0)
    (h : (placeOf K τ).1 (α - t) < (placeOf K τ).1 t) :
    (0 < τ α ↔ 0 < τ t) := by

  have hval : ∀ x : K, (placeOf K τ).1 x = |τ x| := by
    intro x
    rw [← InfinitePlace.coe_apply]
    show (InfinitePlace.mk (Complex.ofRealHom.comp τ)) x = |τ x|
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hval, hval, map_sub] at h

  have ht0 : τ t ≠ 0 := fun h0 => ht ((map_eq_zero τ).mp h0)
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · refine ⟨fun hα => absurd ?_ (not_lt.mpr hα.le), fun hα => absurd hα hneg.not_gt⟩
    calc τ α = τ t + (τ α - τ t) := by ring
      _ < 0 := by
        have := abs_lt.mp h
        linarith [abs_of_neg hneg ▸ this.2]
  · refine ⟨fun _ => hpos, fun _ => ?_⟩
    calc (0 : ℝ) < τ t - |τ α - τ t| := by linarith [abs_of_pos hpos ▸ h]
      _ ≤ τ t - (τ t - τ α) := by linarith [neg_abs_le (τ α - τ t)]
      _ = τ α := by ring

private noncomputable def primesOf (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot])).toFinset

private theorem mem_primesOf {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ primesOf K 𝔣 h𝔣 ↔ v.asIdeal ∣ 𝔣 :=
  Set.Finite.mem_toFinset _

private noncomputable def fadComp (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem fadComp_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    fadComp K u v ≠ 0 := by
  intro h
  exact valued_ne_zero_of_unit K (projFin K u) v (by rw [projFin_val, ← fadComp, h, map_zero])

private theorem archRealProjTau_principal (τ : K →+* ℝ) (α : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = τ (α : K) := by
  unfold archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_placeOf]
  rfl

private theorem exists_embedding_near_fadComp (u : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < ε := by
  obtain ⟨t, ht⟩ := Metric.denseRange_iff.mp (v.denseRange_algebraMap K) (fadComp K u v) ε hε
  exact ⟨t, by rw [FinitePlace.embedding_apply]; rwa [dist_comm, dist_eq_norm] at ht⟩

private theorem cong_of_completion_close {v : HeightOneSpectrum (𝓞 K)} {α : K} {U : v.adicCompletion K}
    (hU : U ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ‖FinitePlace.embedding v α - U‖ < ‖U‖ * δ) :
    ‖U * (FinitePlace.embedding v α)⁻¹‖ = 1 ∧
    ‖U * (FinitePlace.embedding v α)⁻¹ - 1‖ ≤ δ := by
  set αv := FinitePlace.embedding v α with hαv
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hlt : ‖αv - U‖ < ‖U‖ :=
    h.trans_le (by nlinarith)
  have hαeq : ‖αv‖ = ‖U‖ := by
    have hne : ‖U‖ ≠ ‖αv - U‖ := (hlt.trans_le (le_refl _)).ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := U) (y := αv - U) hne
    rw [add_sub_cancel, max_eq_left hlt.le] at this
    exact this
  have hα0 : αv ≠ 0 := fun h0 => by simp [h0] at hαeq; exact hU (norm_eq_zero.mp hαeq.symm)
  refine ⟨?_, ?_⟩
  · rw [norm_mul, norm_inv, hαeq, mul_inv_cancel₀ hUpos.ne']
  · have hfac : U * αv⁻¹ - 1 = (U - αv) * αv⁻¹ := by
      field_simp
    rw [hfac, norm_mul, norm_inv, hαeq, norm_sub_rev]
    calc ‖αv - U‖ * ‖U‖⁻¹ ≤ (‖U‖ * δ) * ‖U‖⁻¹ := by
          exact mul_le_mul_of_nonneg_right h.le (inv_nonneg.mpr hUpos.le)
      _ = δ := by field_simp

private theorem adjCompEq (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
      = fadComp K u v * (FinitePlace.embedding v (α : K))⁻¹ := by
  have hmul : ((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      = (u : AdeleRing (𝓞 K) K).2
        * (((Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
    rw [Units.val_mul]; rfl
  rw [hmul, fad_mul_apply K, ← fadComp]
  congr 1
  rw [← map_inv, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val,
    FinitePlace.embedding_apply]
  show ((algebraMap K (AdeleRing (𝓞 K) K)) ((α : K)⁻¹)).2 v = _
  rw [show ∀ x : K, ((algebraMap K (AdeleRing (𝓞 K) K)) x).2 v
      = algebraMap K (v.adicCompletion K) x from fun x => rfl,
    map_inv₀]
  rfl

private theorem valued_cong_of_norm_cong {v : HeightOneSpectrum (𝓞 K)} {X Y : v.adicCompletion K}
    (h1 : ‖X‖ = 1) (h2 : ‖X - 1‖ ≤ ‖Y‖) :
    Valued.v X = 1 ∧ Valued.v (X - 1) ≤ Valued.v Y := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact (Valued.toNormedField.norm_le_one_iff).mp h1.le
  · exact (Valued.toNormedField.one_le_norm_iff).mp h1.ge
  · exact (Valued.toNormedField.norm_le_iff).mp h2

private theorem exists_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by
  classical
  set S := primesOf K 𝔣 h𝔣 with hS

  obtain ⟨γ, hγ𝔣, hγ0⟩ : ∃ γ : 𝓞 K, γ ∈ 𝔣 ∧ γ ≠ 0 := by
    obtain ⟨γ, hγ𝔣, hγ0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr h𝔣)
    exact ⟨γ, hγ𝔣, fun h => hγ0 (h ▸ Ideal.zero_mem ⊥)⟩
  have hγK0 : (γ : K) ≠ 0 := by exact_mod_cast hγ0

  have hγemb_ne : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.embedding v (γ : K) ≠ 0 :=
    fun v => (map_ne_zero _).mpr hγK0
  have hγnorm_pos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖FinitePlace.embedding v (γ : K)‖ :=
    fun v => norm_pos_iff.mpr (hγemb_ne v)
  have hγnorm_le_one : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖FinitePlace.embedding v (γ : K)‖ ≤ 1 := by
    intro v
    rw [Valued.toNormedField.norm_le_one_iff,
      show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one γ
  have hγval_le : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (FinitePlace.embedding v (γ : K))
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
    intro v _
    rw [show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    refine (v.intValuation_le_pow_iff_dvd γ _).mpr
      (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hγ𝔣))))
    have h𝔣0 : (Associates.mk 𝔣) ≠ 0 :=
      Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
    have hirr := Associates.irreducible_mk.mpr v.irreducible
    have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr
        (k := idealMultiplicity K v 𝔣)).mpr le_rfl
    rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this

  have hUpos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖fadComp K u v‖ :=
    fun v => norm_pos_iff.mpr (fadComp_ne_zero K u v)

  set bnd : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ with hbnd
  have hbnd_pos : ∀ v, 0 < bnd v := fun v => mul_pos (hUpos v) (hγnorm_pos v)
  obtain ⟨r, hr0, hr1, hrS⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ v ∈ S, r < bnd v := by
    by_cases hne : S.Nonempty
    · have hm_pos : 0 < S.inf' hne bnd :=
        (Finset.lt_inf'_iff hne).mpr (fun v _ => hbnd_pos v)
      refine ⟨min (1/2) (S.inf' hne bnd / 2), ?_, ?_, ?_⟩
      · exact lt_min (by norm_num) (by linarith)
      · exact (min_le_left _ _).trans_lt (by norm_num)
      · intro v hv
        refine (min_le_right _ _).trans_lt ?_
        have hle := Finset.inf'_le bnd hv
        linarith [hbnd_pos v]
    · exact ⟨1/2, by norm_num, by norm_num, fun v hv => absurd ⟨v, hv⟩ hne⟩

  have htv : ∀ v ∈ S, ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < r :=
    fun v _ => exists_embedding_near_fadComp K u v hr0
  choose tv htv using htv

  set archTgt : InfinitePlace K → K := fun w =>
    if hw : w.IsReal then
      (if archSign K (InfinitePlace.embedding_of_isReal hw) u then (1:K) else (-1:K))
    else (1:K) with harchTgt
  have harchTgt_ne : ∀ w, archTgt w ≠ 0 := by
    intro w; unfold archTgt; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero
  have harchTgt_abs : ∀ w : InfinitePlace K, w (archTgt w) = 1 := by
    intro w; unfold archTgt; split_ifs
    · exact map_one _
    · exact (w.1.map_neg 1).trans (map_one _)
    · exact map_one _

  set z : InfinitePlace K ⊕ ↥S → K := Sum.elim archTgt (fun v => tv v.1 v.2) with hz

  obtain ⟨α, hα⟩ := Metric.denseRange_iff.mp
    (NumberField.denseRange_algebraMap_pi_mixedAbs K S)
    (fun i => (WithAbs.equiv (NumberField.mixedAbs K S i)).symm (z i)) r hr0
  have hα_at : ∀ i, (NumberField.mixedAbs K S i) (α - z i) < r := by
    intro i
    have hi := (dist_pi_lt_iff hr0).mp hα i
    rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hi
    convert hi using 2
    rfl

  have hα0 : α ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    intro h
    have := hα_at (Sum.inl w)
    simp only [hz, Sum.elim_inl, h, zero_sub] at this
    have heq : (NumberField.mixedAbs K S (Sum.inl w)) (-archTgt w) = 1 := by
      change (w.1 : AbsoluteValue K ℝ) (-archTgt w) = 1
      rw [(w.1).map_neg, ← InfinitePlace.coe_apply, harchTgt_abs w]
    rw [heq] at this; linarith
  refine ⟨Units.mk0 α hα0, ?_, ?_⟩
  ·
    intro v hv
    have hvS : v ∈ S := (mem_primesOf K h𝔣 v).mpr hv
    rw [adjCompEq K u (Units.mk0 α hα0) v, Units.val_mk0]

    have hstep : ‖FinitePlace.embedding v α - fadComp K u v‖
        < ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ := by
      have hα_fin := hα_at (Sum.inr ⟨v, hvS⟩)
      simp only [hz, Sum.elim_inr, NumberField.mixedAbs] at hα_fin

      have h1 : ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖ < r := by
        rw [← map_sub]; exact hα_fin
      have h2 := htv v hvS
      calc ‖FinitePlace.embedding v α - fadComp K u v‖
          ≤ max ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖
              ‖FinitePlace.embedding v (tv v hvS) - fadComp K u v‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact IsUltrametricDist.dist_triangle_max _ _ _
        _ < r := max_lt h1 h2
        _ < bnd v := hrS v hvS
    have hcong := cong_of_completion_close K (fadComp_ne_zero K u v)
      (hγnorm_pos v) (hγnorm_le_one v) hstep
    have hbr := valued_cong_of_norm_cong K hcong.1 hcong.2
    exact ⟨hbr.1, hbr.2.trans (hγval_le v hv)⟩
  ·
    intro τ
    rw [archSign_mul K τ, archSign_inv K τ]
    show archSign K τ u ↔ archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.mk0 α hα0))
    unfold archSign
    rw [archRealProjTau_principal K τ (Units.mk0 α hα0), Units.val_mk0]

    have hwτ := isReal_placeOf K τ
    have htgt_τ : archTgt (placeOf K τ)
        = if (0:ℝ) < archRealProjTau K τ u then (1:K) else (-1:K) := by
      unfold archTgt; rw [dif_pos hwτ]
      congr 1
      · unfold archSign
        rw [show InfinitePlace.embedding_of_isReal hwτ = τ from embedding_of_isReal_placeOf K τ]
    have habs_tgt : (placeOf K τ) (archTgt (placeOf K τ)) = 1 := harchTgt_abs _
    have hclose : (placeOf K τ) (α - archTgt (placeOf K τ)) < (placeOf K τ) (archTgt (placeOf K τ)) := by
      rw [habs_tgt]
      have := hα_at (Sum.inl (placeOf K τ))
      simp only [hz, Sum.elim_inl, NumberField.mixedAbs] at this
      exact this.trans hr1
    have hsign_iff := sign_eq_of_withAbs_dist_lt K τ α (archTgt (placeOf K τ))
      (harchTgt_ne _) hclose
    constructor
    · intro hpos
      refine hsign_iff.mpr ?_
      rw [htgt_τ, if_pos hpos, map_one]; exact one_pos
    · intro hτα
      by_contra hneg
      have hlt : (0:ℝ) < -1 := by
        have := hsign_iff.mp hτα
        rwa [htgt_τ, if_neg hneg, map_neg, map_one] at this
      linarith

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_ExistsAdjuster
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_IdeleContent

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply WithZero"

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private def ideleContentHom (𝔣 : Ideal (𝓞 K)) :
    (AdeleRing (𝓞 K) K)ˣ →* NarrowRayClassGroup K 𝔣 := by
  classical
  by_cases h𝔣 : 𝔣 = ⊥
  · exact 1
  · exact
      { toFun := fun u => NarrowRayClassGroup.mk K 𝔣
          ⟨_, (Classical.choose_spec (exists_isAdjuster K h𝔣 u)).coprime⟩
        map_one' := by
          rw [mk_eq_mk_of_isAdjuster K h𝔣
            (Classical.choose_spec (exists_isAdjuster K h𝔣 1)) (isAdjuster_one_one K 𝔣)]
          simp only [map_one, inv_one, mul_one]; rfl
        map_mul' := fun u u' => by
          have hαu := Classical.choose_spec (exists_isAdjuster K h𝔣 u)
          have hαu' := Classical.choose_spec (exists_isAdjuster K h𝔣 u')
          have hαuu' : IsAdjuster K 𝔣 (u * u') (_ * _) := IsAdjuster.mul K hαu hαu'
          rw [mk_eq_mk_of_isAdjuster K h𝔣
              (Classical.choose_spec (exists_isAdjuster K h𝔣 (u * u'))) hαuu',
            ← (NarrowRayClassGroup.mk K 𝔣).map_mul ⟨_, hαu.coprime⟩ ⟨_, hαu'.coprime⟩]
          refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
          show fadContentHom K (projFin K _) = fadContentHom K (projFin K _)
            * fadContentHom K (projFin K _)
          rw [← map_mul, ← map_mul, adj_adele_mul K u u'] }

private theorem ideleContentHom_apply {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ} (hα : IsAdjuster K 𝔣 u α) :
    ideleContentHom K 𝔣 u = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩ := by
  unfold ideleContentHom
  rw [dif_neg h𝔣]
  exact mk_eq_mk_of_isAdjuster K h𝔣 (Classical.choose_spec (exists_isAdjuster K h𝔣 u)) hα

private theorem ideleContentHom_principal (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    ideleContentHom K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = 1 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · unfold ideleContentHom; rw [dif_pos h𝔣]; rfl
  · rw [ideleContentHom_apply K h𝔣 (isAdjuster_principal_self K 𝔣 α)]
    have h1 : fadContentHom K (projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)) = 1 := by
      rw [mul_inv_cancel, map_one, map_one]
    rw [show (⟨_, (isAdjuster_principal_self K 𝔣 α).coprime⟩ : ↥(coprimeToModulus K 𝔣)) = 1
      from Subtype.ext h1, map_one]

private theorem ideleContentHom_uniformizerIdele_v2 (𝔣 : Ideal (𝓞 K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1)
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w) = 1)
    (huv : Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = WithZero.exp (-1 : ℤ))
    (hu𝔣 : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w - 1)
        ≤ WithZero.exp (-(idealMultiplicity K w 𝔣 : ℤ))) :
    ideleContentHom K 𝔣 u = primeClass K 𝔣 v hv := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣; simp only [show v.asIdeal ∣ (⊥ : Ideal (𝓞 K)) from ⟨0, (mul_zero _).symm⟩,
      not_true] at hv
  ·
    have hadj : IsAdjuster K 𝔣 u 1 := by
      refine ⟨fun w hw𝔣 => ?_, fun τ => ?_⟩
      · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
        show Valued.v (adjFinV K u 1 w) = 1 ∧ Valued.v (adjFinV K u 1 w - 1) ≤ _
        have hu1 : adjFinV K u 1 w = (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)
            w) := by unfold adjFinV; simp only [map_one, inv_one, mul_one]
        rw [hu1]
        exact ⟨huw w hwv, hu𝔣 w hw𝔣⟩
      · simp only [map_one, inv_one, mul_one]
        exact archSign_of_fst_eq_one K τ huarch
    rw [ideleContentHom_apply K h𝔣 hadj]

    refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
    show fadContentHom K (projFin K (u * (pK K 1)⁻¹)) = primeUnit K v
    rw [map_one, inv_one, mul_one, fadContentHom_apply]
    refine finprod_eq_single (fun w => primeUnit K w ^ placeOrd K (projFin K u) w) v
      ?_ |>.trans ?_
    · intro w hwv
      show primeUnit K w ^ placeOrd K (projFin K u) w = 1
      rw [show placeOrd K (projFin K u) w = 0 from
        (placeOrd_eq_zero_iff K (projFin K u) w).mpr (projFin_val K u ▸ huw w hwv), zpow_zero]
    · show primeUnit K v ^ placeOrd K (projFin K u) v = primeUnit K v
      rw [show placeOrd K (projFin K u) v = 1 from by
        unfold placeOrd; rw [projFin_val, huv, WithZero.log_exp, neg_neg], zpow_one]

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

end Fold_IdeleContent
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand"

section Fold_TestIndex

noncomputable section

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.HeckeCharacter"

open scoped nonZeroDivisors

namespace M4aKummer

variable (k : Type*) [Field k] [NumberField k]

variable (S' S : Finset (HeightOneSpectrum (𝓞 k)))

private def testQv (v : HeightOneSpectrum (𝓞 k)) : Type _ :=
  (v.adicCompletion k)ˣ ⧸
    (powMonoidHom 2 : (v.adicCompletion k)ˣ →* (v.adicCompletion k)ˣ).range

private def testQτ : Type := ℝˣ ⧸ Units.posSubgroup ℝ

private scoped instance (v : HeightOneSpectrum (𝓞 k)) : Group (testQv k v) :=
  inferInstanceAs (Group (_ ⧸ _))

private scoped instance : Group testQτ := inferInstanceAs (Group (_ ⧸ _))

end M4aKummer
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer"

end Fold_TestIndex
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer"

section Fold_RadicandBasis

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain"

noncomputable section

namespace M4aKummer
namespace RadicandBasis

variable (k : Type*) [Field k] [NumberField k] (S : Finset (HeightOneSpectrum (𝓞 k)))

private abbrev U : Subgroup kˣ := ((S : Set (HeightOneSpectrum (𝓞 k))).unit k)

private abbrev Sq : Subgroup ↥(U k S) := (powMonoidHom 2 : ↥(U k S) →* ↥(U k S)).range

private abbrev V : Type _ := ↥(U k S) ⧸ Sq k S

private theorem natCard_V : Nat.card (V k S) = 2 ^ (S.card + Units.rank k + 1) := by
  rw [M4aHerbrand.sUnit_card_quotient_sq k (S : Set (HeightOneSpectrum (𝓞 k)))]
  simp only [Nat.card_eq_fintype_card, Finset.coe_sort_coe, Fintype.card_coe]

private scoped instance : Finite (V k S) := Nat.finite_of_card_ne_zero (by rw [natCard_V]; positivity)

variable {k S}

end M4aKummer.RadicandBasis
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

end Fold_RadicandBasis
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

section Fold_SUnitCount

noncomputable section

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.HeckeCharacter"

namespace M4aKummer

variable (k : Type*) [Field k] [NumberField k]

variable (S : Finset (HeightOneSpectrum (𝓞 k)))

private scoped instance : Nontrivial (AdeleRing (𝓞 k) k) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace k))
  exact nontrivial_of_ne 1 0 fun h =>
    one_ne_zero (congrArg (fun x : AdeleRing (𝓞 k) k => x.1 v) h)

variable (S' : Finset (HeightOneSpectrum (𝓞 k)))

end M4aKummer
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

end Fold_SUnitCount
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

section Fold_RealSigns

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain NumberField.InfinitePlace P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField.InfinitePlace NumberField.mixedEmbedding"

open scoped nonZeroDivisors

noncomputable section

namespace M4aKummer
namespace RealSigns

section Form

variable {k : Type*} [Field k] [NumberField k]

private structure NormFormIn (𝔞 : Ideal (𝓞 k)) (p q : 𝓞 k) : Prop where
  hp : p - 1 ∈ 𝔞
  hq : q ∈ 𝔞

omit [NumberField k] in

private theorem NormFormIn.mul {𝔞 : Ideal (𝓞 k)} {b p₁ q₁ p₂ q₂ : 𝓞 k}
    (h₁ : NormFormIn 𝔞 p₁ q₁) (h₂ : NormFormIn 𝔞 p₂ q₂) :
    NormFormIn 𝔞 (p₁ * p₂ + b * q₁ * q₂) (p₁ * q₂ + p₂ * q₁) := by
  refine ⟨?_, 𝔞.add_mem (𝔞.mul_mem_left _ h₂.hq) (𝔞.mul_mem_left _ h₁.hq)⟩
  have : p₁ * p₂ + b * q₁ * q₂ - 1 = (p₁ - 1) * p₂ + (p₂ - 1) + b * q₁ * q₂ := by ring
  rw [this]
  exact 𝔞.add_mem (𝔞.add_mem (𝔞.mul_mem_right _ h₁.hp) h₂.hp) (𝔞.mul_mem_left _ h₂.hq)

end Form
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

end M4aKummer.RealSigns
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

end Fold_RealSigns
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

section Fold_ArtinFrob

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.unitIdeles"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.unitIdeles"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup unitIdeles"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain"

open scoped Pointwise

section Restrict

variable (K M M' : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field M'] [NumberField M']
  [Algebra K M] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M] [IsGalois K M']

private scoped instance : IsScalarTower (𝓞 K) (𝓞 M) (𝓞 M') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    refine RingOfIntegers.ext ?_
    show algebraMap K M' (x : K) = algebraMap M M' (algebraMap (𝓞 K) (𝓞 M) x : M)
    rw [show (algebraMap (𝓞 K) (𝓞 M) x : M) = algebraMap K M (x : K) from rfl, ← IsScalarTower.algebraMap_apply K M M']

end Restrict
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

end Fold_ArtinFrob
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

section Fold_ArtinReciprocity

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.unitIdeles"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.unitIdeles"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup unitIdeles"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply"

open scoped nonZeroDivisors IsMulCommutative

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem primeCarrier_mem (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    primeCarrier K 𝔣 v hv ∈ primeCarriers K 𝔣 :=
  ⟨v, hv, rfl⟩

open Classical in

private def carrierOrOne (v : HeightOneSpectrum (𝓞 K)) : ↥(coprimeToModulus K 𝔣) :=
  if hv : v.asIdeal ∣ 𝔣 then 1 else primeCarrier K 𝔣 v hv

private theorem carrierOrOne_mem_closure (v : HeightOneSpectrum (𝓞 K)) :
    carrierOrOne K 𝔣 v ∈ Subgroup.closure (primeCarriers K 𝔣) := by
  unfold carrierOrOne
  split_ifs with hv
  · exact one_mem _
  · exact Subgroup.subset_closure (primeCarrier_mem K 𝔣 v hv)

open Classical in

private theorem val_carrierOrOne_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (((carrierOrOne K 𝔣 v ^ n : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = if v.asIdeal ∣ 𝔣 then 1 else (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  unfold carrierOrOne
  split_ifs with hv
  · rw [OneMemClass.coe_one, Units.val_one, one_zpow]
  · rw [primeCarrier, primeUnit_val]

private theorem raySymbolHom_carrierOrOne (I : ↥(coprimeToModulus K 𝔣)) : raySymbolHom K 𝔣 (carrierOrOne K 𝔣) I = I := by
  apply Subtype.ext
  apply Units.ext
  rw [raySymbolHom_apply]
  unfold raySymbol
  have hfin := hasFiniteMulSupport_raySymbol_factors K (carrierOrOne K 𝔣)
    ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)

  let φ : ↥(coprimeToModulus K 𝔣) →* FractionalIdeal ((𝓞 K)⁰) K :=
    (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)).comp (coprimeToModulus K 𝔣).subtype
  show φ (∏ᶠ v, carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)) = φ I
  rw [MonoidHom.map_finprod φ hfin]
  conv_rhs => rw [show φ I = ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))]
  refine finprod_congr fun v => ?_
  rw [show φ (carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K))
      = (((carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
          : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    val_carrierOrOne_zpow]
  split_ifs with hv
  · rw [I.2 v hv, zpow_zero]
  · rfl

private theorem closure_primeCarriers_eq_top : Subgroup.closure (primeCarriers K 𝔣) = ⊤ := by
  rw [eq_top_iff]
  intro I _
  rw [← raySymbolHom_carrierOrOne K 𝔣 I, raySymbolHom_apply]
  unfold raySymbol
  exact finprod_induction (· ∈ Subgroup.closure (primeCarriers K 𝔣)) (one_mem _) (fun _ _ => mul_mem)
    fun v => zpow_mem (carrierOrOne_mem_closure K 𝔣 v) _

end Carriers
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

end Fold_ArtinReciprocity
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

section Fold_ICNNormUnit

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem fracRelNormUnit_primeUnit (w : HeightOneSpectrum (𝓞 E))
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal) :
    fracRelNormUnit k E (primeUnit E w)
      = primeUnit k 𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have heq : placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h𝔭w])
  show raySymbolUnitsHom E _ (primeUnit E w) = _
  rw [show raySymbolUnitsHom E _ (primeUnit E w)
        = raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
            FractionalIdeal ((𝓞 E)⁰) E) from rfl,
    raySymbol_primeUnit, heq]

private theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

private theorem fracRelNormUnit_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by
            rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (placeUnder' k E w).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (placeUnder' k E w).isPrime (placeUnder' k E w).ne_bot
  haveI : w.asIdeal.LiesOver (placeUnder' k E w).asIdeal :=
    ⟨(placeUnder'_asIdeal k E w).symm⟩
  rw [fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0,
    ← FractionalIdeal.coeIdeal_pow]
  rw [Ideal.inertiaDeg'_eq_inertiaDeg (p := (placeUnder' k E w).asIdeal) (q := w.asIdeal)]
  exact congrArg _
    (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (placeUnder' k E w).asIdeal).symm

private theorem fracRelNormUnit_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((fracRelNormUnit k E (FractionalIdeal.mk0 E I) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.relNorm (𝓞 k) (I : Ideal (𝓞 E)) : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  obtain ⟨J, hJ⟩ := I
  have hJ' : J ≠ ⊥ := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
  simp only at *
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ'
  | h₂ u hu =>
    obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
    rw [show FractionalIdeal.mk0 E (⟨(⊤ : Ideal (𝓞 E)), hJ⟩ : (Ideal (𝓞 E))⁰) = 1 from
        Units.ext (by rw [FractionalIdeal.coe_mk0, Units.val_one, FractionalIdeal.coeIdeal_top]),
      map_one, Units.val_one, ← Ideal.one_eq_top, map_one, Ideal.one_eq_top,
      FractionalIdeal.coeIdeal_top]
  | h₃ a p ha hp ih =>
    have ha' : a ≠ ⊥ := fun h => ha (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
    have hp_nz : p ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
      mem_nonZeroDivisors_of_ne_zero
        (fun h => hp.ne_zero (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm))
    have ha_nz : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hpw : (FractionalIdeal.mk0 E ⟨p, hp_nz⟩ : (FractionalIdeal ((𝓞 E)⁰) E)ˣ)
        = primeUnit E w := by
      unfold primeUnit; exact congrArg (FractionalIdeal.mk0 E) (Subtype.ext rfl)
    rw [show (⟨p * a, hJ⟩ : (Ideal (𝓞 E))⁰) = ⟨p, hp_nz⟩ * ⟨a, ha_nz⟩ from rfl,
      map_mul, map_mul (fracRelNormUnit k E), Units.val_mul, hpw,
      fracRelNormUnit_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

private theorem fracRelNormUnit_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    ((fracRelNormUnit k E (principalUnit E α hα) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.span {Algebra.intNorm (𝓞 k) (𝓞 E) α} : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl,
    fracRelNormUnit_mk0 k E, Ideal.relNorm_singleton]

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

end Fold_ICNNormUnit
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin"

section Fold_NormRayCompat

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField"

namespace M4aP2

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem prod_sub_one_mem {R : Type*} [CommRing R] (J : Ideal R)
    {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, f i - 1 ∈ J) :
    (∏ i ∈ s, f i) - 1 ∈ J := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]
    have h1 := h a (Finset.mem_cons_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_cons_of_mem hi)
    have hsplit : f a * ∏ i ∈ s, f i - 1 = f a * ((∏ i ∈ s, f i) - 1) + (f a - 1) := by ring
    rw [hsplit]
    exact J.add_mem (Ideal.mul_mem_left _ _ h2) h1

private abbrev NCl := ↥(IntermediateField.normalClosure k E (AlgebraicClosure k))

@[reducible] private noncomputable def algONcl : Algebra (𝓞 k) (𝓞 (NCl k E)) :=
  (RingOfIntegers.mapRingHom (algebraMap k (NCl k E))).toAlgebra

attribute [local instance] algONcl

omit [NumberField k] [NumberField E] in

private theorem algONcl_coe (x : 𝓞 k) :
    (algebraMap (𝓞 k) (𝓞 (NCl k E)) x : NCl k E) = algebraMap k (NCl k E) (x : k) := rfl

omit [NumberField k] [NumberField E] in

private theorem algONcl_injective :
    Function.Injective (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
  intro a b h
  have h1 : algebraMap k (NCl k E) (a : k) = algebraMap k (NCl k E) (b : k) := by
    rw [← algONcl_coe, ← algONcl_coe, h]
  exact FaithfulSMul.algebraMap_injective (𝓞 k) k ((algebraMap k (NCl k E)).injective h1)

private scoped instance : IsScalarTower ℤ (𝓞 k) (𝓞 (NCl k E)) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private scoped instance : Algebra.IsIntegral (𝓞 k) (𝓞 (NCl k E)) :=
  ⟨fun x => IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral x)⟩

private scoped instance : FaithfulSMul (𝓞 k) (𝓞 (NCl k E)) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algONcl_injective k E)

variable {k E}

private noncomputable def embO (σ : E →ₐ[k] AlgebraicClosure k) :
    𝓞 E →+* 𝓞 (NCl k E) :=
  RingOfIntegers.mapRingHom
    ((σ.codRestrict _ fun x => σ.fieldRange_le_normalClosure ⟨x, rfl⟩ :
      E →ₐ[k] NCl k E) : E →+* NCl k E)

omit [NumberField k] [NumberField E] in

private theorem embO_coe (σ : E →ₐ[k] AlgebraicClosure k) (x : 𝓞 E) :
    algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ x : 𝓞 (NCl k E)) : NCl k E)
    = σ (algebraMap (𝓞 E) E x) := rfl

omit [NumberField k] [NumberField E] in

private theorem embO_comp (σ : E →ₐ[k] AlgebraicClosure k) :
    (embO σ).comp (algebraMap (𝓞 k) (𝓞 E)) = algebraMap (𝓞 k) (𝓞 (NCl k E)) := by
  apply RingHom.ext
  intro x
  apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
  show (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
      E →ₐ[k] NCl k E) (algebraMap k E (x : k))
    = algebraMap k (NCl k E) (x : k)
  exact (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
    E →ₐ[k] NCl k E).commutes (x : k)

variable (k E)

private theorem intNorm_sub_one_mem_of_sub_one_mem (𝔠 : Ideal (𝓞 k)) (y : 𝓞 E)
    (hy : y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 E))) :
    Algebra.intNorm (𝓞 k) (𝓞 E) y - 1 ∈ 𝔠 := by
  classical
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E

  have hmem : ∀ σ : E →ₐ[k] AlgebraicClosure k,
      embO σ y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    intro σ
    have h1 : embO σ (y - 1) ∈ (𝔠.map (algebraMap (𝓞 k) (𝓞 E))).map (embO σ) :=
      Ideal.mem_map_of_mem (embO σ) hy
    rw [Ideal.map_map, embO_comp σ] at h1
    simpa [map_sub] using h1
  have hPsub : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y) - 1
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) :=
    prod_sub_one_mem _ _ _ fun σ _ => hmem σ

  have hPeq : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y)
      = algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
    apply RingHom.injective (algebraMap (NCl k E) (AlgebraicClosure k))
    rw [show ((algebraMap (𝓞 (NCl k E)) (NCl k E))
        (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y))
        = ∏ σ : E →ₐ[k] AlgebraicClosure k,
          ((embO σ y : 𝓞 (NCl k E)) : NCl k E) from map_prod _ _ _,
      map_prod]
    have hL : ∀ σ : E →ₐ[k] AlgebraicClosure k,
        algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ y : 𝓞 (NCl k E)) : NCl k E)
        = σ (algebraMap (𝓞 E) E y) := fun σ => embO_coe σ y
    rw [Finset.prod_congr rfl fun σ _ => hL σ]
    have hR : algebraMap (NCl k E) (AlgebraicClosure k)
        ((algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) : NCl k E))
        = algebraMap k (AlgebraicClosure k)
          (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
      rw [algONcl_coe]
      exact (IsScalarTower.algebraMap_apply k (NCl k E) (AlgebraicClosure k) _).symm
    rw [hR, Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact (Algebra.norm_eq_prod_embeddings (K := k) (L := E)
      (E := AlgebraicClosure k) _).symm

  have hfin : algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y - 1)
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    rw [map_sub, map_one, ← hPeq]
    exact hPsub
  haveI hTF : Module.IsTorsionFree (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFlat : Module.Flat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFF : Module.FaithfullyFlat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat
    (A := 𝓞 k) (B := 𝓞 (NCl k E)) 𝔠]
  exact Ideal.mem_comap.mpr hfin

private theorem intNorm_totPos_of_totPos (y : 𝓞 E) (hy0 : y ≠ 0)
    (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E y)) :
    ∀ τ' : k →+* ℝ, 0 < τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
  intro τ'
  classical
  letI : Algebra k ℂ := (Complex.ofRealHom.comp τ').toAlgebra
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E
  set yE : E := algebraMap (𝓞 E) E y with hyEdef
  have hyE0 : yE ≠ 0 := fun h =>
    hy0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h)
  have hσ0 : ∀ σ : E →ₐ[k] ℂ, σ yE ≠ 0 := fun σ h =>
    hyE0 ((map_eq_zero_iff _ (RingHom.injective (σ : E →+* ℂ))).mp h)
  have hstar_alg : ∀ c : k, (starRingEnd ℂ) (algebraMap k ℂ c) = algebraMap k ℂ c := fun c =>
    Complex.conj_ofReal _
  let conjA : (E →ₐ[k] ℂ) → (E →ₐ[k] ℂ) := fun σ =>
    { toRingHom := (starRingEnd ℂ).comp (σ : E →+* ℂ)
      commutes' := fun c => by
        show (starRingEnd ℂ) (σ (algebraMap k E c)) = algebraMap k ℂ c
        rw [σ.commutes]
        exact hstar_alg c }
  have hconjA_apply : ∀ (σ : E →ₐ[k] ℂ) (x : E), conjA σ x = (starRingEnd ℂ) (σ x) :=
    fun _ _ => rfl
  have hconjA_invol : ∀ σ, conjA (conjA σ) = σ := fun σ => AlgHom.ext fun x =>
    Complex.conj_conj (σ x)
  have hf_pair : ∀ σ : E →ₐ[k] ℂ,
      σ yE / (‖σ yE‖ : ℂ) * ((conjA σ) yE / (‖(conjA σ) yE‖ : ℂ)) = 1 := by
    intro σ
    have hz : σ yE ≠ 0 := hσ0 σ
    have hr0 : (‖σ yE‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hc : (conjA σ) yE = (starRingEnd ℂ) (σ yE) := rfl
    rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj', ← sq]
    exact div_self (pow_ne_zero 2 hr0)
  have hf_fixed : ∀ σ : E →ₐ[k] ℂ, σ yE / (‖σ yE‖ : ℂ) ≠ 1 → conjA σ ≠ σ := by
    intro σ hf1 heq
    apply hf1
    have hreal : NumberField.ComplexEmbedding.IsReal (σ : E →+* ℂ) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      have h1 := congrArg (fun ψ : E →ₐ[k] ℂ => ψ x) heq
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq, hconjA_apply] using h1
    have hτpos := hpos hreal.embedding
    have hval : σ yE = ((hreal.embedding yE : ℝ) : ℂ) := (hreal.coe_embedding_apply yE).symm
    rw [hval, Complex.norm_real, Real.norm_of_nonneg hτpos.le]
    exact div_self (Complex.ofReal_ne_zero.mpr hτpos.ne')
  have hprod1 : ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ)) = 1 :=
    Finset.prod_involution (fun σ _ => conjA σ) (fun σ _ => hf_pair σ)
      (fun σ _ h => hf_fixed σ h) (fun σ _ => Finset.mem_univ _) (fun σ _ => hconjA_invol σ)
  have hsplit : ∀ σ : E →ₐ[k] ℂ, σ yE = σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ) := fun σ =>
    (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (hσ0 σ)))).symm
  have hprodR : ∏ σ : E →ₐ[k] ℂ, σ yE = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    calc ∏ σ : E →ₐ[k] ℂ, σ yE
        = ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ)) :=
          Finset.prod_congr rfl fun σ _ => hsplit σ
      _ = (∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ))) * ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) :=
          Finset.prod_mul_distrib
      _ = ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) := by rw [hprod1, one_mul]
  have hbridge : algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y))
      = ∏ σ : E →ₐ[k] ℂ, σ yE := by
    rw [Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact Algebra.norm_eq_prod_embeddings (K := k) (L := E) (E := ℂ) yE
  have hfinal : ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
      = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [show ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
        = algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) from rfl,
      hbridge, hprodR]
  have hval := Complex.ofReal_injective hfinal
  rw [hval]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hσ0 σ)

end M4aP2
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_NormRayCompat
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Fold_ICNRelNormRCG

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

open scoped Classical in

private def fNC2 (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) : NarrowRayClassGroup k 𝔠 :=
  if h : ¬ (placeUnder' k E w).asIdeal ∣ 𝔠
  then primeClass k 𝔠 (placeUnder' k E w) h ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)
  else 1

omit [NumberField E] in

private theorem fNC2_eq_mk_gcop (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) :
    fNC2 k E 𝔠 w = NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 w) := by
  classical
  unfold fNC2 gcopNC2
  split
  · simp only [primeClass, ← map_pow]; rfl
  · rw [map_one]

private theorem coe_raySymbol_gcop_eq_fracRelNormUnit {𝔠 : Ideal (𝓞 k)} (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) :
    ((raySymbol E (gcopNC2 k E 𝔠)
        ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
      : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (principalUnit E α hα0) := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
  have hfRN : fracRelNormUnit k E (principalUnit E α hα0)
      = raySymbol E
          (fun w => primeUnit k (placeUnder' k E w)
            ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)) J := by
    show raySymbol E _ ((principalUnit E α hα0 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
        FractionalIdeal ((𝓞 E)⁰) E) = _
    exact congrArg _ (principalUnit_val E α hα0)
  rw [hfRN]
  unfold raySymbol
  refine ((MonoidHom.map_finprod ((coprimeToModulus k 𝔠).subtype)
    (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J))).trans ?_
  refine finprod_congr (fun w => ?_)
  rw [map_zpow, Subgroup.coe_subtype]
  classical
  by_cases hw : (placeUnder' k E w).asIdeal ∣ 𝔠
  ·
    have hct : FractionalIdeal.count E w J = 0 :=
      count_span_singleton_eq_zero_of_sub_one_mem E hα0 hα1
        ((placeUnder'_dvd_iff k E 𝔠 w).mp hw)
    rw [hct]; simp
  ·
    simp only [gcopNC2]
    rw [dif_pos hw]

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_hkill (𝔠 : Ideal (𝓞 k)) (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E α)) :
    raySymbol E (fNC2 k E 𝔠)
      ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) = 1 := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]

  apply NarrowRayClassGroup.mk_eq_one_of_mem

  rw [coe_raySymbol_gcop_eq_fracRelNormUnit k E α hα0 hα1]

  apply Subgroup.subset_closure
  rw [mem_narrowRaySet_iff]
  exact ⟨Algebra.intNorm (𝓞 k) (𝓞 E) α, intNorm_ne_zero k E hα0,
    M4aP2.intNorm_sub_one_mem_of_sub_one_mem k E 𝔠 α hα1,
    M4aP2.intNorm_totPos_of_totPos k E α hα0 hpos,
    fracRelNormUnit_principalUnit k E α hα0⟩

private def relNormRCG (𝔠 : Ideal (𝓞 k)) :
    NarrowRayClassGroup E (modulusExt k E 𝔠) →* NarrowRayClassGroup k 𝔠 :=
  raySymbolDescend E (fNC2 k E 𝔠)
    (fun α hα0 hα1 hpos => relNormRCG_hkill k E 𝔠 α hα0 hα1 hpos)

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_ICNRelNormRCG
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Fold_ICNIdeleNorm

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

omit [NumberField k] [NumberField E] in

private theorem modulusExt_ne_bot {𝔠 : Ideal (𝓞 k)} (h𝔠 : 𝔠 ≠ ⊥) : modulusExt k E 𝔠 ≠ ⊥ := by
  intro h
  exact h𝔠 ((Ideal.map_eq_bot_iff_of_injective
    (f := algebraMap (𝓞 k) (𝓞 E)) (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E))).mp h)

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_mk (𝔠 : Ideal (𝓞 k)) (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y)
      = NarrowRayClassGroup.mk k 𝔠
          ⟨fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ),
            fracRelNormUnit_mem_coprimeToModulus k E Y.2⟩ := by
  rw [relNormRCG, raySymbolDescend_mk]

  rw [raySymbolHom_apply]
  set J := ((Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]
  exact congrArg _ (Subtype.ext (coe_raySymbol_gcop_eq_fracRelNormUnit' k E _ Y.2))

private theorem fracRelNormUnit_principalUnit' (a : 𝓞 E) (ha : a ≠ 0) :
    fracRelNormUnit k E (principalUnit E a ha)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) a) (intNorm_ne_zero k E ha) :=
  Units.ext ((fracRelNormUnit_principalUnit k E a ha).trans
    (principalUnit_val k _ (intNorm_ne_zero k E ha)).symm)

private theorem toPrincipalIdeal_algebraMap (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          (fun h => ha (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) h)))
      = principalUnit K a ha :=
  Units.ext <| by
    rw [coe_toPrincipalIdeal, Units.val_mk0, principalUnit_val,
      FractionalIdeal.coeIdeal_span_singleton]

private theorem fracRelNormUnit_toPrincipalIdeal (α : Eˣ) :
    fracRelNormUnit k E (toPrincipalIdeal (𝓞 E) E α)
      = toPrincipalIdeal (𝓞 k) k (Units.map (Algebra.norm k) α) := by

  obtain ⟨x, y, hy, hαxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (α : E)
  have hy0 : (y : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨y, hy⟩
  have hey : (algebraMap (𝓞 E) E) y ≠ 0 := fun h => hy0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)
  have hx0 : x ≠ 0 := by
    intro h; subst h
    exact α.ne_zero (hαxy.symm.trans (by simp))
  have hex : (algebraMap (𝓞 E) E) x ≠ 0 := fun h => hx0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)

  have hα_dec : α = Units.mk0 _ hex / Units.mk0 _ hey :=
    Units.ext (by rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, ← hαxy])
  rw [hα_dec]
  simp only [map_div]

  rw [toPrincipalIdeal_algebraMap E x hx0, toPrincipalIdeal_algebraMap E y hy0,
    fracRelNormUnit_principalUnit' k E x hx0, fracRelNormUnit_principalUnit' k E y hy0]
  congr 1 <;>
    · rw [← toPrincipalIdeal_algebraMap k]
      exact congrArg _ (Units.ext (by
        simp only [Units.coe_map, Units.val_mk0]
        exact Algebra.algebraMap_intNorm (K := k) (L := E) _))

private theorem ideleContentHom_comp_ideleNorm (𝔠 : Ideal (𝓞 k)) (h𝔠 : 𝔠 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 k) k)ˣ)
    (hNrm_adjuster : ∀ {u : (AdeleRing (𝓞 E) E)ˣ} {α : Eˣ},
      IsAdjuster E (modulusExt k E 𝔠) u α →
      IsAdjuster k 𝔠 (Nrm u) (Units.map (Algebra.norm k) α))
    (hNrm_fadContent : ∀ u : (AdeleRing (𝓞 E) E)ˣ,
      fadContentHom k (projFin k (Nrm u)) = fracRelNormUnit k E (fadContentHom E (projFin E u))) :
    (ideleContentHom k 𝔠).comp Nrm
      = (relNormRCG k E 𝔠).comp (ideleContentHom E (modulusExt k E 𝔠)) := by
  ext u
  have h𝔠E := modulusExt_ne_bot k E h𝔠
  obtain ⟨α, hα⟩ := exists_isAdjuster E h𝔠E u
  have hNα := hNrm_adjuster hα
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    ideleContentHom_apply k h𝔠 hNα, ideleContentHom_apply E h𝔠E hα,
    relNormRCG_mk k E 𝔠]

  congr 1
  apply Subtype.ext
  show fadContentHom k (projFin k _) = fracRelNormUnit k E (fadContentHom E (projFin E _))
  simp only [map_mul, map_inv]
  rw [hNrm_fadContent u]
  congr 1
  rw [projFin_principal, projFin_principal, fadContentHom_unitEmbedding,
    fadContentHom_unitEmbedding, fracRelNormUnit_toPrincipalIdeal]

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_ICNIdeleNorm
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Fold_RelNormCTM

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem mk_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    NarrowRayClassGroup.mk k 𝔠 (relNormCTM k E 𝔠 Y)
      = relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y) :=
  (relNormRCG_mk k E 𝔠 Y).symm

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_RelNormCTM
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Fold_CSdictTransfer

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.unitIdeles"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.unitIdeles"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup unitIdeles"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Square

variable {I I' R R' : Type*} [Group I] [Group I'] [Group R] [Group R']

private theorem sup_range_eq_comap_range (C : I →* R) (C' : I' →* R') (Nrm : I' →* I) (n : R' →* R) (P : Subgroup I)
    (hsq : C.comp Nrm = n.comp C') (hC' : Function.Surjective C') (hker : C.ker ≤ P ⊔ Nrm.range) (hP : P ≤ C.ker) :
    P ⊔ Nrm.range = n.range.comap C := by
  apply le_antisymm
  · refine sup_le (fun p hp => ?_) ?_
    · rw [Subgroup.mem_comap, show C p = 1 from hP hp]
      exact one_mem _
    · rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_comap, ← MonoidHom.comp_apply, hsq, MonoidHom.comp_apply]
      exact ⟨C' x, rfl⟩
  · intro u hu
    rw [Subgroup.mem_comap] at hu
    obtain ⟨r', hr'⟩ := hu
    obtain ⟨x, rfl⟩ := hC' r'
    have hx : C (Nrm x) = C u := by rw [← MonoidHom.comp_apply, hsq, MonoidHom.comp_apply, hr']
    have hk : u * (Nrm x)⁻¹ ∈ C.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
    have hmem : u * (Nrm x)⁻¹ * Nrm x ∈ P ⊔ Nrm.range := mul_mem (hker hk) (Subgroup.mem_sup_right ⟨x, rfl⟩)
    rwa [inv_mul_cancel_right] at hmem

private theorem index_sup_range_eq (C : I →* R) (C' : I' →* R') (Nrm : I' →* I) (n : R' →* R) (P : Subgroup I)
    (hsq : C.comp Nrm = n.comp C') (hC : Function.Surjective C) (hC' : Function.Surjective C')
    (hker : C.ker ≤ P ⊔ Nrm.range) (hP : P ≤ C.ker) :
    (P ⊔ Nrm.range).index = n.range.index := by
  rw [sup_range_eq_comap_range C C' Nrm n P hsq hC' hker hP]
  exact (n.range).index_comap_of_surjective hC

end Square
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section IdealSide

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem normRaySubgroup_eq_comap (𝔣 : Ideal (𝓞 K)) :
    normRaySubgroup K L 𝔣 = (relNormRCG K L 𝔣).range.comap (NarrowRayClassGroup.mk K 𝔣) := by
  refine sup_range_eq_comap_range (NarrowRayClassGroup.mk K 𝔣) (NarrowRayClassGroup.mk L (modulusExt K L 𝔣))
    (relNormCTM K L 𝔣) (relNormRCG K L 𝔣) _ (MonoidHom.ext fun Y => mk_relNormCTM K L Y) (QuotientGroup.mk'_surjective _)
    (fun x hx => Subgroup.mem_sup_left ?_) (fun x hx => ?_)
  · rwa [MonoidHom.mem_ker, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  · rw [MonoidHom.mem_ker, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx

private theorem normRaySubgroup_index_eq_index_range_relNormRCG (𝔣 : Ideal (𝓞 K)) :
    (normRaySubgroup K L 𝔣).index = (relNormRCG K L 𝔣).range.index := by
  rw [normRaySubgroup_eq_comap]
  exact ((relNormRCG K L 𝔣).range).index_comap_of_surjective (QuotientGroup.mk'_surjective _)

end IdealSide
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section IdeleSide

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private abbrev _root_.LanglandsTunnell.P2.Artin.principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range

p2m_export "LanglandsTunnell.P2.Artin" "principalIdeles"
private theorem normRaySubgroup_index_eq_idele_index (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hNrm_adjuster : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hNrm_fadContent : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hsurjK : Function.Surjective (ideleContentHom K 𝔣))
    (hsurjL : Function.Surjective (ideleContentHom L (modulusExt K L 𝔣)))
    (hkerK : (ideleContentHom K 𝔣).ker ≤ principalIdeles K ⊔ Nrm.range) :
    (normRaySubgroup K L 𝔣).index = (principalIdeles K ⊔ Nrm.range).index := by
  rw [normRaySubgroup_index_eq_index_range_relNormRCG,
    index_sup_range_eq (ideleContentHom K 𝔣) (ideleContentHom L (modulusExt K L 𝔣)) Nrm (relNormRCG K L 𝔣) (principalIdeles K)
      (ideleContentHom_comp_ideleNorm K L 𝔣 h𝔣 Nrm hNrm_adjuster hNrm_fadContent) hsurjK hsurjL hkerK ?_]
  intro u hu
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hu
  rw [MonoidHom.mem_ker]
  exact ideleContentHom_principal K 𝔣 α

end IdeleSide
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_CSdictTransfer
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Fold_CSdictBsurj

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.unitIdeles"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.unitIdeles"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup unitIdeles"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.HeckeCharacter WithZero"

open scoped nonZeroDivisors

section Uniformizer

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def unifAt : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_unifAt : Valued.v (unifAt K v) = exp (-1 : ℤ) := by
  unfold unifAt
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem unifAt_ne_zero : unifAt K v ≠ 0 := fun h => by
  have h1 := valued_unifAt K v
  rw [h, map_zero] at h1
  exact exp_ne_zero h1.symm

private theorem isUnit_mulSingle (x : v.adicCompletion K) (hx : x ≠ 0) [DecidableEq (HeightOneSpectrum (𝓞 K))] :
    IsUnit (show FiniteAdeleRing (𝓞 K) K from
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x) := by
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun w => ?_, ?_⟩
  · show Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w ≠ 0
    by_cases h : w = v
    · subst h; rw [Pi.mulSingle_eq_same]; exact hx
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_ne_zero
  · filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) ∈ Filter.cofinite by simp] with w hw
    show Valued.v (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w) = 1
    rw [Pi.mulSingle_eq_of_ne (by simpa using hw), map_one]

open scoped Classical in

private noncomputable def uniformizerFad : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (isUnit_mulSingle K v (unifAt K v) (unifAt_ne_zero K v)).unit

open scoped Classical in

private theorem uniformizerFad_apply (w : HeightOneSpectrum (𝓞 K)) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
      Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v (unifAt K v) w := by
  unfold uniformizerFad
  rw [IsUnit.unit_spec]
  rfl

open scoped Classical in

private theorem uniformizerFad_apply_self :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = unifAt K v := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_same]

open scoped Classical in

private theorem uniformizerFad_apply_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1 := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_of_ne hw]

private noncomputable def uniformizerIdele : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (uniformizerFad K v : FiniteAdeleRing (𝓞 K) K))
  inv := (1, ((uniformizerFad K v)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ))
  val_inv := Prod.ext (one_mul 1) (uniformizerFad K v).mul_inv
  inv_val := Prod.ext (one_mul 1) (uniformizerFad K v).inv_mul

private theorem uniformizerIdele_snd :
    ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = uniformizerFad K v := rfl

private theorem ideleContentHom_uniformizerIdele (𝔣 : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    ideleContentHom K 𝔣 (uniformizerIdele K v) = primeClass K 𝔣 v hv := by
  refine ideleContentHom_uniformizerIdele_v2 K 𝔣 hv (uniformizerIdele K v) rfl (fun w hw => ?_) ?_ (fun w hw𝔣 => ?_)
  · rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hw, map_one]
  · rw [uniformizerIdele_snd, uniformizerFad_apply_self, valued_unifAt]
  · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
    rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hwv, sub_self, map_zero]
    exact zero_le'

end Uniformizer
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Surj

variable (K : Type*) [Field K] [NumberField K]

private theorem ideleContentHom_surjective (𝔣 : Ideal (𝓞 K)) : Function.Surjective (ideleContentHom K 𝔣) := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hc : c ∈ (⊤ : Subgroup ↥(coprimeToModulus K 𝔣)) := Subgroup.mem_top c
  rw [← closure_primeCarriers_eq_top K 𝔣] at hc
  refine Subgroup.closure_induction (p := fun c _ => ∃ u, ideleContentHom K 𝔣 u = QuotientGroup.mk' _ c)
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨uniformizerIdele K w, ideleContentHom_uniformizerIdele K w 𝔣 hw⟩
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro a b _ _ ⟨u, hu⟩ ⟨u', hu'⟩
    exact ⟨u * u', by rw [map_mul, map_mul, hu, hu']⟩
  · rintro a _ ⟨u, hu⟩
    exact ⟨u⁻¹, by rw [map_inv, map_inv, hu]⟩

end Surj
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_CSdictBsurj
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Fold_CSdictBker

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.unitIdeles"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.unitIdeles"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup unitIdeles"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.HeckeCharacter WithZero"

open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

local notation "pK" => Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)

section RayUnit

variable (𝔣 : Ideal (𝓞 K))

private def IsRayUnit (β : Kˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ exp (-(idealMultiplicity K v 𝔣 : ℤ))) ∧
    ∀ τ : K →+* ℝ, 0 < τ (β : K)

variable {K 𝔣}

private theorem IsRayUnit.valuation_eq_one (h𝔣 : 𝔣 ≠ ⊥) {β : Kˣ} (h : IsRayUnit K 𝔣 β)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) : v.valuation K (β : K) = 1 :=
  valuation_eq_one_of_cong K h𝔣 h.1 v hv

private theorem isRayUnit_one : IsRayUnit K 𝔣 1 :=
  ⟨fun v _ => by rw [Units.val_one, sub_self, map_zero]; exact zero_le', fun τ => by rw [Units.val_one, map_one]; exact one_pos⟩

private theorem IsRayUnit.mul (h𝔣 : 𝔣 ≠ ⊥) {β β' : Kˣ} (h : IsRayUnit K 𝔣 β) (h' : IsRayUnit K 𝔣 β') : IsRayUnit K 𝔣 (β * β') := by
  refine ⟨fun v hv => ?_, fun τ => by rw [Units.val_mul, map_mul]; exact mul_pos (h.2 τ) (h'.2 τ)⟩
  have heq : ((β * β' : Kˣ) : K) - 1 = (β : K) * ((β' : K) - 1) + ((β : K) - 1) := by push_cast; ring
  rw [heq]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (h.1 v hv))
  rw [map_mul, h.valuation_eq_one h𝔣 v hv, one_mul]
  exact h'.1 v hv

private theorem IsRayUnit.inv (h𝔣 : 𝔣 ≠ ⊥) {β : Kˣ} (h : IsRayUnit K 𝔣 β) : IsRayUnit K 𝔣 β⁻¹ := by
  refine ⟨fun v hv => ?_, fun τ => by rw [Units.val_inv_eq_inv_val, map_inv₀]; exact inv_pos.mpr (h.2 τ)⟩
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  have heq : ((β⁻¹ : Kˣ) : K) - 1 = -(β : K)⁻¹ * ((β : K) - 1) := by
    rw [Units.val_inv_eq_inv_val]; field_simp; ring
  rw [heq, map_mul, Valuation.map_neg, map_inv₀, h.valuation_eq_one h𝔣 v hv, inv_one, one_mul]
  exact h.1 v hv

variable (K 𝔣)

private theorem exists_isRayUnit_of_mem_narrowRaySubgroup (h𝔣 : 𝔣 ≠ ⊥) {I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ}
    (hI : I ∈ narrowRaySubgroup K 𝔣) : ∃ β : Kˣ, IsRayUnit K 𝔣 β ∧ I = toPrincipalIdeal (𝓞 K) K β := by
  refine Subgroup.closure_induction (p := fun I _ => ∃ β : Kˣ, IsRayUnit K 𝔣 β ∧ I = toPrincipalIdeal (𝓞 K) K β)
    ?_ ?_ ?_ ?_ hI
  · rintro I ⟨α, hα0, hα𝔣, hpos, hIα⟩
    have hα0' : (algebraMap (𝓞 K) K α) ≠ 0 := fun h => hα0 ((map_eq_zero_iff _ (RingOfIntegers.coe_injective)).mp h)
    refine ⟨Units.mk0 _ hα0', ⟨fun v hv => ?_, fun τ => hpos τ⟩, Units.ext ?_⟩
    · rw [Units.val_mk0, show algebraMap (𝓞 K) K α - 1 = algebraMap (𝓞 K) K (α - 1) by rw [map_sub, map_one],
        HeightOneSpectrum.valuation_of_algebraMap]
      refine (v.intValuation_le_pow_iff_dvd (α - 1) _).mpr
        (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hα𝔣))))
      have h𝔣0 : (Associates.mk 𝔣) ≠ 0 := Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
      have hirr := Associates.irreducible_mk.mpr v.irreducible
      have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr (k := idealMultiplicity K v 𝔣)).mpr le_rfl
      rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this
    · rw [hIα, coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coeIdeal_span_singleton]
  · exact ⟨1, isRayUnit_one, by rw [map_one]⟩
  · rintro I J _ _ ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
    exact ⟨β * β', hβ.mul h𝔣 hβ', by rw [map_mul]⟩
  · rintro I _ ⟨β, hβ, rfl⟩
    exact ⟨β⁻¹, hβ.inv h𝔣, by rw [map_inv]⟩

end RayUnit
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section UnitIdeles

variable (𝔣 : Ideal (𝓞 K))

private theorem adele_snd_apply (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v := by
  rw [projFin_val]

variable {K 𝔣}

variable (K 𝔣)

private theorem isAdjuster_one_of_mem_unitIdeles {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ unitIdeles K 𝔣) : IsAdjuster K 𝔣 u 1 := by
  refine ⟨fun v hv => ?_, fun τ => ?_⟩
  · rw [map_one, inv_one, mul_one, adele_snd_apply]
    exact ⟨hu.1 v, hu.2.1 v hv⟩
  · rw [map_one, inv_one, mul_one]; exact hu.2.2 τ

private theorem fadContentHom_projFin_eq_one_of_mem_unitIdeles {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ unitIdeles K 𝔣) :
    fadContentHom K (projFin K u) = 1 := by
  rw [fadContentHom_apply]
  exact finprod_eq_one_of_forall_eq_one fun v => by rw [(placeOrd_eq_zero_iff K _ v).mpr (hu.1 v), zpow_zero]

private theorem unitIdeles_le_ker (h𝔣 : 𝔣 ≠ ⊥) : unitIdeles K 𝔣 ≤ (ideleContentHom K 𝔣).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, ideleContentHom_apply K h𝔣 (isAdjuster_one_of_mem_unitIdeles K 𝔣 hu)]
  refine NarrowRayClassGroup.mk_eq_one_of_mem K ?_
  have h1 : fadContentHom K (projFin K (u * (pK 1)⁻¹)) = 1 := by
    rw [map_one, inv_one, mul_one]; exact fadContentHom_projFin_eq_one_of_mem_unitIdeles K 𝔣 hu
  show fadContentHom K (projFin K (u * (pK 1)⁻¹)) ∈ narrowRaySubgroup K 𝔣
  rw [h1]; exact one_mem _

private theorem principalIdeles_le_ker : principalIdeles K ≤ (ideleContentHom K 𝔣).ker := by
  rintro _ ⟨α, rfl⟩
  rw [MonoidHom.mem_ker]
  exact ideleContentHom_principal K 𝔣 α

end UnitIdeles
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Ker

variable (𝔣 : Ideal (𝓞 K))

private theorem coe_sub_one_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (((x - 1 : K)) : v.adicCompletion K) = (x : v.adicCompletion K) - 1 := by
  have h := map_sub (algebraMap K (v.adicCompletion K)) x 1
  rw [map_one] at h
  exact h

private theorem valued_eq_of_fadContentHom_eq {X Y : (FiniteAdeleRing (𝓞 K) K)ˣ} (h : fadContentHom K X = fadContentHom K Y)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((X : FiniteAdeleRing (𝓞 K) K) v) = Valued.v ((Y : FiniteAdeleRing (𝓞 K) K) v) := by
  have hc := congrArg (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ => FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) h
  simp only [count_fadContentHom] at hc
  unfold placeOrd at hc
  rw [neg_inj] at hc
  rw [← exp_log (valued_ne_zero_of_unit K X v), ← exp_log (valued_ne_zero_of_unit K Y v), hc]

private theorem ker_ideleContentHom_eq (h𝔣 : 𝔣 ≠ ⊥) :
    (ideleContentHom K 𝔣).ker = principalIdeles K ⊔ unitIdeles K 𝔣 := by
  refine le_antisymm (fun u hu => ?_) (sup_le (principalIdeles_le_ker K 𝔣) (unitIdeles_le_ker K 𝔣 h𝔣))
  obtain ⟨α, hα⟩ := exists_isAdjuster K h𝔣 u
  rw [MonoidHom.mem_ker, ideleContentHom_apply K h𝔣 hα, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hu
  obtain ⟨β, hβ, hcβ⟩ := exists_isRayUnit_of_mem_narrowRaySubgroup K 𝔣 h𝔣 hu

  have hcont : fadContentHom K (projFin K (u * (pK α)⁻¹)) = fadContentHom K (projFin K (pK β)) := by
    rw [projFin_principal, fadContentHom_unitEmbedding]; exact hcβ
  set w : (AdeleRing (𝓞 K) K)ˣ := u * (pK α)⁻¹ * (pK β)⁻¹ with hw
  have hw_mem : w ∈ unitIdeles K 𝔣 := by
    have hval : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((projFin K (u * (pK α)⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) =
          Valued.v (((projFin K (pK β) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) :=
      valued_eq_of_fadContentHom_eq K hcont
    have hβv : ∀ v : HeightOneSpectrum (𝓞 K),
        ((projFin K (pK β) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = ((β : K) : v.adicCompletion K) := by
      intro v; rw [projFin_principal]; rfl
    have hβ1 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → Valued.v (((β : K) : v.adicCompletion K)) = 1 := by
      intro v hv; rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hβ.valuation_eq_one h𝔣 v hv
    have hβc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v (((β : K) : v.adicCompletion K) - 1) ≤ exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
      intro v hv
      rw [← coe_sub_one_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hβ.1 v hv
    have hβ0 : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((β : K) : v.adicCompletion K)) ≠ 0 := by
      intro v; rw [← hβv]; exact valued_ne_zero_of_unit K _ v
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => ?_⟩
    · rw [hw, map_mul, Units.val_mul, fad_mul_apply, map_mul, map_inv, fad_units_inv_apply, map_inv₀, hval v, hβv,
        mul_inv_cancel₀ (hβ0 v)]
    · rw [hw, map_mul, Units.val_mul, fad_mul_apply, map_inv, fad_units_inv_apply, hβv]
      have hca := (hα.cong v hv).2
      rw [adele_snd_apply] at hca
      exact unit_cong_div K hca (hβ1 v hv) (hβc v hv)
    · rw [hw, archSign_mul, archSign_inv, archSign_principal]
      exact iff_of_true (hα.sign τ) (hβ.2 τ)
  have hu_eq : u = pK (α * β) * w := by
    have hw' : w = (pK β)⁻¹ * ((pK α)⁻¹ * u) := by rw [hw, mul_comm (u * (pK α)⁻¹), mul_comm u]
    rw [hw', map_mul, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_left]
  rw [hu_eq]
  exact Subgroup.mul_mem_sup ⟨α * β, rfl⟩ hw_mem

private theorem ker_ideleContentHom_le_of_unitIdeles_le (h𝔣 : 𝔣 ≠ ⊥) {N : Subgroup (AdeleRing (𝓞 K) K)ˣ}
    (hN : unitIdeles K 𝔣 ≤ N) : (ideleContentHom K 𝔣).ker ≤ principalIdeles K ⊔ N := by
  rw [ker_ideleContentHom_eq K 𝔣 h𝔣]; exact sup_le_sup_left hN _

end Ker
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_CSdictBker
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

section Fold_CSdictFirstIneq

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.unitIdeles"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.unitIdeles"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup unitIdeles"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.HeckeCharacter"

open scoped nonZeroDivisors

section Assembly

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem normRaySubgroup_index_eq_of_anchors_aux (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range) :
    (normRaySubgroup K L 𝔣).index = (principalIdeles K ⊔ Nrm.range).index :=
  normRaySubgroup_index_eq_idele_index K L 𝔣 h𝔣 Nrm hA1 hA2 (ideleContentHom_surjective K 𝔣)
    (ideleContentHom_surjective L (modulusExt K L 𝔣)) (ker_ideleContentHom_le_of_unitIdeles_le K 𝔣 h𝔣 hA3)

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

end Fold_CSdictFirstIneq
p2m_reactivate "P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aHerbrand P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aKummer.RadicandBasis P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors.M4aP2"

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      HeckeCharacter.IsAdjuster L (HeckeCharacter.modulusExt K L 𝔣) u α →
        HeckeCharacter.IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K (Nrm u)) =
        HeckeCharacter.fracRelNormUnit K L
          (HeckeCharacter.fadContentHom L (HeckeCharacter.projFin L u)))
    (hA3 : LanglandsTunnell.P2.Artin.unitIdeles K 𝔣 ≤ Nrm.range) :
    (LanglandsTunnell.P2.Artin.normRaySubgroup K L 𝔣).index =
      (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index :=
  LanglandsTunnell.P2.Artin.normRaySubgroup_index_eq_of_anchors_aux K L 𝔣 h𝔣 Nrm hA1 hA2 hA3

end S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors (solution)
