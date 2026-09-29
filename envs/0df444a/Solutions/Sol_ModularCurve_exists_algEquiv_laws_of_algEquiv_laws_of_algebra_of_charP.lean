-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d16530dc-f937-5bc0-8966-0c238073c7e5

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct MatrixGroups ModularForm
open scoped IntermediateField.algebraAdjoinAdjoin

namespace BaseChangeW

open HahnSeries

section Coeff

variable (κ K : Type*) [Field κ] [Field K] [Algebra κ K]

theorem algebraMap_laurent (c : κ) :
    algebraMap κ (LaurentSeries K) c = HahnSeries.C (algebraMap κ K c) := by
  have h1 : algebraMap κ (PowerSeries K) c = PowerSeries.C (algebraMap κ K c) := PowerSeries.algebraMap_apply
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

noncomputable def ι : LaurentSeries κ →ₐ[κ] LaurentSeries K :=
  { ModularCurve.coeffMap (algebraMap κ K) with
    commutes' := fun c => by
      show ModularCurve.coeffMap (algebraMap κ K) (algebraMap κ (LaurentSeries κ) c) = algebraMap κ (LaurentSeries K) c
      rw [algebraMap_laurent κ κ c, algebraMap_laurent κ K c, Algebra.algebraMap_self, RingHom.id_apply,
        HahnSeries.C_apply, HahnSeries.C_apply, ModularCurve.coeffMap_single] }

theorem ι_apply (x : LaurentSeries κ) : ι κ K x = ModularCurve.coeffMap (algebraMap κ K) x := rfl

theorem ι_coeff (x : LaurentSeries κ) (n : ℤ) : (ι κ K x).coeff n = algebraMap κ K (x.coeff n) := rfl

theorem ι_injective : Function.Injective (ι κ K) := (ι κ K).toRingHom.injective

noncomputable def constAlgHom : K →ₐ[κ] LaurentSeries K :=
  { (HahnSeries.C : K →+* LaurentSeries K) with
    commutes' := fun c => by
      show HahnSeries.C (algebraMap κ K c) = algebraMap κ (LaurentSeries K) c
      rw [algebraMap_laurent] }

theorem constAlgHom_apply (b : K) : constAlgHom κ K b = HahnSeries.C b := rfl

theorem linearDisjoint_range : (ι κ K).range.LinearDisjoint (constAlgHom κ K).range := by
  classical
  let b := Module.Basis.ofVectorSpace κ K
  let e : K ≃ₐ[κ] (constAlgHom κ K).range := AlgEquiv.ofInjective (constAlgHom κ K) (RingHom.injective _)
  let b' : Module.Basis _ κ (constAlgHom κ K).range := b.map e.toLinearEquiv
  refine Subalgebra.LinearDisjoint.of_basis_right _ _ b' ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hx : ∀ j, ∃ x : LaurentSeries κ, ι κ K x = ((g j : (ι κ K).range) : LaurentSeries K) :=
    fun j => (AlgHom.mem_range _).mp (g j).2
  choose x hxg using hx
  have hval : ∀ j, ((constAlgHom κ K).range.val (b' j) : LaurentSeries K) = HahnSeries.C (b j) := by
    intro j
    show (((b.map e.toLinearEquiv) j : (constAlgHom κ K).range) : LaurentSeries K) = HahnSeries.C (b j)
    rw [Module.Basis.map_apply]
    show ((e (b j) : (constAlgHom κ K).range) : LaurentSeries K) = _
    rw [AlgEquiv.ofInjective_apply]
    rfl
  have hcoef : ∀ n : ℤ, ∑ j ∈ s, (x j).coeff n • b j = 0 := by
    intro n
    have h := congrArg (fun z : LaurentSeries K => z.coeff n) hsum
    simp only [Function.comp_apply, HahnSeries.coeff_zero] at h
    rw [HahnSeries.coeff_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, hval j, smul_eq_mul, mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      ← hxg j, ι_coeff, smul_eq_mul, Algebra.smul_def, mul_comm]
  have hzero : ∀ n : ℤ, (x i).coeff n = 0 := fun n =>
    linearIndependent_iff'.mp b.linearIndependent s (fun j => (x j).coeff n) (hcoef n) i hi
  have hxi : x i = 0 := HahnSeries.ext (funext hzero)
  apply Subtype.ext
  show ((g i : (ι κ K).range) : LaurentSeries K) = 0
  rw [← hxg i, hxi, map_zero]

scoped instance isScalarTower_laurent {k₁ k₂ : Type*} [Field k₁] [Field k₂] [Algebra k₁ k₂] :
    @IsScalarTower k₁ k₂ (LaurentSeries k₂) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.of_algebraMap_eq' k₁ k₂ (LaurentSeries k₂) _ _ _ _ _ _ (by
    ext c : 1
    rw [RingHom.comp_apply, algebraMap_laurent, ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl)

theorem injective_mul (E : IntermediateField κ (LaurentSeries κ)) :
    Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId K (LaurentSeries K)) ((ι κ K).comp E.val)
      (fun _ _ => Commute.all _ _)) := by
  classical
  set mul := Algebra.TensorProduct.lift (Algebra.ofId K (LaurentSeries K)) ((ι κ K).comp E.val) (fun _ _ => Commute.all _ _) with hmul

  let P : Subalgebra κ (LaurentSeries K) := ((ι κ K).comp E.val).range
  let Q : Subalgebra κ (LaurentSeries K) := (constAlgHom κ K).range
  have hle : P ≤ (ι κ K).range := by
    rintro _ ⟨r, rfl⟩; exact ⟨(r : LaurentSeries κ), rfl⟩
  have hPQ : P.LinearDisjoint Q := (linearDisjoint_range κ K).of_le_left_of_flat hle
  have hinj := Subalgebra.linearDisjoint_iff_injective.mp hPQ

  let eE : ↥E ≃ₐ[κ] ↥P := AlgEquiv.ofInjective ((ι κ K).comp E.val) (((ι κ K).comp E.val).toRingHom.injective)
  let eK : K ≃ₐ[κ] ↥Q := AlgEquiv.ofInjective (constAlgHom κ K) (RingHom.injective _)
  let θ : K ⊗[κ] ↥E ≃ₐ[κ] ↥P ⊗[κ] ↥Q :=
    (Algebra.TensorProduct.congr eK eE).trans (Algebra.TensorProduct.comm κ ↥Q ↥P)
  have hfac : ∀ t, mul t = P.mulMap Q (θ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      rw [hmul, Algebra.TensorProduct.lift_tmul]
      show algebraMap K (LaurentSeries K) c * ι κ K (y : LaurentSeries κ) = P.mulMap Q (Algebra.TensorProduct.comm κ ↥Q ↥P (eK c ⊗ₜ eE y))
      rw [Algebra.TensorProduct.comm_tmul, Subalgebra.mulMap_tmul, mul_comm,
        show ((eE y : ↥P) : LaurentSeries K) = ι κ K (y : LaurentSeries κ) from AlgEquiv.ofInjective_apply _ _ y,
        show ((eK c : ↥Q) : LaurentSeries K) = HahnSeries.C c from AlgEquiv.ofInjective_apply _ _ c,
        ModularCurve.algebraMap_laurentSeries_eq_single]
      rfl
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  intro a b hab
  apply θ.injective
  apply hinj
  rw [← hfac, ← hfac, hab]

end Coeff

end BaseChangeW
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

namespace BaseChangeW

open HahnSeries

noncomputable section

section Extend

variable (κ K : Type*) [Field κ] [Field K] [Algebra κ K]
variable (S : Set (LaurentSeries κ))

abbrev Eκ : IntermediateField κ (LaurentSeries κ) := IntermediateField.adjoin κ S
abbrev EK : IntermediateField K (LaurentSeries K) := IntermediateField.adjoin K (ι κ K '' S)

theorem ι_mem {y : LaurentSeries κ} (hy : y ∈ Eκ κ S) : ι κ K y ∈ EK κ K S := by
  have hy' : y ∈ Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ S) := hy
  revert hy'
  refine fun hy' => (Subfield.closure_le (t := (EK κ K S).toSubfield.comap (ι κ K).toRingHom)).mpr ?_ hy'
  rintro z (⟨r, rfl⟩ | hz)
  · show ι κ K (algebraMap κ (LaurentSeries κ) r) ∈ EK κ K S
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply κ K (LaurentSeries K)]
    exact IntermediateField.algebraMap_mem _ _
  · exact IntermediateField.subset_adjoin K _ ⟨z, hz, rfl⟩

variable (W : ↥(Eκ κ S) ≃ₐ[κ] ↥(Eκ κ S))

noncomputable def μ : K ⊗[κ] ↥(Eκ κ S) →ₐ[K] LaurentSeries K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (LaurentSeries K)) ((ι κ K).comp (Eκ κ S).val) (fun _ _ => Commute.all _ _)

noncomputable def ψ : K ⊗[κ] ↥(Eκ κ S) →ₐ[K] LaurentSeries K :=
  (μ κ K S).comp (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) W).toAlgHom

theorem μ_tmul (c : K) (y : ↥(Eκ κ S)) : μ κ K S (c ⊗ₜ y) = algebraMap K (LaurentSeries K) c * ι κ K (y : LaurentSeries κ) :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem ψ_tmul (c : K) (y : ↥(Eκ κ S)) :
    ψ κ K S W (c ⊗ₜ y) = algebraMap K (LaurentSeries K) c * ι κ K ((W y : ↥(Eκ κ S)) : LaurentSeries κ) := by
  show μ κ K S (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) W (c ⊗ₜ y)) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, μ_tmul]
  rfl

theorem μ_injective : Function.Injective (μ κ K S) := injective_mul κ K (Eκ κ S)

theorem ψ_injective : Function.Injective (ψ κ K S W) :=
  (μ_injective κ K S).comp (AlgEquiv.injective _)

theorem μ_mem (t : K ⊗[κ] ↥(Eκ κ S)) : μ κ K S t ∈ EK κ K S := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c y =>
    rw [μ_tmul]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (ι_mem κ K S y.2)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

theorem ψ_mem (t : K ⊗[κ] ↥(Eκ κ S)) : ψ κ K S W t ∈ EK κ K S := by
  rw [ψ, AlgHom.comp_apply]; exact μ_mem κ K S _

theorem adjoin_le_range : Algebra.adjoin K (ι κ K '' S) ≤ (μ κ K S).range := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨(1 : K) ⊗ₜ ⟨s, IntermediateField.subset_adjoin κ S hs⟩, ?_⟩
  show μ κ K S _ = _
  rw [μ_tmul, map_one, one_mul]

noncomputable def eμ : (K ⊗[κ] ↥(Eκ κ S)) ≃ₐ[K] ↥(μ κ K S).range :=
  AlgEquiv.ofInjective (μ κ K S) (μ_injective κ K S)

noncomputable def gW : ↥(Algebra.adjoin K (ι κ K '' S)) →ₐ[K] LaurentSeries K :=
  ((ψ κ K S W).comp ((eμ κ K S).symm : ↥(μ κ K S).range →ₐ[K] K ⊗[κ] ↥(Eκ κ S))).comp
    (Subalgebra.inclusion (adjoin_le_range κ K S))

theorem gW_injective : Function.Injective (gW κ K S W) := by
  exact ((ψ_injective κ K S W).comp (eμ κ K S).symm.injective).comp (Subalgebra.inclusion_injective (adjoin_le_range κ K S))

theorem gW_gen {s : LaurentSeries κ} (hs : s ∈ S) :
    gW κ K S W ⟨ι κ K s, Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ =
      ι κ K ((W ⟨s, IntermediateField.subset_adjoin κ S hs⟩ : ↥(Eκ κ S)) : LaurentSeries κ) := by
  have hμ : μ κ K S ((1 : K) ⊗ₜ ⟨s, IntermediateField.subset_adjoin κ S hs⟩) = ι κ K s := by rw [μ_tmul, map_one, one_mul]
  have he : (eμ κ K S).symm
      ⟨ι κ K s, adjoin_le_range κ K S (Algebra.subset_adjoin ⟨s, hs, rfl⟩)⟩ = (1 : K) ⊗ₜ ⟨s, IntermediateField.subset_adjoin κ S hs⟩ := by
    apply (eμ κ K S).injective
    rw [AlgEquiv.apply_symm_apply]
    exact Subtype.ext hμ.symm
  show ψ κ K S W ((eμ κ K S).symm ⟨ι κ K s, _⟩) = _
  rw [he, ψ_tmul, map_one, one_mul]

noncomputable def fW : ↥(EK κ K S) →ₐ[K] LaurentSeries K :=
  IsFractionRing.liftAlgHom (K := ↥(EK κ K S)) (gW_injective κ K S W)

theorem fW_algebraMap (a : ↥(Algebra.adjoin K (ι κ K '' S))) :
    fW κ K S W (algebraMap _ ↥(EK κ K S) a) = gW κ K S W a := by
  rw [fW, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem fW_ι (y : ↥(Eκ κ S)) : fW κ K S W ⟨ι κ K y, ι_mem κ K S y.2⟩ = ι κ K ((W y : ↥(Eκ κ S)) : LaurentSeries κ) := by

  let jE : ↥(Eκ κ S) →+* ↥(EK κ K S) :=
    { toFun := fun y => ⟨ι κ K y, ι_mem κ K S y.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  let h₁ : ↥(Eκ κ S) →ₐ[κ] LaurentSeries K :=
    { (fW κ K S W).toRingHom.comp jE with
      commutes' := fun c => by
        show fW κ K S W ⟨ι κ K (algebraMap κ ↥(Eκ κ S) c : LaurentSeries κ), _⟩ = algebraMap κ (LaurentSeries K) c
        have e : (⟨ι κ K ((algebraMap κ ↥(Eκ κ S) c : ↥(Eκ κ S)) : LaurentSeries κ), ι_mem κ K S (algebraMap κ ↥(Eκ κ S) c).2⟩ : ↥(EK κ K S)) =
            algebraMap K ↥(EK κ K S) (algebraMap κ K c) := by
          apply Subtype.ext
          show ι κ K (algebraMap κ (LaurentSeries κ) c) = algebraMap K (LaurentSeries K) (algebraMap κ K c)
          rw [AlgHom.commutes, IsScalarTower.algebraMap_apply κ K (LaurentSeries K)]
        rw [e, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
  let h₂ : ↥(Eκ κ S) →ₐ[κ] LaurentSeries K := ((ι κ K).comp (Eκ κ S).val).comp (W : ↥(Eκ κ S) →ₐ[κ] ↥(Eκ κ S))
  have heq : h₁ = h₂ := by
    apply IntermediateField.adjoin_algHom_ext κ
    intro s hs
    show fW κ K S W ⟨ι κ K s, _⟩ = ι κ K ((W ⟨s, _⟩ : ↥(Eκ κ S)) : LaurentSeries κ)
    have ha : (⟨ι κ K s, ι_mem κ K S (IntermediateField.subset_adjoin κ S hs)⟩ : ↥(EK κ K S)) =
        algebraMap _ ↥(EK κ K S) (⟨ι κ K s, Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : ↥(Algebra.adjoin K (ι κ K '' S))) :=
      Subtype.ext rfl
    rw [ha, fW_algebraMap, gW_gen κ K S W hs]
  exact congrArg (fun h : ↥(Eκ κ S) →ₐ[κ] LaurentSeries K => h y) heq

theorem fW_mem (x : ↥(EK κ K S)) : fW κ K S W x ∈ EK κ K S := by
  have hr : (fW κ K S W).fieldRange = IntermediateField.adjoin K (gW κ K S W).range := IsFractionRing.liftAlgHom_fieldRange _
  have hx : fW κ K S W x ∈ (fW κ K S W).fieldRange := ⟨x, rfl⟩
  rw [hr] at hx
  refine (IntermediateField.adjoin_le_iff.mpr ?_ : IntermediateField.adjoin K (Set.range (gW κ K S W)) ≤ EK κ K S) hx
  rintro _ ⟨a, rfl⟩
  show ψ κ K S W _ ∈ EK κ K S
  exact ψ_mem κ K S W _

theorem fW_surj (z : ↥(EK κ K S)) : ∃ x : ↥(EK κ K S), fW κ K S W x = z := by

  have hle : EK κ K S ≤ (fW κ K S W).fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨ι κ K ((W.symm ⟨s, IntermediateField.subset_adjoin κ S hs⟩ : ↥(Eκ κ S)) : LaurentSeries κ), ι_mem κ K S (W.symm _).2⟩, ?_⟩
    show fW κ K S W ⟨ι κ K ((W.symm ⟨s, _⟩ : ↥(Eκ κ S)) : LaurentSeries κ), _⟩ = ι κ K s
    rw [fW_ι, AlgEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := hle z.2
  exact ⟨x, hx⟩

noncomputable def WK : ↥(EK κ K S) ≃ₐ[K] ↥(EK κ K S) :=
  AlgEquiv.ofBijective ((fW κ K S W).codRestrict (EK κ K S).toSubalgebra (fW_mem κ K S W))
    ⟨fun a b h => (fW κ K S W).toRingHom.injective (congrArg Subtype.val h),
     fun z => by obtain ⟨x, hx⟩ := fW_surj κ K S W z; exact ⟨x, Subtype.ext hx⟩⟩

theorem WK_coe (x : ↥(EK κ K S)) : ((WK κ K S W x : ↥(EK κ K S)) : LaurentSeries K) = fW κ K S W x := rfl

theorem WK_ι (y : ↥(Eκ κ S)) :
    ((WK κ K S W ⟨ι κ K y, ι_mem κ K S y.2⟩ : ↥(EK κ K S)) : LaurentSeries K) = ι κ K ((W y : ↥(Eκ κ S)) : LaurentSeries κ) := by
  rw [WK_coe, fW_ι]

end Extend
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end BaseChangeW
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

namespace BaseChangeW

open HahnSeries

noncomputable section

section Modular

variable (κ K : Type*) [Field κ] [Field K] [Algebra κ K]

theorem ι_ofPowerSeries_map_int (u : PowerSeries ℤ) :
    ι κ K (ofPowerSeries ℤ κ (u.map (Int.castRingHom κ))) = ofPowerSeries ℤ K (u.map (Int.castRingHom K)) := by
  rw [ι_apply]
  ext k
  rw [ModularCurve.coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map,
      eq_intCast, eq_intCast, map_intCast]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem ι_intSeriesC (u : PowerSeries ℤ) : ι κ K (ModularCurve.intSeriesC κ u) = ModularCurve.intSeriesC K u :=
  ι_ofPowerSeries_map_int κ K u

theorem intSeriesC_ne_zero_iff (u : PowerSeries ℤ) : ModularCurve.intSeriesC K u ≠ 0 ↔ ModularCurve.intSeriesC κ u ≠ 0 := by
  rw [← ι_intSeriesC κ K, map_ne_zero_iff _ (ι_injective κ K)]

theorem image_intFormRatiosC (Δ : Subgroup SL(2, ℤ)) :
    ι κ K '' ModularCurve.intFormRatiosC κ Δ = ModularCurve.intFormRatiosC K Δ := by
  ext z
  constructor
  · rintro ⟨_, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff κ K pg).mpr hg0, ?_⟩
    rw [map_div₀, ι_intSeriesC, ι_intSeriesC]
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨_, ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff κ K pg).mp hg0, rfl⟩, ?_⟩
    rw [map_div₀, ι_intSeriesC, ι_intSeriesC]

theorem EK_eq (Δ : Subgroup SL(2, ℤ)) :
    EK κ K (ModularCurve.intFormRatiosC κ Δ) = ModularCurve.qExpFunctionFieldC K Δ := by
  rw [EK, image_intFormRatiosC]; rfl

theorem ι_mem_qExp (Δ : Subgroup SL(2, ℤ)) {y : LaurentSeries κ} (hy : y ∈ ModularCurve.qExpFunctionFieldC κ Δ) :
    ι κ K y ∈ ModularCurve.qExpFunctionFieldC K Δ := by
  rw [← EK_eq κ K Δ]; exact ι_mem κ K _ hy

def jq (Δ : Subgroup SL(2, ℤ)) : ↥(ModularCurve.qExpFunctionFieldC κ Δ) →+* ↥(ModularCurve.qExpFunctionFieldC K Δ) where
  toFun y := ⟨ι κ K y, ι_mem_qExp κ K Δ y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_jq (Δ : Subgroup SL(2, ℤ)) (y : ↥(ModularCurve.qExpFunctionFieldC κ Δ)) :
    ((jq κ K Δ y : ↥(ModularCurve.qExpFunctionFieldC K Δ)) : LaurentSeries K) = ι κ K y := rfl

theorem jq_algebraMap (Δ : Subgroup SL(2, ℤ)) (c : κ) :
    jq κ K Δ (algebraMap κ _ c) = algebraMap K _ (algebraMap κ K c) := by
  apply Subtype.ext
  show ι κ K (algebraMap κ (LaurentSeries κ) c) = algebraMap K (LaurentSeries K) (algebraMap κ K c)
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply κ K (LaurentSeries K)]

theorem coeffMap_qExpand {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    ModularCurve.coeffMap f (ModularCurve.qExpand R n x) = ModularCurve.qExpand T n (ModularCurve.coeffMap f x) := by
  ext k
  rw [ModularCurve.coeffMap_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, ModularCurve.coeffMap_coeff]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd _ _ hk, ModularCurve.qExpand_coeff_of_not_dvd _ _ hk, map_zero]

theorem ι_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries κ) :
    ι κ K (ModularCurve.qExpand κ n x) = ModularCurve.qExpand K n (ι κ K x) :=
  coeffMap_qExpand _ n x

variable (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

theorem jq_alpha (y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) :
    jq κ K _ (ModularCurve.heckeAlphaModLH κ N H' ℓ y) = ModularCurve.heckeAlphaModLH K N H' ℓ (jq κ K _ y) := by
  apply Subtype.ext
  rw [coe_jq, ModularCurve.coe_heckeAlphaModLH, ModularCurve.coe_heckeAlphaModLH, coe_jq]

theorem jq_beta (hβκ : ModularCurve.HeckeBetaModLHDefined κ N H' ℓ) (hβK : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) :
    jq κ K _ (ModularCurve.heckeBetaModLH κ N H' ℓ y) = ModularCurve.heckeBetaModLH K N H' ℓ (jq κ K _ y) := by
  apply Subtype.ext
  rw [coe_jq, ModularCurve.coe_heckeBetaModLH _ _ _ _ hβκ, ModularCurve.coe_heckeBetaModLH _ _ _ _ hβK, coe_jq, ι_qExpand]

end Modular
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end BaseChangeW
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

namespace BaseChangeW

open HahnSeries
open scoped ModularForm

noncomputable section

section Dia

variable (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (hpN : ¬ p ∣ N)

theorem intSeriesC_C_mul (F : Type*) [Field F] (z : ℤ) (q : PowerSeries ℤ) :
    ModularCurve.intSeriesC F (PowerSeries.C z * q) = HahnSeries.C (z : F) * ModularCurve.intSeriesC F q := by
  rw [ModularCurve.intSeriesC, ModularCurve.intSeriesC, map_mul, PowerSeries.map_C, map_mul, ofPowerSeries_C]
  rfl

theorem T_mem_gammaH : ModularGroup.T ∈ CohCarrier.GammaH N H' := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨CongruenceSubgroup.Gamma1_in_Gamma0 N hT, ?_⟩
  have h1 : CohCarrier.gamma0Units N ⟨_, CongruenceSubgroup.Gamma1_in_Gamma0 N hT⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact ((CongruenceSubgroup.Gamma1_mem N _).mp hT).2.1
  rw [h1]; exact one_mem H'

theorem isIntegralQExp_smul {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k) {pf : PowerSeries ℤ}
    (hf : ModularCurve.IsIntegralQExp f pf) (z : ℤ) :
    ModularCurve.IsIntegralQExp (⇑((z : ℂ) • f)) (PowerSeries.C z * pf) := by
  have h1 : (1 : ℝ) ∈ (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_gammaH N H')]
    exact AddSubgroup.mem_zmultiples _
  unfold ModularCurve.IsIntegralQExp at hf ⊢
  rw [ModularForm.IsGLPos.coe_smul, ModularFormClass.qExpansion_smul one_pos h1 (z : ℂ) f, map_mul, PowerSeries.map_C, hf,
    eq_intCast, PowerSeries.smul_eq_C_mul]

include hpN in

theorem exists_pullback_data (γ : CongruenceSubgroup.Gamma0 N) {k : ℤ}
    (a b : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k) (pa pb : PowerSeries ℤ)
    (ha : ModularCurve.IsIntegralQExp a pa) (hb : ModularCurve.IsIntegralQExp b pb)
    (hb0 : ModularCurve.intSeriesC (ZMod p) pb ≠ 0) :
    ∃ (PF PG : PowerSeries ℤ) (F G : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k) (m : ℕ),
      ModularCurve.IsIntegralQExp F PF ∧ ModularCurve.IsIntegralQExp G PG ∧
      ModularCurve.IsIntegralQExp (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • a)) (PowerSeries.C ((N : ℤ) ^ m) * pa) ∧
      ModularCurve.IsIntegralQExp (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • b)) (PowerSeries.C ((N : ℤ) ^ m) * pb) ∧
      (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • a) : UpperHalfPlane → ℂ) = ((⇑F : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) ∧
      (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • b) : UpperHalfPlane → ℂ) = ((⇑G : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) ∧
      ModularCurve.intSeriesC (ZMod p) PG ≠ 0 := by
  classical
  set γ' : CongruenceSubgroup.Gamma0 N := γ⁻¹ with hγ'
  obtain ⟨ρp, hint, -, -, -, -⟩ := ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod p N hpN H'
  obtain ⟨n, f₁, pf₁, hf₁eq, hf₁int, hf₁iff⟩ := hint γ' k a pa ha
  obtain ⟨n', g₁, pg₁, hg₁eq, hg₁int, hg₁iff⟩ := hint γ' k b pb hb
  set F₁ : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k := (((N : ℤ) ^ n' : ℤ) : ℂ) • f₁ with hF₁
  set G₁ : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k := (((N : ℤ) ^ n : ℤ) : ℂ) • g₁ with hG₁
  have hF₁int : ModularCurve.IsIntegralQExp F₁ (PowerSeries.C ((N : ℤ) ^ n') * pf₁) := isIntegralQExp_smul N H' f₁ hf₁int _
  have hG₁int : ModularCurve.IsIntegralQExp G₁ (PowerSeries.C ((N : ℤ) ^ n) * pg₁) := isIntegralQExp_smul N H' g₁ hg₁int _
  set c : ℂ := ((N : ℂ) ^ (n + n')) with hc
  have hF₁eq : (⇑F₁ : UpperHalfPlane → ℂ) = c • ((⇑a : UpperHalfPlane → ℂ) ∣[k] (γ' : SL(2, ℤ))) := by
    rw [hF₁, ModularForm.IsGLPos.coe_smul, hf₁eq, smul_smul, hc]
    congr 1; push_cast; ring
  have hG₁eq : (⇑G₁ : UpperHalfPlane → ℂ) = c • ((⇑b : UpperHalfPlane → ℂ) ∣[k] (γ' : SL(2, ℤ))) := by
    rw [hG₁, ModularForm.IsGLPos.coe_smul, hg₁eq, smul_smul, hc]
    congr 1; push_cast; ring
  have hγγ : (γ' : SL(2, ℤ)) * (γ : SL(2, ℤ)) = 1 := by rw [hγ', Subgroup.coe_inv, inv_mul_cancel]
  have hscalar : ((((N : ℤ) ^ (n + n') : ℤ)) : ℂ) = c := by rw [hc]; push_cast; ring
  refine ⟨_, _, F₁, G₁, n + n', hF₁int, hG₁int, isIntegralQExp_smul N H' a ha _, isIntegralQExp_smul N H' b hb _, ?_, ?_, ?_⟩
  · rw [hF₁eq, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, hγγ, SlashAction.slash_one,
      ModularForm.IsGLPos.coe_smul, hscalar]
  · rw [hG₁eq, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, hγγ, SlashAction.slash_one,
      ModularForm.IsGLPos.coe_smul, hscalar]
  · rw [intSeriesC_C_mul]
    refine mul_ne_zero (HahnSeries.C_ne_zero ?_) (fun h0 => hb0 (hg₁iff.mp h0))
    have : ((N : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpN
    push_cast
    exact pow_ne_zero _ this

include hpN in

theorem rho_gen (F : Type*) [Field F] [CharP F p]
    (ρ : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC F (CohCarrier.GammaH N H')) ≃ₐ[F] ↥(ModularCurve.qExpFunctionFieldC F (CohCarrier.GammaH N H'))))
    (hρ : ModularCurve.IsDiamondPullbackModL F N H' ρ)
    (γ : CongruenceSubgroup.Gamma0 N) {k : ℤ}
    {a b F₁ G₁ : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k} {pa pb PF PG : PowerSeries ℤ} {m : ℕ}
    (ha : ModularCurve.IsIntegralQExp a pa) (hb : ModularCurve.IsIntegralQExp b pb)
    (hF : ModularCurve.IsIntegralQExp F₁ PF) (hG : ModularCurve.IsIntegralQExp G₁ PG)
    (hca : ModularCurve.IsIntegralQExp (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • a)) (PowerSeries.C ((N : ℤ) ^ m) * pa))
    (hcb : ModularCurve.IsIntegralQExp (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • b)) (PowerSeries.C ((N : ℤ) ^ m) * pb))
    (hfs : (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • a) : UpperHalfPlane → ℂ) = ((⇑F₁ : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hgs : (⇑((((N : ℤ) ^ m : ℤ) : ℂ) • b) : UpperHalfPlane → ℂ) = ((⇑G₁ : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hPG : ModularCurve.intSeriesC (ZMod p) PG ≠ 0)
    (hbF : ModularCurve.intSeriesC F pb ≠ 0) :
    ((ρ γ ⟨ModularCurve.intSeriesC F pa / ModularCurve.intSeriesC F pb, ModularCurve.div_mem_qExpFunctionFieldC a b ha hb hbF⟩ :
        ↥(ModularCurve.qExpFunctionFieldC F (CohCarrier.GammaH N H'))) : LaurentSeries F) =
      ModularCurve.intSeriesC F PF / ModularCurve.intSeriesC F PG := by
  letI := ZMod.algebra F p
  have hNF : ((N : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p]; exact hpN
  have hpz : ∀ q : PowerSeries ℤ, ModularCurve.intSeriesC (ZMod p) q ≠ 0 → ModularCurve.intSeriesC F q ≠ 0 := by
    intro q hq h0
    apply hq
    have h1 : q.map (Int.castRingHom F) = 0 := ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
    have h2 : (q.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) F) = 0 := by
      rw [show PowerSeries.map (algebraMap (ZMod p) F) (PowerSeries.map (Int.castRingHom (ZMod p)) q) =
          PowerSeries.map ((algebraMap (ZMod p) F).comp (Int.castRingHom (ZMod p))) q from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom (ZMod p)) (algebraMap (ZMod p) F))) q).symm,
        RingHom.ext_int ((algebraMap (ZMod p) F).comp (Int.castRingHom (ZMod p))) (Int.castRingHom _), h1]
    have h3 : q.map (Int.castRingHom (ZMod p)) = 0 :=
      PowerSeries.map_injective _ (algebraMap (ZMod p) F).injective (by rw [h2, map_zero])
    rw [ModularCurve.intSeriesC, h3, map_zero]
  have hCF : (HahnSeries.C ((((N : ℤ) ^ m : ℤ)) : F) : LaurentSeries F) ≠ 0 := by
    refine HahnSeries.C_ne_zero ?_
    push_cast
    exact pow_ne_zero _ hNF
  have hx : (((⟨ModularCurve.intSeriesC F pa / ModularCurve.intSeriesC F pb, ModularCurve.div_mem_qExpFunctionFieldC a b ha hb hbF⟩ :
        ↥(ModularCurve.qExpFunctionFieldC F (CohCarrier.GammaH N H')))) : LaurentSeries F) =
      ModularCurve.intSeriesC F (PowerSeries.C ((N : ℤ) ^ m) * pa) / ModularCurve.intSeriesC F (PowerSeries.C ((N : ℤ) ^ m) * pb) := by
    rw [intSeriesC_C_mul, intSeriesC_C_mul, mul_div_mul_left _ _ hCF]
  exact hρ.coe_apply_eq γ hF hG hca hcb hfs hgs (hpz PG hPG) hx

end Dia
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end BaseChangeW
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

namespace BaseChangeW

open HahnSeries

noncomputable section

section Laws

theorem hpN_of (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) (hNK : ((N : ℕ) : K) ≠ 0) : ¬ p ∣ N :=
  fun h => hNK ((CharP.cast_eq_zero_iff K p N).mpr h)

theorem charP_κ (K : Type*) [Field K] (p : ℕ) [CharP K p] (κ : Type*) [Field κ] [Algebra κ K] : CharP κ p :=
  ((algebraMap κ K).charP_iff_charP p).mpr inferInstance

theorem jq_rho (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (hNK : ((N : ℕ) : K) ≠ 0)
    (κ : Type*) [Field κ] [Algebra κ K]
    (ρκ : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))))
    (hρκ : ModularCurve.IsDiamondPullbackModL κ N H' ρκ)
    (ρK : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))))
    (hρK : ModularCurve.IsDiamondPullbackModL K N H' ρK)
    (γ : CongruenceSubgroup.Gamma0 N) (y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) :
    jq κ K _ (ρκ γ y) = ρK γ (jq κ K _ y) := by
  classical
  haveI := charP_κ K p κ

  let h₁ : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) →ₐ[κ] LaurentSeries K :=
    { ((ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')).val.toRingHom.comp
        ((ρK γ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] _).toRingEquiv.toRingHom)).comp (jq κ K _) with
      commutes' := fun c => by
        show (((ρK γ) (jq κ K _ (algebraMap κ _ c)) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K) =
          algebraMap κ (LaurentSeries K) c
        rw [jq_algebraMap, AlgEquiv.commutes, IsScalarTower.algebraMap_apply κ K (LaurentSeries K)]
        rfl }
  let h₂ : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) →ₐ[κ] LaurentSeries K :=
    ((ι κ K).comp (ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')).val).comp
      ((ρκ γ : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] _) :
        ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) →ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')))
  have heq : h₁ = h₂ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin κ (s := ModularCurve.intFormRatiosC κ (CohCarrier.GammaH N H')) rfl ?_
    rintro _ ⟨k, a, b, pa, pb, ha, hb, hb0, rfl⟩

    have hb0p : ModularCurve.intSeriesC (ZMod p) pb ≠ 0 := by
      letI := ZMod.algebra κ p
      intro h0; apply hb0
      have h1 : pb.map (Int.castRingHom (ZMod p)) = 0 := ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
      have h2 : pb.map (Int.castRingHom κ) = 0 := by
        rw [← RingHom.ext_int ((algebraMap (ZMod p) κ).comp (Int.castRingHom (ZMod p))) (Int.castRingHom _),
          show PowerSeries.map ((algebraMap (ZMod p) κ).comp (Int.castRingHom (ZMod p))) pb =
            PowerSeries.map (algebraMap (ZMod p) κ) (PowerSeries.map (Int.castRingHom (ZMod p)) pb) from
            congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom (ZMod p)) (algebraMap (ZMod p) κ))) pb,
          h1, map_zero]
      rw [ModularCurve.intSeriesC, h2, map_zero]
    have hb0K : ModularCurve.intSeriesC K pb ≠ 0 := (intSeriesC_ne_zero_iff κ K pb).mpr hb0
    obtain ⟨PF, PG, F₁, G₁, m, hF, hG, hca, hcb, hfs, hgs, hPG⟩ := exists_pullback_data p N H' (hpN_of K p N hNK) γ a b pa pb ha hb hb0p
    have hκ := rho_gen p N H' (hpN_of K p N hNK) κ ρκ hρκ γ ha hb hF hG hca hcb hfs hgs hPG hb0
    have hK := rho_gen p N H' (hpN_of K p N hNK) K ρK hρK γ ha hb hF hG hca hcb hfs hgs hPG hb0K
    show (((ρK γ) (jq κ K (CohCarrier.GammaH N H') ⟨ModularCurve.intSeriesC κ pa / ModularCurve.intSeriesC κ pb,
          IntermediateField.subset_adjoin κ _ (ModularCurve.mem_intFormRatiosC a b ha hb hb0)⟩) :
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K) =
      ι κ K (((ρκ γ) ⟨ModularCurve.intSeriesC κ pa / ModularCurve.intSeriesC κ pb,
          IntermediateField.subset_adjoin κ _ (ModularCurve.mem_intFormRatiosC a b ha hb hb0)⟩ :
        ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) : LaurentSeries κ)
    have ej : jq κ K _ ⟨ModularCurve.intSeriesC κ pa / ModularCurve.intSeriesC κ pb,
        IntermediateField.subset_adjoin κ _ (ModularCurve.mem_intFormRatiosC a b ha hb hb0)⟩ =
        ⟨ModularCurve.intSeriesC K pa / ModularCurve.intSeriesC K pb, ModularCurve.div_mem_qExpFunctionFieldC a b ha hb hb0K⟩ := by
      apply Subtype.ext
      rw [coe_jq, map_div₀, ι_intSeriesC, ι_intSeriesC]
    rw [ej, hK, show (⟨ModularCurve.intSeriesC κ pa / ModularCurve.intSeriesC κ pb,
        IntermediateField.subset_adjoin κ _ (ModularCurve.mem_intFormRatiosC a b ha hb hb0)⟩ :
          ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) =
        ⟨_, ModularCurve.div_mem_qExpFunctionFieldC a b ha hb hb0⟩ from rfl, hκ, map_div₀, ι_intSeriesC, ι_intSeriesC]
  apply Subtype.ext
  exact (congrArg (fun h : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) →ₐ[κ] LaurentSeries K => h y) heq).symm

end Laws
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end BaseChangeW
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

namespace BaseChangeW

open HahnSeries

noncomputable section

section Final

theorem coe_equivOfEq {F E : Type*} [Field F] [Field E] [Algebra F E] {S T : IntermediateField F E} (h : S = T) (x : ↥S) :
    ((IntermediateField.equivOfEq h x : ↥T) : E) = (x : E) := rfl

theorem equivOfEq_symm_mk {F E : Type*} [Field F] [Field E] [Algebra F E] {S T : IntermediateField F E} (h : S = T)
    (z : E) (hz : z ∈ T) (hz' : z ∈ S) :
    (IntermediateField.equivOfEq h).symm ⟨z, hz⟩ = ⟨z, hz'⟩ := rfl

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (κ : Type*) [Field κ] [Algebra κ K]

abbrev ΓT : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)

variable (Wκ : ↥(ModularCurve.qExpFunctionFieldC κ (ΓT N H' ℓ)) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (ΓT N H' ℓ)))

def WT : ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) :=
  ((IntermediateField.equivOfEq (EK_eq κ K (ΓT N H' ℓ))).symm.trans
    (WK κ K (ModularCurve.intFormRatiosC κ (ΓT N H' ℓ)) Wκ)).trans (IntermediateField.equivOfEq (EK_eq κ K (ΓT N H' ℓ)))

theorem WT_jq (y : ↥(ModularCurve.qExpFunctionFieldC κ (ΓT N H' ℓ))) :
    WT K N H' ℓ κ Wκ (jq κ K _ y) = jq κ K _ (Wκ y) := by
  apply Subtype.ext
  have step : WT K N H' ℓ κ Wκ (jq κ K _ y) =
      IntermediateField.equivOfEq (EK_eq κ K (ΓT N H' ℓ))
        (WK κ K _ Wκ ((IntermediateField.equivOfEq (EK_eq κ K (ΓT N H' ℓ))).symm (jq κ K _ y))) := rfl
  have e : (IntermediateField.equivOfEq (EK_eq κ K (ΓT N H' ℓ))).symm (jq κ K _ y) =
      ⟨ι κ K y, ι_mem κ K _ y.2⟩ := equivOfEq_symm_mk _ _ _ _
  rw [step, coe_equivOfEq, coe_jq, e, WK_ι]
  rfl

theorem gen_eq {Δ : Subgroup SL(2, ℤ)} {x : LaurentSeries K} (hx : x ∈ ModularCurve.intFormRatiosC K Δ) :
    ∃ y : ↥(ModularCurve.qExpFunctionFieldC κ Δ),
      (⟨x, ModularCurve.intFormRatiosC_subset K Δ hx⟩ : ↥(ModularCurve.qExpFunctionFieldC K Δ)) = jq κ K Δ y := by
  have hx' := hx
  rw [← image_intFormRatiosC κ K] at hx'
  obtain ⟨z, hz, hzx⟩ := hx'
  exact ⟨⟨z, ModularCurve.intFormRatiosC_subset κ Δ hz⟩, Subtype.ext hzx.symm⟩

theorem law4 (hβκ : ModularCurve.HeckeBetaModLHDefined κ N H' ℓ) (hβK : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (h4 : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
      Wκ (ModularCurve.heckeBetaModLH κ N H' ℓ y) = ModularCurve.heckeAlphaModLH κ N H' ℓ y)
    (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    WT K N H' ℓ κ Wκ (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x := by
  have heq : ((WT K N H' ℓ κ Wκ : ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) ≃ₐ[K] _) :
        ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ))).comp
        (ModularCurve.heckeBetaModLH K N H' ℓ) = ModularCurve.heckeAlphaModLH K N H' ℓ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ModularCurve.intFormRatiosC K (CohCarrier.GammaH N H')) rfl ?_
    intro z hz
    obtain ⟨y, hy⟩ := gen_eq K κ hz
    show WT K N H' ℓ κ Wκ (ModularCurve.heckeBetaModLH K N H' ℓ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩) =
      ModularCurve.heckeAlphaModLH K N H' ℓ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩
    rw [hy, ← jq_beta κ K N H' ℓ hβκ hβK, WT_jq, h4, jq_alpha]
  exact congrArg (fun h : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) => h x) heq

theorem law3 (p : ℕ) [Fact p.Prime] [CharP K p] (hNK : ((N : ℕ) : K) ≠ 0)
    (hβκ : ModularCurve.HeckeBetaModLHDefined κ N H' ℓ) (hβK : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (ρκ : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))))
    (hρκ : ModularCurve.IsDiamondPullbackModL κ N H' ρκ)
    (ρK : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))))
    (hρK : ModularCurve.IsDiamondPullbackModL K N H' ρK)
    (γ₀ : CongruenceSubgroup.Gamma0 N)
    (h3 : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
      Wκ (ModularCurve.heckeAlphaModLH κ N H' ℓ y) = ModularCurve.heckeBetaModLH κ N H' ℓ (ρκ γ₀ y))
    (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    WT K N H' ℓ κ Wκ (ModularCurve.heckeAlphaModLH K N H' ℓ x) = ModularCurve.heckeBetaModLH K N H' ℓ (ρK γ₀ x) := by
  have heq : ((WT K N H' ℓ κ Wκ : ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) ≃ₐ[K] _) :
        ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ))).comp
        (ModularCurve.heckeAlphaModLH K N H' ℓ) =
      (ModularCurve.heckeBetaModLH K N H' ℓ).comp
        ((ρK γ₀ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] _) :
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ModularCurve.intFormRatiosC K (CohCarrier.GammaH N H')) rfl ?_
    intro z hz
    obtain ⟨y, hy⟩ := gen_eq K κ hz
    show WT K N H' ℓ κ Wκ (ModularCurve.heckeAlphaModLH K N H' ℓ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩) =
      ModularCurve.heckeBetaModLH K N H' ℓ (ρK γ₀ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩)
    rw [hy, ← jq_alpha κ K N H' ℓ, WT_jq, h3, jq_beta κ K N H' ℓ hβκ hβK, jq_rho K p N H' hNK κ ρκ hρκ ρK hρK]
  exact congrArg (fun h : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) => h x) heq

theorem modularFunctionFieldC_le (F : Type*) [Field F] :
    ModularCurve.modularFunctionFieldC F N ≤ ModularCurve.qExpFunctionFieldC F (CohCarrier.GammaH N H') :=
  ((ModularCurve.modularFunctionFieldC_le_full F N).trans (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 F N)).trans
    (ModularCurve.qExpFunctionFieldC_mono F (CohCarrier.GammaH_le_Gamma0 H'))

theorem ι_jqModC : ι κ K (ModularCurve.jqModC κ) = ModularCurve.jqModC K := ModularCurve.map_jqModC (algebraMap κ K)

theorem ι_jqNModC : ι κ K (ModularCurve.jqNModC κ N) = ModularCurve.jqNModC K N := by
  rw [ModularCurve.jqNModC, ModularCurve.jqNModC, ι_qExpand, ι_jqModC]

theorem floor_fixed (p : ℕ) [Fact p.Prime] [CharP K p] (hNK : ((N : ℕ) : K) ≠ 0)
    (ρκ : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))))
    (hρκ : ModularCurve.IsDiamondPullbackModL κ N H' ρκ)
    (ρK : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))))
    (hρK : ModularCurve.IsDiamondPullbackModL K N H' ρK)
    (γ₀ : CongruenceSubgroup.Gamma0 N)
    (h1 : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
      (y : LaurentSeries κ) ∈ ModularCurve.modularFunctionFieldC κ N →
        Wκ (ModularCurve.heckeAlphaModLH κ N H' ℓ y) = ModularCurve.heckeBetaModLH κ N H' ℓ y)
    (h3 : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
      Wκ (ModularCurve.heckeAlphaModLH κ N H' ℓ y) = ModularCurve.heckeBetaModLH κ N H' ℓ (ρκ γ₀ y))
    (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')))
    (hx : (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldC K N) : ρK γ₀ x = x := by

  have hfixκ : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
      (y : LaurentSeries κ) ∈ ModularCurve.modularFunctionFieldC κ N → ρκ γ₀ y = y := by
    intro y hy
    apply (ModularCurve.heckeBetaModLH κ N H' ℓ).toRingHom.injective
    show ModularCurve.heckeBetaModLH κ N H' ℓ (ρκ γ₀ y) = ModularCurve.heckeBetaModLH κ N H' ℓ y
    rw [← h3, h1 y hy]
  let φ₁ : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K :=
    ((ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')).val.comp
      ((ρK γ₀ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] _) :
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')))).comp
      (IntermediateField.inclusion (modularFunctionFieldC_le N H' K))
  let φ₂ : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K := (ModularCurve.modularFunctionFieldC K N).val
  have heq : φ₁ = φ₂ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K (s := {ModularCurve.jqModC K, ModularCurve.jqNModC K N}) rfl ?_
    intro z hz
    show (((ρK γ₀) (IntermediateField.inclusion (modularFunctionFieldC_le N H' K) ⟨z, IntermediateField.subset_adjoin K _ hz⟩)) :
      LaurentSeries K) = z
    obtain ⟨t, ht, htz⟩ : ∃ t : LaurentSeries κ, t ∈ ({ModularCurve.jqModC κ, ModularCurve.jqNModC κ N} : Set (LaurentSeries κ)) ∧
        ι κ K t = z := by
      rcases hz with rfl | rfl
      · exact ⟨_, Set.mem_insert _ _, ι_jqModC K κ⟩
      · exact ⟨_, Set.mem_insert_of_mem _ rfl, ι_jqNModC K N κ⟩
    have htM : t ∈ ModularCurve.modularFunctionFieldC κ N := IntermediateField.subset_adjoin κ _ ht
    have htD : t ∈ ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H') := modularFunctionFieldC_le N H' κ htM
    have e : IntermediateField.inclusion (modularFunctionFieldC_le N H' K)
        ⟨z, IntermediateField.subset_adjoin K _ hz⟩ = jq κ K _ ⟨t, htD⟩ := Subtype.ext htz.symm
    rw [e, ← jq_rho K p N H' hNK κ ρκ hρκ ρK hρK, hfixκ ⟨t, htD⟩ htM, coe_jq, htz]
  have key : (((ρK γ₀) (IntermediateField.inclusion (modularFunctionFieldC_le N H' K) ⟨(x : LaurentSeries K), hx⟩) :
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K) = (x : LaurentSeries K) :=
    congrArg (fun h : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K => h ⟨x, hx⟩) heq
  have e2 : IntermediateField.inclusion (modularFunctionFieldC_le N H' K) ⟨(x : LaurentSeries K), hx⟩ = x := Subtype.ext rfl
  rw [e2] at key
  exact Subtype.ext key

end Final
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

end BaseChangeW
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.BaseChangeW"

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (κ : Type*) [Field κ] [Algebra κ K]
    (hβκ : ModularCurve.HeckeBetaModLHDefined κ N H' ℓ) (hβK : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (ρκ : CongruenceSubgroup.Gamma0 N →* (↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))))
    (hρκ : ModularCurve.IsDiamondPullbackModL κ N H' ρκ)
    (ρK : CongruenceSubgroup.Gamma0 N →* (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))))
    (hρK : ModularCurve.IsDiamondPullbackModL K N H' ρK)
    (Wκ : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))))
    (hWκ :
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        (x : LaurentSeries κ) ∈ ModularCurve.modularFunctionFieldC κ N →
          Wκ (ModularCurve.heckeAlphaModLH κ N H' ℓ x) = ModularCurve.heckeBetaModLH κ N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        (x : LaurentSeries κ) ∈ ModularCurve.modularFunctionFieldC κ N →
          Wκ (ModularCurve.heckeBetaModLH κ N H' ℓ x) = ModularCurve.heckeAlphaModLH κ N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        Wκ (ModularCurve.heckeAlphaModLH κ N H' ℓ x) =
          ModularCurve.heckeBetaModLH κ N H' ℓ (ρκ (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x)) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        Wκ (ModularCurve.heckeBetaModLH κ N H' ℓ x) = ModularCurve.heckeAlphaModLH κ N H' ℓ x)) :
    ∃ WK : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))),
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldC K N →
          WK (ModularCurve.heckeAlphaModLH K N H' ℓ x) = ModularCurve.heckeBetaModLH K N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldC K N →
          WK (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        WK (ModularCurve.heckeAlphaModLH K N H' ℓ x) =
          ModularCurve.heckeBetaModLH K N H' ℓ (ρK (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x)) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        WK (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hWκ
  refine ⟨BaseChangeW.WT K N H' ℓ κ Wκ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [BaseChangeW.law3 K N H' ℓ κ Wκ p hNK hβκ hβK ρκ hρκ ρK hρK _ h3 x,
      BaseChangeW.floor_fixed K N H' ℓ κ Wκ p hNK ρκ hρκ ρK hρK _ h1 h3 x hx]
  · intro x _
    exact BaseChangeW.law4 K N H' ℓ κ Wκ hβκ hβK h4 x
  · intro x
    exact BaseChangeW.law3 K N H' ℓ κ Wκ p hNK hβκ hβK ρκ hρκ ρK hρK _ h3 x
  · intro x
    exact BaseChangeW.law4 K N H' ℓ κ Wκ hβκ hβK h4 x

end S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP (solution)
