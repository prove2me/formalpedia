-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4916f2b3-1431-574e-b622-075267a5b4ff

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct MatrixGroups ModularForm
open scoped IntermediateField.algebraAdjoinAdjoin

namespace BCPair

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

end BCPair
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

namespace BCPair

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
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

end BCPair
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

namespace BCPair

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

variable (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]

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
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

end BCPair
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

namespace BCPair

open HahnSeries
open scoped ModularForm

noncomputable section

section Phi

variable (κ K : Type*) [Field κ] [Field K] [Algebra κ K]

theorem ι_ofPowerSeries_map {R : Type*} [CommRing R] (φ : R →+* κ) (u : PowerSeries R) :
    ι κ K (ofPowerSeries ℤ κ (u.map φ)) = ofPowerSeries ℤ K (u.map ((algebraMap κ K).comp φ)) := by
  rw [ι_apply]
  ext k
  rw [ModularCurve.coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map,
      RingHom.comp_apply]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]

end Phi
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

section Final

theorem coe_equivOfEq {F E : Type*} [Field F] [Field E] [Algebra F E] {S T : IntermediateField F E} (h : S = T) (x : ↥S) :
    ((IntermediateField.equivOfEq h x : ↥T) : E) = (x : E) := rfl

theorem equivOfEq_symm_mk {F E : Type*} [Field F] [Field E] [Algebra F E] {S T : IntermediateField F E} (h : S = T)
    (z : E) (hz : z ∈ T) (hz' : z ∈ S) :
    (IntermediateField.equivOfEq h).symm ⟨z, hz⟩ = ⟨z, hz'⟩ := rfl

variable (K : Type*) [Field K] (κ : Type*) [Field κ] [Algebra κ K]

def WD (Δ : Subgroup SL(2, ℤ)) (Wκ : ↥(ModularCurve.qExpFunctionFieldC κ Δ) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ Δ)) :
    ↥(ModularCurve.qExpFunctionFieldC K Δ) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K Δ) :=
  ((IntermediateField.equivOfEq (EK_eq κ K Δ)).symm.trans
    (WK κ K (ModularCurve.intFormRatiosC κ Δ) Wκ)).trans (IntermediateField.equivOfEq (EK_eq κ K Δ))

theorem WD_jq (Δ : Subgroup SL(2, ℤ)) (Wκ : ↥(ModularCurve.qExpFunctionFieldC κ Δ) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ Δ)) (y : ↥(ModularCurve.qExpFunctionFieldC κ Δ)) :
    WD K κ Δ Wκ (jq κ K Δ y) = jq κ K Δ (Wκ y) := by
  apply Subtype.ext
  have step : WD K κ Δ Wκ (jq κ K Δ y) =
      IntermediateField.equivOfEq (EK_eq κ K Δ)
        (WK κ K _ Wκ ((IntermediateField.equivOfEq (EK_eq κ K Δ)).symm (jq κ K Δ y))) := rfl
  have e : (IntermediateField.equivOfEq (EK_eq κ K Δ)).symm (jq κ K Δ y) =
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

theorem lawS (Δ : Subgroup SL(2, ℤ)) (Wκ : ↥(ModularCurve.qExpFunctionFieldC κ Δ) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ Δ))
    (φκ : ↥(integralClosure ℤ ℂ) →+* κ) (W : GL (Fin 2) ℝ)
    (hS : ∀ (k : ℤ) (f g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] W)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] W)) →
          ModularCurve.intSeriesC κ pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Δ),
            (x : LaurentSeries κ) = ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg →
            ((Wκ x : ↥(ModularCurve.qExpFunctionFieldC κ Δ)) : LaurentSeries κ) * HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) =
              HahnSeries.ofPowerSeries ℤ κ (PfW.map φκ))
    (k : ℤ) (f g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hf : ModularCurve.IsIntegralQExp ⇑f pf) (hg : ModularCurve.IsIntegralQExp ⇑g pg)
    (hPf : PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] W)))
    (hPg : PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] W)))
    (hg0 : ModularCurve.intSeriesC K pg ≠ 0)
    (hPg0 : HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) ≠ 0)
    (x : ↥(ModularCurve.qExpFunctionFieldC K Δ))
    (hx : (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg) :
    ((WD K κ Δ Wκ x : ↥(ModularCurve.qExpFunctionFieldC K Δ)) : LaurentSeries K) *
        HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) =
      HahnSeries.ofPowerSeries ℤ K (PfW.map ((algebraMap κ K).comp φκ)) := by
  have hg0κ : ModularCurve.intSeriesC κ pg ≠ 0 := (intSeriesC_ne_zero_iff κ K pg).mp hg0
  have hPg0κ : HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 := by
    intro h
    apply hPg0
    rw [← ι_ofPowerSeries_map κ K φκ PgW, h, map_zero]
  have hmem : ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg ∈ ModularCurve.qExpFunctionFieldC κ Δ :=
    ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0κ
  have hjx : jq κ K Δ ⟨_, hmem⟩ = x := by
    apply Subtype.ext
    rw [coe_jq, hx]
    show ι κ K (ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg) = _
    rw [map_div₀, ι_intSeriesC, ι_intSeriesC]
  have key := congrArg (ι κ K) (hS k f g pf pg D PfW PgW hf hg hPf hPg hg0κ hPg0κ ⟨_, hmem⟩ rfl)
  rw [map_mul, ι_ofPowerSeries_map, ι_ofPowerSeries_map] at key
  rw [← hjx, WD_jq, coe_jq]
  exact key

variable (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]

abbrev ΓT : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)

variable (σκ : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')))
  (τκ : ↥(ModularCurve.qExpFunctionFieldC κ (ΓT N H' ℓ)) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (ΓT N H' ℓ)))

theorem law1 (hβκ : ModularCurve.HeckeBetaModLHDefined κ N H' ℓ) (hβK : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (h1 : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
      τκ (ModularCurve.heckeAlphaModLH κ N H' ℓ y) = ModularCurve.heckeBetaModLH κ N H' ℓ (σκ y))
    (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    WD K κ (ΓT N H' ℓ) τκ (ModularCurve.heckeAlphaModLH K N H' ℓ x) =
      ModularCurve.heckeBetaModLH K N H' ℓ (WD K κ (CohCarrier.GammaH N H') σκ x) := by
  have heq : ((WD K κ (ΓT N H' ℓ) τκ : ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) ≃ₐ[K] _) :
        ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ))).comp
        (ModularCurve.heckeAlphaModLH K N H' ℓ) =
      (ModularCurve.heckeBetaModLH K N H' ℓ).comp
        ((WD K κ (CohCarrier.GammaH N H') σκ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] _) :
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ModularCurve.intFormRatiosC K (CohCarrier.GammaH N H')) rfl ?_
    intro z hz
    obtain ⟨y, hy⟩ := gen_eq K κ hz
    show WD K κ (ΓT N H' ℓ) τκ (ModularCurve.heckeAlphaModLH K N H' ℓ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩) =
      ModularCurve.heckeBetaModLH K N H' ℓ (WD K κ (CohCarrier.GammaH N H') σκ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩)
    rw [hy, ← jq_alpha κ K N H' ℓ, WD_jq, h1, jq_beta κ K N H' ℓ hβκ hβK, WD_jq]
  exact congrArg (fun h : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) => h x) heq

theorem law2 (hβκ : ModularCurve.HeckeBetaModLHDefined κ N H' ℓ) (hβK : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (h2 : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
      τκ (ModularCurve.heckeBetaModLH κ N H' ℓ y) = ModularCurve.heckeAlphaModLH κ N H' ℓ (σκ y))
    (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    WD K κ (ΓT N H' ℓ) τκ (ModularCurve.heckeBetaModLH K N H' ℓ x) =
      ModularCurve.heckeAlphaModLH K N H' ℓ (WD K κ (CohCarrier.GammaH N H') σκ x) := by
  have heq : ((WD K κ (ΓT N H' ℓ) τκ : ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) ≃ₐ[K] _) :
        ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ))).comp
        (ModularCurve.heckeBetaModLH K N H' ℓ) =
      (ModularCurve.heckeAlphaModLH K N H' ℓ).comp
        ((WD K κ (CohCarrier.GammaH N H') σκ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] _) :
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ModularCurve.intFormRatiosC K (CohCarrier.GammaH N H')) rfl ?_
    intro z hz
    obtain ⟨y, hy⟩ := gen_eq K κ hz
    show WD K κ (ΓT N H' ℓ) τκ (ModularCurve.heckeBetaModLH K N H' ℓ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩) =
      ModularCurve.heckeAlphaModLH K N H' ℓ (WD K κ (CohCarrier.GammaH N H') σκ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩)
    rw [hy, ← jq_beta κ K N H' ℓ hβκ hβK, WD_jq, h2, jq_alpha κ K N H' ℓ, WD_jq]
  exact congrArg (fun h : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (ΓT N H' ℓ)) => h x) heq

omit [NeZero ℓ] in

theorem law2' (h2' : ∀ y : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')), σκ (σκ y) = y)
    (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    WD K κ (CohCarrier.GammaH N H') σκ (WD K κ (CohCarrier.GammaH N H') σκ x) = x := by
  have heq : ((WD K κ (CohCarrier.GammaH N H') σκ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] _) :
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))).comp
        ((WD K κ (CohCarrier.GammaH N H') σκ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] _) :
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) =
      AlgHom.id K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ModularCurve.intFormRatiosC K (CohCarrier.GammaH N H')) rfl ?_
    intro z hz
    obtain ⟨y, hy⟩ := gen_eq K κ hz
    show WD K κ (CohCarrier.GammaH N H') σκ (WD K κ (CohCarrier.GammaH N H') σκ ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩) =
      ⟨z, ModularCurve.intFormRatiosC_subset K _ hz⟩
    rw [hy, WD_jq, WD_jq, h2']
  exact congrArg (fun h : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) => h x) heq

end Final
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

end BCPair
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.BCPair"

theorem solution
    (p Q : ℕ) [Fact p.Prime] [NeZero Q] (H' : Subgroup (ZMod Q)ˣ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (κ : Type*) [Field κ] [Algebra κ K]
    (q : ℕ) (hq : q.Prime) (hQK : ((Q : ℕ) : K) ≠ 0) (hqK : ((q : ℕ) : K) ≠ 0)
    (hβκ : haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.HeckeBetaModLHDefined κ Q H' q)
    (hβK : haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.HeckeBetaModLHDefined K Q H' q)
    (φκ : ↥(integralClosure ℤ ℂ) →+* κ)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (Q : ℝ), 0])
    (WQq : GL (Fin 2) ℝ) (hWQq : (WQq : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((Q * q : ℕ) : ℝ), 0])
    (σκ : haveI : NeZero q := ⟨hq.ne_zero⟩;
      ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')))
    (τκ : haveI : NeZero q := ⟨hq.ne_zero⟩;
      ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[κ]
        ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))))
    (hκ : haveI : NeZero q := ⟨hq.ne_zero⟩;

      (∀ x, τκ (ModularCurve.heckeAlphaModLH κ Q H' q x) = ModularCurve.heckeBetaModLH κ Q H' q (σκ x)) ∧

      (∀ x, τκ (ModularCurve.heckeBetaModLH κ Q H' q x) = ModularCurve.heckeAlphaModLH κ Q H' q (σκ x)) ∧

      (∀ x, σκ (σκ x) = x) ∧

      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH Q H' : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC κ pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')),
            (x : LaurentSeries κ) = ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg →
            ((σκ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H'))) : LaurentSeries κ) *
                HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) =
              HahnSeries.ofPowerSeries ℤ κ (PfW.map φκ)) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC κ pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries κ) = ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg →
            ((τκ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries κ) *
                HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) =
              HahnSeries.ofPowerSeries ℤ κ (PfW.map φκ))) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ (σ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')))
      (τ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))),

      (∀ x, τ (ModularCurve.heckeAlphaModLH K Q H' q x) = ModularCurve.heckeBetaModLH K Q H' q (σ x)) ∧

      (∀ x, τ (ModularCurve.heckeBetaModLH K Q H' q x) = ModularCurve.heckeAlphaModLH K Q H' q (σ x)) ∧

      (∀ x, σ (σ x) = x) ∧

      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH Q H' : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H'))) : LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map ((algebraMap κ K).comp φκ))) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((τ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map ((algebraMap κ K).comp φκ))) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨h1, h2, h2', hS, hS'⟩ := hκ
  refine ⟨BCPair.WD K κ (CohCarrier.GammaH Q H') σκ,
    BCPair.WD K κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) τκ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact BCPair.law1 K κ Q H' q σκ τκ hβκ hβK h1 x
  · intro x
    exact BCPair.law2 K κ Q H' q σκ τκ hβκ hβK h2 x
  · intro x
    exact BCPair.law2' K κ Q H' σκ h2' x
  · intro k f g pf pg D PfW PgW hf hg hPf hPg hg0 hPg0 x hx
    exact BCPair.lawS K κ (CohCarrier.GammaH Q H') σκ φκ WQ hS k f g pf pg D PfW PgW hf hg hPf hPg hg0 hPg0 x hx
  · intro k f g pf pg D PfW PgW hf hg hPf hPg hg0 hPg0 x hx
    exact BCPair.lawS K κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) τκ φκ WQq hS'
      k f g pf pg D PfW PgW hf hg hPf hPg hg0 hPg0 x hx

end S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP (solution)
