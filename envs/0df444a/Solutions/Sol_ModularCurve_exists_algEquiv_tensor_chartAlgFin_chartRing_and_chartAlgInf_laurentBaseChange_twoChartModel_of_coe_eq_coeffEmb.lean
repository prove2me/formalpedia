-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_laurentBaseChange_twoChartModel_of_coe_eq_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3e47f7ca-e5ce-51de-8af7-c7315b7c5cab

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_laurentBaseChange_twoChartModel_of_coe_eq_coeffEmb
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open scoped TensorProduct

noncomputable section

namespace X1CHARTBC

open ModularCurve AlgebraicCurve.CurveModel

section Emb

variable {L : Type} [Field L] {C : Type} [Field C] [Algebra L C]
variable (K : IntermediateField L (LaurentSeries L)) (B : IntermediateField C (LaurentSeries C))
variable (hmem : ∀ b : K, coeffMap (algebraMap L C) ((b : K) : LaurentSeries L) ∈ B)

def emb : K →+* B :=
  ((coeffMap (algebraMap L C)).comp (SubringClass.subtype K)).codRestrict B fun x => hmem x

theorem emb_apply (x : K) :
    emb K B hmem x = ⟨coeffMap (algebraMap L C) ((x : K) : LaurentSeries L), hmem x⟩ := rfl

theorem coe_emb (x : K) :
    ((emb K B hmem x : B) : LaurentSeries C) = coeffMap (algebraMap L C) ((x : K) : LaurentSeries L) :=
  rfl

theorem emb_inv (x : K) : emb K B hmem x⁻¹ = (emb K B hmem x)⁻¹ := map_inv₀ _ _

omit [Algebra L C] in

theorem coeffMap_algebraMap' (g : L →+* C) (c : L) :
    coeffMap g (algebraMap L (LaurentSeries L) c) = algebraMap C (LaurentSeries C) (g c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

variable {A : Type} [CommRing A] [Algebra A L] [Algebra A K] [IsScalarTower A L K]
  [Algebra A C] [IsScalarTower A L C]

theorem emb_algebraMap (a : A) :
    emb K B hmem (algebraMap A K a) = algebraMap C B (algebraMap A C a) := by
  apply Subtype.ext
  rw [coe_emb, IsScalarTower.algebraMap_apply A L K, IsScalarTower.algebraMap_apply A L C]
  change coeffMap (algebraMap L C) (algebraMap L (LaurentSeries L) (algebraMap A L a)) =
    algebraMap C (LaurentSeries C) (algebraMap L C (algebraMap A L a))
  exact coeffMap_algebraMap' _ _

end Emb

section Charts

variable {L : Type} [Field L] {C : Type} [Field C] [Algebra L C]
variable (K : IntermediateField L (LaurentSeries L)) (B : IntermediateField C (LaurentSeries C))
variable (hmem : ∀ b : K, coeffMap (algebraMap L C) ((b : K) : LaurentSeries L) ∈ B)
variable (A : Type) [CommRing A] [Algebra A L] [Algebra A K] [IsScalarTower A L K]
  [Algebra A C] [IsScalarTower A L C]

theorem emb_mem_adjoin {S : Set K} {T : Set B} (hST : ∀ s ∈ S, emb K B hmem s ∈ T) {x : K}
    (hx : x ∈ Algebra.adjoin A S) :
    emb K B hmem x ∈ Algebra.adjoin C T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hST x hx)
  | algebraMap r =>
      rw [emb_algebraMap]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem emb_mem_chartRing {S : Set K} {T : Set B} (hST : ∀ s ∈ S, emb K B hmem s ∈ T) {b : K}
    (hb : b ∈ TwoChart.chartAlg A K S) :
    emb K B hmem b ∈ chartRing C T := by
  have hint : IsIntegral (Algebra.adjoin A S) b := hb
  let ψ : ↥(Algebra.adjoin A S) →+* ↥(Algebra.adjoin C T) :=
    ((emb K B hmem).comp (Algebra.adjoin A S).val.toRingHom).codRestrict
      (Algebra.adjoin C T).toSubring fun x => emb_mem_adjoin K B hmem A hST x.2
  exact IsIntegral.map_of_comp_eq ψ (emb K B hmem) (RingHom.ext fun _ => rfl) hint

def ρ (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T) :
    ↥(TwoChart.chartAlg A K S) →+* ↥(chartRing C T) where
  toFun b := ⟨emb K B hmem b, emb_mem_chartRing K B hmem A hST b.2⟩
  map_one' := Subtype.ext (by simp only [Subalgebra.coe_one, map_one])
  map_mul' a b := Subtype.ext (by simp only [Subalgebra.coe_mul, map_mul])
  map_zero' := Subtype.ext (by simp only [Subalgebra.coe_zero, map_zero])
  map_add' a b := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])

theorem coe_ρ_apply (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (b : ↥(TwoChart.chartAlg A K S)) :
    (ρ K B hmem A S T hST b : B) = emb K B hmem b := rfl

theorem ρ_comp_algebraMap (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T) :
    (ρ K B hmem A S T hST).comp (algebraMap A ↥(TwoChart.chartAlg A K S)) =
      (algebraMap C ↥(chartRing C T)).comp (algebraMap A C) := by
  refine RingHom.ext fun q => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, coe_ρ_apply, Subalgebra.coe_algebraMap,
    Subalgebra.coe_algebraMap, emb_algebraMap]

variable (j : K)

theorem fin_sub : ∀ s ∈ ({j} : Set K), emb K B hmem s ∈ ({emb K B hmem j} : Set B) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs]

theorem inf_sub : ∀ s ∈ ({(j)⁻¹} : Set K), emb K B hmem s ∈ ({(emb K B hmem j)⁻¹} : Set B) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, emb_inv]

end Charts

section Tensor

variable {L : Type} [Field L] {C : Type} [Field C] [Algebra L C]
variable (K : IntermediateField L (LaurentSeries L)) (B : IntermediateField C (LaurentSeries C))
variable (hmem : ∀ b : K, coeffMap (algebraMap L C) ((b : K) : LaurentSeries L) ∈ B)
variable (A : Type) [CommRing A] [Algebra A L] [Algebra A K] [IsScalarTower A L K]
  [Algebra A C] [IsScalarTower A L C]

local instance instAlgebraBaseChartRing (T : Set B) : Algebra A ↥(chartRing C T) :=
  ((algebraMap C ↥(chartRing C T)).comp (algebraMap A C)).toAlgebra

set_option synthInstance.maxHeartbeats 1600000 in

def ρAlg (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T) :
    ↥(TwoChart.chartAlg A K S) →ₐ[A] ↥(chartRing C T) :=
  { ρ K B hmem A S T hST with
    commutes' := fun q => RingHom.congr_fun (ρ_comp_algebraMap K B hmem A S T hST) q }

set_option synthInstance.maxHeartbeats 1600000 in

def incAlg (T : Set B) : C →ₐ[A] ↥(chartRing C T) :=
  { algebraMap C ↥(chartRing C T) with
    commutes' := fun _ => rfl }

set_option synthInstance.maxHeartbeats 1600000 in

def θ (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T) :
    (↥(TwoChart.chartAlg A K S) ⊗[A] C) →+* ↥(chartRing C T) :=
  (Algebra.TensorProduct.lift (ρAlg K B hmem A S T hST) (incAlg B A T) fun _ _ => Commute.all _ _).toRingHom

set_option synthInstance.maxHeartbeats 1600000 in
theorem θ_tmul (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (b : ↥(TwoChart.chartAlg A K S)) (c : C) :
    θ K B hmem A S T hST (b ⊗ₜ c) = ρ K B hmem A S T hST b * algebraMap C _ c :=
  Algebra.TensorProduct.lift_tmul (ρAlg K B hmem A S T hST) (incAlg B A T) _ b c

set_option synthInstance.maxHeartbeats 1600000 in
theorem coe_θ_tmul (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (b : ↥(TwoChart.chartAlg A K S)) (c : C) :
    ((θ K B hmem A S T hST (b ⊗ₜ c) : ↥(chartRing C T)) : B) = c • (emb K B hmem b : B) := by
  rw [θ_tmul, Subalgebra.coe_mul, coe_ρ_apply, Algebra.smul_def, mul_comm]
  rfl

abbrev cm (S : Set K) : (C ⊗[A] ↥(TwoChart.chartAlg A K S)) ≃ₐ[A] (↥(TwoChart.chartAlg A K S) ⊗[A] C) :=
  Algebra.TensorProduct.comm A C ↥(TwoChart.chartAlg A K S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

def θL (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T) :
    (C ⊗[A] ↥(TwoChart.chartAlg A K S)) →ₐ[C] ↥(chartRing C T) where
  toRingHom := (θ K B hmem A S T hST).comp (cm K A S (C := C)).toRingEquiv.toRingHom
  commutes' c := by
    show θ K B hmem A S T hST ((1 : ↥(TwoChart.chartAlg A K S)) ⊗ₜ c) = algebraMap C _ c
    rw [θ_tmul, map_one, one_mul]

set_option synthInstance.maxHeartbeats 1600000 in
theorem θL_apply (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (x : C ⊗[A] ↥(TwoChart.chartAlg A K S)) :
    θL K B hmem A S T hST x = θ K B hmem A S T hST (cm K A S x) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
theorem θL_one_tmul (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (b : ↥(TwoChart.chartAlg A K S)) :
    θL K B hmem A S T hST (1 ⊗ₜ b) = ρ K B hmem A S T hST b := by
  show θ K B hmem A S T hST (b ⊗ₜ 1) = _
  rw [θ_tmul, map_one, mul_one]

set_option synthInstance.maxHeartbeats 1600000 in

theorem coe_θL_one_tmul (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (b : ↥(TwoChart.chartAlg A K S)) :
    ((θL K B hmem A S T hST (1 ⊗ₜ b) : ↥(chartRing C T)) : B) = emb K B hmem b := by
  rw [θL_one_tmul, coe_ρ_apply]

set_option synthInstance.maxHeartbeats 1600000 in
theorem θL_injective (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (h : Function.Injective (θ K B hmem A S T hST)) :
    Function.Injective (θL K B hmem A S T hST) := fun x y hxy =>
  (cm K A S).injective (h (by rwa [θL_apply, θL_apply] at hxy))

set_option synthInstance.maxHeartbeats 1600000 in
theorem θL_surjective (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (h : Function.Surjective (θ K B hmem A S T hST)) :
    Function.Surjective (θL K B hmem A S T hST) := fun z => by
  obtain ⟨w, hw⟩ := h z
  exact ⟨(cm K A S).symm w, by rw [θL_apply, (cm K A S).apply_symm_apply, hw]⟩

set_option synthInstance.maxHeartbeats 1600000 in

def chartEquivL (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (hinj : Function.Injective (θ K B hmem A S T hST))
    (hsurj : Function.Surjective (θ K B hmem A S T hST)) :
    (C ⊗[A] ↥(TwoChart.chartAlg A K S)) ≃ₐ[C] ↥(chartRing C T) :=
  AlgEquiv.ofBijective (θL K B hmem A S T hST)
    ⟨θL_injective K B hmem A S T hST hinj, θL_surjective K B hmem A S T hST hsurj⟩

set_option synthInstance.maxHeartbeats 1600000 in
theorem coe_chartEquivL_one_tmul (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (hinj : Function.Injective (θ K B hmem A S T hST))
    (hsurj : Function.Surjective (θ K B hmem A S T hST)) (b : ↥(TwoChart.chartAlg A K S)) :
    ((chartEquivL K B hmem A S T hST hinj hsurj (1 ⊗ₜ b) : ↥(chartRing C T)) : B) = emb K B hmem b :=
  coe_θL_one_tmul K B hmem A S T hST b

end Tensor

section NormalForm

open TensorProduct

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {O : Type*} [AddCommGroup O] [Module R O]
  {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]
  {C : Type*} [Field C] [Algebra L C] [Module R C] [IsScalarTower R L C] [Module.IsTorsionFree R C]

omit [IsDomain R] [IsPrincipalIdealRing R] [Module.IsTorsionFree R C] in

theorem linearIndependent_of_basis {V : Submodule R C} {ι : Type*} (b : Module.Basis ι R V) :
    LinearIndependent L (fun k => (b k : C)) := by
  have h : LinearIndependent R (fun k => (b k : C)) :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  exact (LinearIndependent.iff_fractionRing R L).mp h

theorem injective_of_coeff (v : O →+ LaurentSeries L) (hv : Function.Injective v)
    (Φ : O ⊗[R] C →+ LaurentSeries C)
    (hΦ : ∀ (a : O) (c : C) (n : ℤ),
      (Φ (a ⊗ₜ[R] c)).coeff n = c * algebraMap L C ((v a).coeff n)) :
    Function.Injective Φ := by
  classical
  refine (injective_iff_map_eq_zero Φ).mpr fun t ht => ?_
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t

  let V : Submodule R C := Submodule.span R (↑(s.image Prod.snd) : Set C)
  haveI : Module.Finite R V := Module.Finite.span_of_finite R (s.image Prod.snd).finite_toSet
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := V)
  have hli : LinearIndependent L (fun k => (b k : C)) := linearIndependent_of_basis b
  have hmem : ∀ i ∈ s, i.2 ∈ V := fun i hi =>
    Submodule.subset_span (by
      rw [Finset.coe_image]
      exact Set.mem_image_of_mem _ hi)

  let c' : s → V := fun i => ⟨i.1.2, hmem i.1 i.2⟩
  let a' : Fin n → O := fun k => ∑ i : s, (b.repr (c' i) k) • i.1.1
  have key : ∑ i ∈ s, i.1 ⊗ₜ[R] i.2 = ∑ k : Fin n, a' k ⊗ₜ[R] (b k : C) := by
    calc ∑ i ∈ s, i.1 ⊗ₜ[R] i.2
        = ∑ i : s, i.1.1 ⊗ₜ[R] ((c' i : V) : C) :=
          (Finset.sum_coe_sort s (fun i => i.1 ⊗ₜ[R] i.2)).symm
      _ = ∑ i : s, ∑ k : Fin n, ((b.repr (c' i) k) • i.1.1) ⊗ₜ[R] (b k : C) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (c' i)]
          rw [Submodule.coe_sum, tmul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Submodule.coe_smul, smul_tmul]
      _ = ∑ k : Fin n, ∑ i : s, ((b.repr (c' i) k) • i.1.1) ⊗ₜ[R] (b k : C) :=
          Finset.sum_comm
      _ = ∑ k : Fin n, a' k ⊗ₜ[R] (b k : C) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_tmul]
  rw [key, map_sum] at ht

  have hcoeff : ∀ (k : Fin n) (m : ℤ), (v (a' k)).coeff m = 0 := by
    intro k m
    have h0 : ∑ j : Fin n, ((v (a' j)).coeff m) • (b j : C) = 0 := by
      have h1 := congrArg (fun x : LaurentSeries C => x.coeff m) ht
      simp only [HahnSeries.coeff_sum, hΦ, HahnSeries.coeff_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp hli _ h0 k
  have ha' : ∀ k : Fin n, a' k = 0 := fun k =>
    hv (by
      rw [map_zero]
      exact HahnSeries.coeff_inj.mp (funext fun m => by rw [hcoeff k m, HahnSeries.coeff_zero]))
  rw [key]
  exact Finset.sum_eq_zero fun k _ => by rw [ha' k, zero_tmul]

end NormalForm

section Inj

open TensorProduct

variable {L : Type} [Field L] {C : Type} [Field C] [Algebra L C]
variable (K : IntermediateField L (LaurentSeries L)) (B : IntermediateField C (LaurentSeries C))
variable (hmem : ∀ b : K, coeffMap (algebraMap L C) ((b : K) : LaurentSeries L) ∈ B)
variable (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Algebra A L] [IsFractionRing A L]
  [Algebra A K] [IsScalarTower A L K] [Algebra A C] [IsScalarTower A L C]

omit [IsDomain A] [IsPrincipalIdealRing A] [IsFractionRing A L] in
set_option synthInstance.maxHeartbeats 1600000 in

theorem coeff_coe_θ_tmul (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (b : ↥(TwoChart.chartAlg A K S)) (c : C) (n : ℤ) :
    (((θ K B hmem A S T hST (b ⊗ₜ c) : ↥(chartRing C T)) : B) : LaurentSeries C).coeff n =
      c * algebraMap L C ((((b : K) : LaurentSeries L)).coeff n) := by
  rw [coe_θ_tmul, Algebra.smul_def, MulMemClass.coe_mul,
    show ((algebraMap C B c : B) : LaurentSeries C) = HahnSeries.single 0 c from
      algebraMap_laurentSeries_eq_single C c,
    HahnSeries.coeff_single_zero_mul]
  rfl

def coeLS (S : Set K) : ↥(TwoChart.chartAlg A K S) →+ LaurentSeries L :=
  AddMonoidHom.mk' (fun b => ((b : K) : LaurentSeries L)) fun _ _ => rfl

omit [IsDomain A] [IsPrincipalIdealRing A] [Algebra A L] [IsFractionRing A L] [IsScalarTower A L ↥K] in
theorem coeLS_injective (S : Set K) : Function.Injective (coeLS K A S) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

set_option synthInstance.maxHeartbeats 1600000 in

def θLS (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T) :
    (↥(TwoChart.chartAlg A K S) ⊗[A] C) →+ LaurentSeries C :=
  AddMonoidHom.mk'
    (fun t => (((θ K B hmem A S T hST t : ↥(chartRing C T)) : B) : LaurentSeries C))
    fun x y => by simp only [(θ K B hmem A S T hST).map_add]; rfl

set_option synthInstance.maxHeartbeats 1600000 in

theorem θ_injective (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T) :
    Function.Injective (θ K B hmem A S T hST) := by
  haveI : Module.IsTorsionFree A C := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A L C]
    exact (algebraMap L C).injective.comp (IsFractionRing.injective A L)
  have h : Function.Injective (θLS K B hmem A S T hST) :=
    injective_of_coeff (coeLS K A S) (coeLS_injective K A S) (θLS K B hmem A S T hST)
      fun b c n => coeff_coe_θ_tmul K B hmem A S T hST b c n
  intro x y hxy
  exact h (congrArg (fun z : ↥(chartRing C T) => ((z : B) : LaurentSeries C)) hxy)

end Inj

section Surj

variable {L : Type} [Field L] {C : Type} [Field C] [Algebra L C]
variable (K : IntermediateField L (LaurentSeries L)) (B : IntermediateField C (LaurentSeries C))
variable (hmem : ∀ b : K, coeffMap (algebraMap L C) ((b : K) : LaurentSeries L) ∈ B)
variable (A : Type) [CommRing A] [Algebra A L] [Algebra A K] [IsScalarTower A L K]
  [Algebra A C] [IsScalarTower A L C]

set_option synthInstance.maxHeartbeats 1600000 in

theorem surjective_θ_of_le_span (S : Set K) (T : Set B) (hST : ∀ s ∈ S, emb K B hmem s ∈ T)
    (hgen : (chartRing C T).toSubmodule ≤
      Submodule.span C (Set.range fun b : ↥(TwoChart.chartAlg A K S) => (emb K B hmem b : B))) :
    Function.Surjective (θ K B hmem A S T hST) := by
  intro y
  have hrange :
      (Set.range fun b : ↥(TwoChart.chartAlg A K S) => (emb K B hmem b : B)) =
        ⇑(chartRing C T).val.toLinearMap '' Set.range ⇑(ρ K B hmem A S T hST) := by
    rw [← Set.range_comp]; rfl
  have hy₀ : (y : B) ∈ Submodule.map (chartRing C T).val.toLinearMap
        (Submodule.span C (Set.range (ρ K B hmem A S T hST))) := by
    rw [Submodule.map_span, ← hrange]
    exact hgen y.2
  obtain ⟨y', hy', hyy'⟩ := Submodule.mem_map.mp hy₀
  obtain rfl : y' = y := Subtype.ext hyy'
  clear hy₀ hyy' hgen hrange
  refine Submodule.span_induction ?mem ?zero ?add ?smul hy'
  case mem =>
    rintro _ ⟨b, rfl⟩
    exact ⟨b ⊗ₜ (1 : C), by rw [θ_tmul, map_one, mul_one]⟩
  case zero =>
    exact ⟨0, (θ K B hmem A S T hST).map_zero⟩
  case add =>
    rintro x₁ x₂ _ _ ⟨z₁, h₁⟩ ⟨z₂, h₂⟩
    exact ⟨z₁ + z₂, ((θ K B hmem A S T hST).map_add z₁ z₂).trans (by rw [h₁, h₂])⟩
  case smul =>
    rintro c x _ ⟨z, hz⟩
    refine ⟨((1 : ↥(TwoChart.chartAlg A K S)) ⊗ₜ[A] c) * z, ?_⟩
    rw [(θ K B hmem A S T hST).map_mul, hz, θ_tmul, map_one, one_mul]
    exact (Algebra.smul_def c x).symm

end Surj

section RatLoc

theorem ringHom_apply_eq_ratCast {S : Subring ℚ} {R : Type*} [DivisionRing R] [Algebra ℚ R]
    (f : ↥S →+* R) (q : ↥S) : f q = ((q : ℚ) : R) := by
  have hd : (((q : ℚ).den : ℕ) : R) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ R)]
    exact (map_ne_zero (algebraMap ℚ R)).mpr (Nat.cast_ne_zero.mpr (q : ℚ).den_ne_zero)
  have hmul : f q * (((q : ℚ).den : ℕ) : R) = (((q : ℚ).num : ℤ) : R) := by
    rw [← map_natCast f, ← map_intCast f, ← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (q : ℚ)
  rw [Rat.cast_def, eq_div_iff hd, hmul]

variable (A : Type) [CommRing A] [IsLocalRing A] (L : Type) [Field L] [Algebra A L] (p : ℕ)

theorem exists_algebraMap_eq_ratCast (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (r : ↥(GaloisRep.ratLocalizedAt p)) : ∃ a : A, algebraMap A L a = ((r : ℚ) : L) := by
  have hden : IsUnit (((r : ℚ).den : ℕ) : A) := by
    by_contra hu
    have hmemd : (((r : ℚ).den : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hu
    have hcop : IsCoprime (((r : ℚ).den : ℕ) : ℤ) ((p : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr r.2
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have h := congrArg (Int.cast : ℤ → A) huv
      push_cast at h
      rw [← h]
      exact add_mem (Ideal.mul_mem_left _ _ hmemd) (Ideal.mul_mem_left _ _ hAp)
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨d, hd⟩ := hden
  refine ⟨((r : ℚ).num : A) * ↑d⁻¹, ?_⟩
  have hinv : algebraMap A L ↑d⁻¹ = ((((r : ℚ).den : ℕ) : L))⁻¹ := by
    rw [← map_natCast (algebraMap A L), ← hd]
    exact map_units_inv (algebraMap A L) d
  rw [map_mul, map_intCast, hinv, Rat.cast_def, div_eq_mul_inv]

end RatLoc

section Supply

variable (L : Type) [Field L] [CharZero L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def ι : ↥F₀ →+* ↥(laurentBaseChange L F₀) :=
  ((coeffEmb L).comp (SubringClass.subtype F₀)).codRestrict (laurentBaseChange L F₀)
    fun x => coeffEmb_mem_laurentBaseChange L x.2

theorem coe_ι (x : ↥F₀) : ((ι L F₀ x : ↥(laurentBaseChange L F₀)) : LaurentSeries L) =
    coeffEmb L ((x : ↥F₀) : LaurentSeries ℚ) := rfl

variable (A : Type) [CommRing A] [IsLocalRing A] [Algebra A L]
  [Algebra A ↥(laurentBaseChange L F₀)] [IsScalarTower A L ↥(laurentBaseChange L F₀)]
  (p : ℕ)

theorem exists_ι_algebraMap_eq (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (r : ↥(GaloisRep.ratLocalizedAt p)) :
    ∃ a : A, ι L F₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ r) =
      algebraMap A ↥(laurentBaseChange L F₀) a := by
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_ratCast A L p hAp r
  refine ⟨a, Subtype.ext ?_⟩
  rw [coe_ι, IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀)]
  change coeffEmb L _ = algebraMap L (LaurentSeries L) (algebraMap A L a)
  rw [ha,
    show ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ r : ↥F₀) : LaurentSeries ℚ) =
        ((r : ℚ) : LaurentSeries ℚ) from
      ringHom_apply_eq_ratCast ((SubringClass.subtype F₀ : ↥F₀ →+* LaurentSeries ℚ).comp
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀)) r,
    ← eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)), coeffEmb, coeffMap_algebraMap',
    eq_ratCast]

theorem ι_mem_adjoin (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) {S₀ : Set ↥F₀}
    {S : Set ↥(laurentBaseChange L F₀)} (hST : ∀ s ∈ S₀, ι L F₀ s ∈ S) {x : ↥F₀}
    (hx : x ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S₀) :
    ι L F₀ x ∈ Algebra.adjoin A S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hST x hx)
  | algebraMap r =>
      obtain ⟨a, ha⟩ := exists_ι_algebraMap_eq L F₀ A p hAp r
      rw [ha]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem ι_mem_chartAlg (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) {S₀ : Set ↥F₀}
    {S : Set ↥(laurentBaseChange L F₀)} (hST : ∀ s ∈ S₀, ι L F₀ s ∈ S) {b : ↥F₀}
    (hb : b ∈ TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S₀) :
    ι L F₀ b ∈ TwoChart.chartAlg A ↥(laurentBaseChange L F₀) S := by
  have hint : IsIntegral (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S₀) b := hb
  let ψ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S₀) →+* ↥(Algebra.adjoin A S) :=
    ((ι L F₀).comp (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S₀).val.toRingHom).codRestrict
      (Algebra.adjoin A S).toSubring fun x => ι_mem_adjoin L F₀ A p hAp hST x.2
  exact IsIntegral.map_of_comp_eq ψ (ι L F₀) (RingHom.ext fun _ => rfl) hint

variable [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
variable (hmem : ∀ b : ↥(laurentBaseChange L F₀), coeffMap (algebraMap L (AlgebraicClosure ℚ))
  ((b : ↥(laurentBaseChange L F₀)) : LaurentSeries L) ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀)

theorem emb_ι (x : ↥F₀) :
    emb (laurentBaseChange L F₀) (laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem (ι L F₀ x) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((x : ↥F₀) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := by
  apply Subtype.ext
  rw [coe_emb, coe_ι, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) _

omit [Algebra A (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)] in

theorem chartRing_le_span (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (j₀ : ↥F₀) (j : ↥(laurentBaseChange L F₀)) (hj : ι L F₀ j₀ = j) [Fact (j ≠ 0)] :
    ((chartRing (AlgebraicClosure ℚ)
        ({emb (laurentBaseChange L F₀) (laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem j} :
          Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : ↥(TwoChart.chartAlgFin A ↥(laurentBaseChange L F₀) j) =>
        (emb (laurentBaseChange L F₀) (laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem b :
          ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) ∧
    ((chartRing (AlgebraicClosure ℚ)
        ({(emb (laurentBaseChange L F₀) (laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem j)⁻¹} :
          Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : ↥(TwoChart.chartAlgInf A ↥(laurentBaseChange L F₀) j) =>
        (emb (laurentBaseChange L F₀) (laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem b :
          ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) := by
  haveI : Fact (j₀ ≠ 0) := ⟨fun h => (Fact.out : j ≠ 0) (by rw [← hj, h, map_zero])⟩
  have hjb : ((emb (laurentBaseChange L F₀) (laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem j :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((j₀ : ↥F₀) : LaurentSeries ℚ) := by
    rw [← hj, emb_ι]
  obtain ⟨hfin, hinf⟩ :=
    ModularCurve.chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg F₀ p j₀ _ hjb
  have hfinST : ∀ s ∈ ({j₀} : Set ↥F₀), ι L F₀ s ∈ ({j} : Set ↥(laurentBaseChange L F₀)) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs ⊢
    rw [hs, hj]
  have hinfST : ∀ s ∈ ({j₀⁻¹} : Set ↥F₀), ι L F₀ s ∈ ({(j)⁻¹} : Set ↥(laurentBaseChange L F₀)) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs ⊢
    rw [hs, map_inv₀, hj]
  refine ⟨hfin.trans (Submodule.span_mono ?_), hinf.trans (Submodule.span_mono ?_)⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨⟨ι L F₀ b, ι_mem_chartAlg L F₀ A p hAp hfinST b.2⟩, emb_ι L F₀ hmem b⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨⟨ι L F₀ b, ι_mem_chartAlg L F₀ A p hAp hinfST b.2⟩, emb_ι L F₀ hmem b⟩

end Supply

end X1CHARTBC

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j₀ : ↥F₀)
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥(ModularCurve.laurentBaseChange L F₀)] [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L F₀)]
    (j : ↥(ModularCurve.laurentBaseChange L F₀)) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ((j₀ : ↥F₀) : LaurentSeries ℚ)) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (jb : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((j₀ : ↥F₀) : LaurentSeries ℚ)) [Fact (jb ≠ 0)]
    (hmem : ∀ b : ↥(ModularCurve.laurentBaseChange L F₀), ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    (∃ eFin : (AlgebraicClosure ℚ) ⊗[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L F₀)) j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀))),
      ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L F₀)) j),
        ((eFin ((1 : AlgebraicClosure ℚ) ⊗ₜ[A] b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L), hmem b⟩) ∧
    (∃ eInf : (AlgebraicClosure ℚ) ⊗[A] ↥(ModularCurve.TwoChart.chartAlgInf A (↥(ModularCurve.laurentBaseChange L F₀)) j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀))),
      ∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥(ModularCurve.laurentBaseChange L F₀)) j),
        ((eInf ((1 : AlgebraicClosure ℚ) ⊗ₜ[A] b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L), hmem b⟩) := by
  have hj' : X1CHARTBC.ι L F₀ j₀ = j := Subtype.ext hj.symm

  obtain rfl : jb = X1CHARTBC.emb (ModularCurve.laurentBaseChange L F₀)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem j := by
    apply Subtype.ext
    rw [hjb, ← hj', X1CHARTBC.emb_ι]
  obtain ⟨hfin, hinf⟩ := X1CHARTBC.chartRing_le_span L F₀ A p hmem hAp j₀ j hj'
  exact ⟨⟨X1CHARTBC.chartEquivL _ _ hmem A _ _ (X1CHARTBC.fin_sub _ _ hmem j)
      (X1CHARTBC.θ_injective _ _ hmem A _ _ _)
      (X1CHARTBC.surjective_θ_of_le_span _ _ hmem A _ _ _ hfin),
    fun b => X1CHARTBC.coe_chartEquivL_one_tmul _ _ hmem A _ _ _ _ _ b⟩,
  ⟨X1CHARTBC.chartEquivL _ _ hmem A _ _ (X1CHARTBC.inf_sub _ _ hmem j)
      (X1CHARTBC.θ_injective _ _ hmem A _ _ _)
      (X1CHARTBC.surjective_θ_of_le_span _ _ hmem A _ _ _ hinf),
    fun b => X1CHARTBC.coe_chartEquivL_one_tmul _ _ hmem A _ _ _ _ _ b⟩⟩

end

end S_ModularCurve_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_laurentBaseChange_twoChartModel_of_coe_eq_coeffEmb
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_laurentBaseChange_twoChartModel_of_coe_eq_coeffEmb (solution)
