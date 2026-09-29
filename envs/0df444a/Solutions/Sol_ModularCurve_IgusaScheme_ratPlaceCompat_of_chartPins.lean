-- Prove2me | solution 1 for ModularCurve.IgusaScheme.ratPlaceCompat_of_chartPins
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6ca7e194-91eb-513b-b7cc-f675e9a6c2c7

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap
import Theorems.Thm_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iotaInf_comap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve"
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

universe u

namespace P3core

section Points
variable {A F' : Type u} [CommRing A] [Field F'] {X : Scheme.{u}}

theorem range_base_eq_singleton (p : Spec (CommRingCat.of F') ⟶ X) :
    Set.range p.base = {p.base (IsLocalRing.closedPoint F')} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    have hq : q = IsLocalRing.closedPoint F' := Subsingleton.elim (α := PrimeSpectrum F') _ _
    rw [hq]
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨_, rfl⟩

theorem exists_SpecMap_comp_eq_of_mem_range (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (p : Spec (CommRingCat.of F') ⟶ X) (hp : p.base (IsLocalRing.closedPoint F') ∈ Set.range ι.base) :
    ∃ φ : A →+* F', Spec.map (CommRingCat.ofHom φ) ≫ ι = p := by
  have hrange : Set.range p.base ⊆ Set.range ι.base := by
    rw [range_base_eq_singleton]
    exact Set.singleton_subset_iff.mpr hp
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ι p hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem ringHom_unique_of_SpecMap_comp_eq (ι : Spec (CommRingCat.of A) ⟶ X) [Mono ι] (φ φ' : A →+* F')
    (h : Spec.map (CommRingCat.ofHom φ') ≫ ι = Spec.map (CommRingCat.ofHom φ) ≫ ι) : φ' = φ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono ι).mp h))

theorem SpecMap_comp_base_closedPoint (ι : Spec (CommRingCat.of A) ⟶ X) (φ : A →+* F') :
    (Spec.map (CommRingCat.ofHom φ) ≫ ι).base (IsLocalRing.closedPoint F') =
      ι.base ((Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint F')) :=
  rfl

theorem SpecMap_comp_base_closedPoint_mem_range (ι : Spec (CommRingCat.of A) ⟶ X) (φ : A →+* F') :
    (Spec.map (CommRingCat.ofHom φ) ≫ ι).base (IsLocalRing.closedPoint F') ∈ Set.range ι.base :=
  ⟨_, (SpecMap_comp_base_closedPoint ι φ).symm⟩

theorem asIdeal_SpecMap_base_closedPoint {R : Type u} [CommRing R] (φ : R →+* F') :
    ((Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint F')).asIdeal = RingHom.ker φ := by
  show Ideal.comap φ (IsLocalRing.maximalIdeal F') = RingHom.ker φ
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]

theorem exists_ringHom_point_of_mem_range (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (p : Spec (CommRingCat.of F') ⟶ X) (hp : p.base (IsLocalRing.closedPoint F') ∈ Set.range ι.base) :
    ∃ (φ : A →+* F') (P : Spec (CommRingCat.of A)),
      Spec.map (CommRingCat.ofHom φ) ≫ ι = p ∧
      P = (Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint F') ∧
      p.base (IsLocalRing.closedPoint F') = ι.base P ∧ P.asIdeal = RingHom.ker φ := by
  obtain ⟨φ, hφ⟩ := exists_SpecMap_comp_eq_of_mem_range ι p hp
  refine ⟨φ, _, hφ, rfl, ?_, asIdeal_SpecMap_base_closedPoint φ⟩
  rw [← hφ, SpecMap_comp_base_closedPoint]

end Points

end P3core

namespace P3

theorem hom_SpecRat_ext {L : Type} [CommRing L]
    (f g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of ℚ)) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

theorem SpecMap_comp_eq_comp_inv_of_pins
    {A A₀ B L : Type} [CommRing A] [CommRing A₀] [CommRing B] [CommRing L]
    {X S C C₀ Y : Scheme.{0}} (c : X ⟶ S) (gS : Spec (CommRingCat.of ℚ) ⟶ S) (p : Y ⟶ X)
    (eC : C ⟶ Y) (e₀ : C₀ ⟶ pullback c gS) [IsIso e₀]
    (ι : Spec (CommRingCat.of A) ⟶ C) (ι₀ : Spec (CommRingCat.of A₀) ⟶ C₀)
    (ιX : Spec (CommRingCat.of B) ⟶ X)
    (ε : B →+* A) (ε₀ : B →+* A₀) (ψ : A₀ →+* A) (hψ : ψ.comp ε₀ = ε)
    (pin : ι ≫ eC ≫ p = Spec.map (CommRingCat.ofHom ε) ≫ ιX)
    (pin₀ : ι₀ ≫ e₀ ≫ pullback.fst c gS = Spec.map (CommRingCat.ofHom ε₀) ≫ ιX)
    (x : Spec (CommRingCat.of L) ⟶ C) (φ : A →+* L) (hx : Spec.map (CommRingCat.ofHom φ) ≫ ι = x)
    (y : Spec (CommRingCat.of L) ⟶ pullback c gS) (hy : y ≫ pullback.fst c gS = x ≫ eC ≫ p) :
    Spec.map (CommRingCat.ofHom (φ.comp ψ)) ≫ ι₀ = y ≫ inv e₀ := by
  have key : (Spec.map (CommRingCat.ofHom (φ.comp ψ)) ≫ ι₀) ≫ e₀ = y := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pin₀, hy, ← hx, Category.assoc, pin, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, hψ]
    · exact hom_SpecRat_ext _ _
  rw [← key]
  simp

theorem base_comp_inv_closedPoint_eq_of_pins
    {A A₀ B L : Type} [CommRing A] [CommRing A₀] [CommRing B] [Field L]
    {X S C C₀ Y : Scheme.{0}} (c : X ⟶ S) (gS : Spec (CommRingCat.of ℚ) ⟶ S) (p : Y ⟶ X)
    (eC : C ⟶ Y) (e₀ : C₀ ⟶ pullback c gS) [IsIso e₀]
    (ι : Spec (CommRingCat.of A) ⟶ C) (ι₀ : Spec (CommRingCat.of A₀) ⟶ C₀)
    (ιX : Spec (CommRingCat.of B) ⟶ X)
    (ε : B →+* A) (ε₀ : B →+* A₀) (ψ : A₀ →+* A) (hψ : ψ.comp ε₀ = ε)
    (pin : ι ≫ eC ≫ p = Spec.map (CommRingCat.ofHom ε) ≫ ιX)
    (pin₀ : ι₀ ≫ e₀ ≫ pullback.fst c gS = Spec.map (CommRingCat.ofHom ε₀) ≫ ιX)
    (x : Spec (CommRingCat.of L) ⟶ C) (φ : A →+* L) (hx : Spec.map (CommRingCat.ofHom φ) ≫ ι = x)
    (y : Spec (CommRingCat.of L) ⟶ pullback c gS) (hy : y ≫ pullback.fst c gS = x ≫ eC ≫ p) :
    (y ≫ inv e₀).base (IsLocalRing.closedPoint L) =
      ι₀.base ((Spec.map (CommRingCat.ofHom (φ.comp ψ))).base (IsLocalRing.closedPoint L)) ∧
    ((Spec.map (CommRingCat.ofHom (φ.comp ψ))).base (IsLocalRing.closedPoint L)).asIdeal =
      (RingHom.ker φ).comap ψ := by
  refine ⟨?_, ?_⟩
  · rw [← SpecMap_comp_eq_comp_inv_of_pins c gS p eC e₀ ι ι₀ ιX ε ε₀ ψ hψ pin pin₀ x φ hx y hy]
    rfl
  · show Ideal.comap (φ.comp ψ) (IsLocalRing.maximalIdeal L) = (RingHom.ker φ).comap ψ
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, RingHom.comap_ker]

end P3

namespace QFormP3
p2m_open "AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel"
universe v
theorem not_mem_range_ι₀_of_asIdeal_eq_comap
    (K₀ : Type v) [Field K₀] {L₀ : Type v} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type v) [Field K] {L : Type v} [Field L] [Algebra K L] (t : L)
    [Fact (t₀ ≠ 0)] [Fact (t ≠ 0)]
    (ψ : ↥(chartRing K₀ ({t₀⁻¹} : Set L₀)) →+* ↥(chartRing K ({t⁻¹} : Set L)))
    (hψ : ψ (tInvChart K₀ t₀) = tInvChart K t)
    {x : glued K t} (hx : x ∉ Set.range (ι₀ K t).base)
    (xb : XInf K t) (hxb : (CurveModel.ιInf K t).base xb = x)
    {y : glued K₀ t₀} (yb : XInf K₀ t₀) (hyb : (CurveModel.ιInf K₀ t₀).base yb = y)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    y ∉ Set.range (ι₀ K₀ t₀).base := by
  rw [← hyb, ιInf_mem_range_ι₀_iff, not_not, h, Ideal.mem_comap, hψ]
  have hx' := hx
  rw [← hxb, ιInf_mem_range_ι₀_iff, not_not] at hx'
  exact hx'
end QFormP3

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place CurveModel.X₀ CurveModel.XInf CurveModel.ι₀ CurveModel.ιInf CurveModel.mem_range_ι₀_or_mem_range_ιInf CurveModel.ofGenerator CurveModel CurveModel.pointEquivPlace_apply CurveModel.chartRing CurveModel.placeOfPoint_ofGenerator_iota0_comap CurveModel.placeOfPoint_ofGenerator_iotaInf_comap"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "tChart tInvChart coe_tInvChart X₀ XInf glued ι₀ ιInf mem_range_ι₀_or_mem_range_ιInf ιInf_mem_range_ι₀_iff ofGenerator pointEquivPlace pointEquivPlace_apply placeOfPoint toBase C chartRing mem_chartRing_iff placeOfPoint_ofGenerator_iota0_comap placeOfPoint_ofGenerator_iotaInf_comap"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

section ChartRingMap

variable {K₀ K F₀ F : Type u} [Field K₀] [Field K] [Field F₀] [Field F]
  [Algebra K₀ F₀] [Algebra K F]
  (φ : F₀ →+* F) (hφ : ∀ c : K₀, φ (algebraMap K₀ F₀ c) ∈ Set.range (algebraMap K F))

include hφ in

theorem map_mem_adjoin_of_forall_map_mem {S : Set F₀} {T : Set F} (hST : ∀ s ∈ S, φ s ∈ T)
    {x : F₀} (hx : x ∈ Algebra.adjoin K₀ S) : φ x ∈ Algebra.adjoin K T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hST x hx)
  | algebraMap r =>
      obtain ⟨c, hc⟩ := hφ r
      rw [← hc]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

include hφ in

theorem map_mem_chartRing_of_forall_map_mem {S : Set F₀} {T : Set F} (hST : ∀ s ∈ S, φ s ∈ T)
    {x : F₀} (hx : x ∈ chartRing K₀ S) : φ x ∈ chartRing K T := by
  rw [mem_chartRing_iff] at hx ⊢
  let ψ : ↥(Algebra.adjoin K₀ S) →+* ↥(Algebra.adjoin K T) :=
    (φ.comp (Algebra.adjoin K₀ S).val.toRingHom).codRestrict (Algebra.adjoin K T).toSubring
      fun x => map_mem_adjoin_of_forall_map_mem φ hφ hST x.2
  exact IsIntegral.map_of_comp_eq ψ φ (RingHom.ext fun _ => rfl) hx

def chartRingMap {S : Set F₀} {T : Set F} (hST : ∀ s ∈ S, φ s ∈ T) :
    ↥(chartRing K₀ S) →+* ↥(chartRing K T) where
  toFun b := ⟨φ b, map_mem_chartRing_of_forall_map_mem φ hφ hST b.2⟩
  map_one' := Subtype.ext (by simp only [Subalgebra.coe_one, map_one])
  map_mul' a b := Subtype.ext (by simp only [Subalgebra.coe_mul, map_mul])
  map_zero' := Subtype.ext (by simp only [Subalgebra.coe_zero, map_zero])
  map_add' a b := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])

@[scoped simp] theorem coe_chartRingMap_apply {S : Set F₀} {T : Set F} (hST : ∀ s ∈ S, φ s ∈ T)
    (b : ↥(chartRing K₀ S)) : (chartRingMap φ hφ hST b : F) = φ b := rfl

omit hφ in

theorem forall_mem_singleton_map_mem {t₀ : F₀} {t : F} (h : φ t₀ = t) :
    ∀ s ∈ ({t₀} : Set F₀), φ s ∈ ({t} : Set F) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, h]

omit hφ in
theorem forall_mem_singleton_inv_map_mem {t₀ : F₀} {t : F} (h : φ t₀ = t) :
    ∀ s ∈ ({t₀⁻¹} : Set F₀), φ s ∈ ({t⁻¹} : Set F) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, map_inv₀, h]

theorem ratCast_mem_range_algebraMap [CharZero K] (φ' : F₀ →+* F) [Algebra ℚ F₀] (c : ℚ) :
    φ' (algebraMap ℚ F₀ c) ∈ Set.range (algebraMap K F) :=
  ⟨(c : K), by rw [map_ratCast, eq_ratCast, map_ratCast]⟩

end ChartRingMap

end AlgebraicCurve.CurveModel
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve"

namespace P3prime

theorem comp_eq_of_forall_apply_one_tmul
    {R A k₀ k S₀ S : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing k₀] [Algebra R k₀] [CommRing k] [Algebra R k]
    [CommRing S₀] [Algebra k₀ S₀] [CommRing S] [Algebra k S]
    (e₀ : k₀ ⊗[R] A ≃ₐ[k₀] S₀) (e : k ⊗[R] A ≃ₐ[k] S) (ψ₀ : S₀ →+* S)
    (hcomm : ∀ a : A, ψ₀ (e₀ (1 ⊗ₜ a)) = e (1 ⊗ₜ a)) :
    ψ₀.comp (e₀.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := k₀) (B := A)).toRingHom)
      = e.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := A)).toRingHom :=
  RingHom.ext fun a => by
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply]
    exact hcomm a

theorem forall_apply_one_tmul_of_comp_eq
    {R A k₀ k S₀ S : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing k₀] [Algebra R k₀] [CommRing k] [Algebra R k]
    [CommRing S₀] [Algebra k₀ S₀] [CommRing S] [Algebra k S]
    (e₀ : k₀ ⊗[R] A ≃ₐ[k₀] S₀) (e : k ⊗[R] A ≃ₐ[k] S) (ψ₀ : S₀ →+* S)
    (h : ψ₀.comp (e₀.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := k₀) (B := A)).toRingHom)
      = e.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := A)).toRingHom) (a : A) :
    ψ₀ (e₀ (1 ⊗ₜ a)) = e (1 ⊗ₜ a) := by
  have := RingHom.congr_fun h a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Algebra.TensorProduct.includeRight_apply] at this
  exact this

end P3prime
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme IgusaScheme.ιFin IgusaScheme.ιInf modularFunctionFieldFull coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldBar baseChangeEquiv baseChangeEquiv_one_tmul"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull chartAlgFin chartAlgInf XInf ιFin ιInf igusaTo"
namespace P3psi
p2m_open "ModularCurve.IgusaScheme ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel ModularCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve ModularCurve.CharPModel"
open scoped TensorProduct

variable (N : ℕ) [NeZero N]

abbrev φF : ↥(modularFunctionFieldFull N) →+* modularFunctionFieldBar N :=
  (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
      (B := ↥(modularFunctionFieldFull N))).toRingHom

omit [NeZero N] in
theorem φF_apply (f : ↥(modularFunctionFieldFull N)) :
    φF N f = ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ := by
  rw [← baseChangeEquiv_one_tmul]
  rfl

theorem φF_jFull : φF N (jFull N) = jBar N := by
  rw [φF_apply]
  rfl

theorem φF_jFull_inv : φF N (jFull N)⁻¹ = (jBar N)⁻¹ := by
  rw [map_inv₀, φF_jFull]

omit [NeZero N] in
theorem φF_algebraMap_mem (c : ℚ) :
    φF N (algebraMap ℚ ↥(modularFunctionFieldFull N) c) ∈
      Set.range (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
  ratCast_mem_range_algebraMap (K := AlgebraicClosure ℚ) (φF N) c

def ψ₀ : ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))) :=
  chartRingMap (φF N) (φF_algebraMap_mem N) (forall_mem_singleton_map_mem (φF N) (φF_jFull N))

def ψInf : ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))) :=
  chartRingMap (φF N) (φF_algebraMap_mem N) (forall_mem_singleton_inv_map_mem (φF N) (φF_jFull N))

@[scoped simp] theorem coe_ψ₀_apply (a : ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) :
    (ψ₀ N a : modularFunctionFieldBar N) = φF N a := rfl

@[scoped simp] theorem coe_ψInf_apply (a : ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) :
    (ψInf N a : modularFunctionFieldBar N) = φF N a := rfl

theorem ψ₀_tChart : ψ₀ N (tChart ℚ (jFull N)) = tChart (AlgebraicClosure ℚ) (jBar N) :=
  Subtype.ext (φF_jFull N)

theorem ψInf_tInvChart : ψInf N (tInvChart ℚ (jFull N)) = tInvChart (AlgebraicClosure ℚ) (jBar N) :=
  Subtype.ext (by rw [coe_ψInf_apply, coe_tInvChart, coe_tInvChart, φF_jFull_inv])

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem ψ₀_eFin₀_one_tmul
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))))
    (hFin : ∀ b : chartAlgFin N ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eFin₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ℚ]
      ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (hFin₀ : ∀ b : chartAlgFin N ℓ,
      ((eFin₀ (1 ⊗ₜ b) : ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))
    (b : chartAlgFin N ℓ) : ψ₀ N (eFin₀ (1 ⊗ₜ b)) = eFin (1 ⊗ₜ b) :=
  Subtype.ext (by rw [coe_ψ₀_apply, hFin₀, φF_apply, hFin])

theorem ψInf_eInf₀_one_tmul
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hInf : ∀ b : chartAlgInf N ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eInf₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ℚ]
      ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (hInf₀ : ∀ b : chartAlgInf N ℓ,
      ((eInf₀ (1 ⊗ₜ b) : ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))
    (b : chartAlgInf N ℓ) : ψInf N (eInf₀ (1 ⊗ₜ b)) = eInf (1 ⊗ₜ b) :=
  Subtype.ext (by rw [coe_ψInf_apply, hInf₀, φF_apply, hInf])

end ModularCurve.IgusaScheme.P3psi
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme.P3psi"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve"

namespace P3asm

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel ModularCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme"
open scoped TensorProduct

local notation "Qb" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_chartRingHom
    (eFin : Qb ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[Qb]
      ↥(chartRing Qb ({jBar N} : Set (modularFunctionFieldBar N))))
    (hFin : ∀ b : chartAlgFin N ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(chartRing Qb ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb Qb ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange Qb (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eInf : Qb ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[Qb]
      ↥(chartRing Qb ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hInf : ∀ b : chartAlgInf N ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(chartRing Qb ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb Qb ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange Qb (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eFin₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ℚ]
      ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (hFin₀ : ∀ b : chartAlgFin N ℓ, ((eFin₀ (1 ⊗ₜ b) :
        ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) : ↥(modularFunctionFieldFull N))
          = (b : ↥(modularFunctionFieldFull N)))
    (eInf₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ℚ]
      ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (hInf₀ : ∀ b : chartAlgInf N ℓ, ((eInf₀ (1 ⊗ₜ b) :
        ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) : ↥(modularFunctionFieldFull N))
          = (b : ↥(modularFunctionFieldFull N))) :
    let φF : ↥(modularFunctionFieldFull N) →+* modularFunctionFieldBar N :=
      (baseChangeEquiv Qb (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := Qb) (B := ↥(modularFunctionFieldFull N))).toRingHom
    ∃ (ψ₀ : ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) →+*
          ↥(chartRing Qb ({jBar N} : Set (modularFunctionFieldBar N))))
      (ψinf : ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) →+*
          ↥(chartRing Qb ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))),
      (∀ a : ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))),
        φF (a : ↥(modularFunctionFieldFull N)) = (ψ₀ a : modularFunctionFieldBar N)) ∧
      (∀ a : ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))),
        φF (a : ↥(modularFunctionFieldFull N)) = (ψinf a : modularFunctionFieldBar N)) ∧
      ψ₀.comp (eFin₀.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgFin N ℓ))).toRingHom) =
        eFin.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := Qb) (B := ↥(chartAlgFin N ℓ))).toRingHom ∧
      ψinf.comp (eInf₀.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgInf N ℓ))).toRingHom) =
        eInf.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := Qb) (B := ↥(chartAlgInf N ℓ))).toRingHom ∧
      ψinf (tInvChart ℚ (jFull N)) = tInvChart Qb (jBar N : modularFunctionFieldBar N) := by
  intro φF
  refine ⟨ModularCurve.IgusaScheme.P3psi.ψ₀ N, ModularCurve.IgusaScheme.P3psi.ψInf N,
    fun a => rfl, fun a => rfl, ?_, ?_, ModularCurve.IgusaScheme.P3psi.ψInf_tInvChart N⟩
  · exact P3prime.comp_eq_of_forall_apply_one_tmul eFin₀ eFin _
      (ModularCurve.IgusaScheme.P3psi.ψ₀_eFin₀_one_tmul N ℓ eFin hFin eFin₀ hFin₀)
  · exact P3prime.comp_eq_of_forall_apply_one_tmul eInf₀ eInf _
      (ModularCurve.IgusaScheme.P3psi.ψInf_eInf₀_one_tmul N ℓ eInf hInf eInf₀ hInf₀)

end P3asm
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme.P3psi"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N))
    [hne : Fact (jBar N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N))))
    (hFin : ∀ b : chartAlgFin N ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hInf : ∀ b : chartAlgInf N ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))

    (htrans₀ : Transcendental ℚ (jFull N))
    [hne₀ : Fact (jFull N ≠ 0)]
    [hfd₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    [hfd_inv₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    (eFin₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (hFin₀ : ∀ b : chartAlgFin N ℓ,
      ((eFin₀ (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))
    (eInf₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (hInf₀ : ∀ b : chartAlgInf N ℓ,
      ((eInf₀ (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))

    (eη : (CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans).C ⟶
      pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd (igusaTo N ℓ) _ = (CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans).toBase)
    (hpinFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N ℓ)
    (hpinInf : AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
    (e₀ : (CurveModel.ofGenerator ℚ (jFull N) htrans₀).C ⟶
      pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd (igusaTo N ℓ) _ = (CurveModel.ofGenerator ℚ (jFull N) htrans₀).toBase)
    (hpinFin₀ : AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eFin₀.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
        ModularCurve.IgusaScheme.ιFin N ℓ)
    (hpinInf₀ : AlgebraicCurve.CurveModel.ιInf ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eInf₀.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
        ModularCurve.IgusaScheme.ιInf N ℓ) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans
    let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) :=
      CurveModel.ofGenerator ℚ (jFull N) htrans₀
    ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst (igusaTo N ℓ) _ = x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring) := by
  intro Mη M₀ x y x₀ hA hB
  obtain ⟨ψ₀, ψinf, hφψ₀, hφψinf, hcomm₀, hcomminf, hψt⟩ :=
    P3asm.exists_chartRingHom N ℓ eFin hFin eInf hInf eFin₀ hFin₀ eInf₀ hInf₀

  rw [CurveModel.pointEquivPlace_apply]

  have hxb1 : ((pointEquivClosedPoint Mη.toBase x : closedPoints Mη.C) : Mη.C) =
      x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) := rfl
  by_cases hfin : x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈
      Set.range (CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N)).base
  ·

    obtain ⟨φ, P, hφ, hPdef, hxP, hPker⟩ :=
      P3core.exists_ringHom_point_of_mem_range (CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N)) x.1 hfin

    obtain ⟨hx₀P₀, hP₀⟩ := P3.base_comp_inv_closedPoint_eq_of_pins (igusaTo N ℓ) _ _ eη e₀
      (CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N)) (CurveModel.ι₀ ℚ (jFull N)) (ModularCurve.IgusaScheme.ιFin N ℓ)
      _ _ ψ₀ hcomm₀ hpinFin hpinFin₀ x.1 φ hφ y hA
    rw [hB] at hx₀P₀
    set P₀ : CurveModel.X₀ ℚ (jFull N) :=
      (Spec.map (CommRingCat.ofHom (φ.comp ψ₀))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) with hP₀def
    have hPP₀ : P₀.asIdeal = P.asIdeal.comap ψ₀ := by rw [hPker]; exact hP₀

    have hxbP : ((pointEquivClosedPoint Mη.toBase x : closedPoints Mη.C) : Mη.C) =
        (CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N)).base P := hxb1.trans hxP
    have hxbmem : (CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N)).base P ∈ closedPoints Mη.C :=
      hxbP ▸ (pointEquivClosedPoint Mη.toBase x).2
    have hx₀mem : (CurveModel.ι₀ ℚ (jFull N)).base P₀ ∈ closedPoints M₀.C := hx₀P₀ ▸ x₀.2
    have hxbeq : pointEquivClosedPoint Mη.toBase x = ⟨(CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N)).base P, hxbmem⟩ :=
      Subtype.ext hxbP
    have hx₀eq : x₀ = ⟨(CurveModel.ι₀ ℚ (jFull N)).base P₀, hx₀mem⟩ := Subtype.ext hx₀P₀
    rw [hxbeq, hx₀eq]
    exact CurveModel.placeOfPoint_ofGenerator_iota0_comap ℚ (jFull N) (AlgebraicClosure ℚ) (jBar N) htrans₀ htrans
      _ ψ₀ hφψ₀ P hxbmem P₀ hx₀mem hPP₀
  ·
    have hinf : x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈
        Set.range (CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N)).base :=
      (CurveModel.mem_range_ι₀_or_mem_range_ιInf (AlgebraicClosure ℚ) (jBar N) _).resolve_left hfin
    obtain ⟨φ, P, hφ, hPdef, hxP, hPker⟩ :=
      P3core.exists_ringHom_point_of_mem_range (CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N)) x.1 hinf
    obtain ⟨hx₀P₀, hP₀⟩ := P3.base_comp_inv_closedPoint_eq_of_pins (igusaTo N ℓ) _ _ eη e₀
      (CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N)) (CurveModel.ιInf ℚ (jFull N)) (ModularCurve.IgusaScheme.ιInf N ℓ)
      _ _ ψinf hcomminf hpinInf hpinInf₀ x.1 φ hφ y hA
    rw [hB] at hx₀P₀
    set P₀ : CurveModel.XInf ℚ (jFull N) :=
      (Spec.map (CommRingCat.ofHom (φ.comp ψinf))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) with hP₀def
    have hPP₀ : P₀.asIdeal = P.asIdeal.comap ψinf := by rw [hPker]; exact hP₀
    have hxbP : ((pointEquivClosedPoint Mη.toBase x : closedPoints Mη.C) : Mη.C) =
        (CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N)).base P := hxb1.trans hxP

    have hfin' : ((pointEquivClosedPoint Mη.toBase x : closedPoints Mη.C) : Mη.C) ∉
        Set.range (CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N)).base := hxb1 ▸ hfin
    have hfin₀ : (x₀ : M₀.C) ∉ Set.range (CurveModel.ι₀ ℚ (jFull N)).base :=
      QFormP3.not_mem_range_ι₀_of_asIdeal_eq_comap ℚ (jFull N) (AlgebraicClosure ℚ) (jBar N) ψinf hψt
        hfin' P hxbP.symm P₀ hx₀P₀.symm hPP₀
    exact CurveModel.placeOfPoint_ofGenerator_iotaInf_comap ℚ (jFull N) (AlgebraicClosure ℚ) (jBar N) htrans₀ htrans
      _ ψinf hφψinf (pointEquivClosedPoint Mη.toBase x) hfin' P hxbP.symm x₀ hfin₀ P₀ hx₀P₀.symm hPP₀

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins.ModularCurve.IgusaScheme.P3psi"

end S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_ratPlaceCompat_of_chartPins (solution)
