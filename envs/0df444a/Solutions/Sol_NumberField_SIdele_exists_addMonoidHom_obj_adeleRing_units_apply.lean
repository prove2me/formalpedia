-- Prove2me | solution 1 for NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9429ba4b-7501-53aa-8a57-7f4bb8bba27e

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits_transportUnits_apply
import Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply
import Theorems.Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Theorems.Thm_NumberField_PlaceTransport_transport_trans_transport
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_trans_transport
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply

set_option autoImplicit false

namespace SIdeleRealisation

set_option synthInstance.maxHeartbeats 800000

open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport NumberField.PlaceDecomp NumberField.InfPlaceDecomp

section bricks

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def evalAt (w : HeightOneSpectrum R) : FiniteAdeleRing R K →* w.adicCompletion K where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem evalAt_apply (w : HeightOneSpectrum R) (x : FiniteAdeleRing R K) : evalAt w x = x w := rfl

noncomputable abbrev finUnitAt (w : HeightOneSpectrum R) (u : (FiniteAdeleRing R K)ˣ) : (w.adicCompletion K)ˣ :=
  Units.map (evalAt w) u

theorem coe_finUnitAt (w : HeightOneSpectrum R) (u : (FiniteAdeleRing R K)ˣ) :
    (finUnitAt w u : w.adicCompletion K) = (u : FiniteAdeleRing R K) w := rfl

theorem coe_inv_finUnitAt (w : HeightOneSpectrum R) (u : (FiniteAdeleRing R K)ˣ) :
    (((finUnitAt w u)⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) = ((u⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w := rfl

noncomputable def finIdeleOfUnits (u : Π w : HeightOneSpectrum R, (w.adicCompletion K)ˣ)
    (h₁ : ∀ᶠ w in Filter.cofinite, (u w : w.adicCompletion K) ∈ w.adicCompletionIntegers K)
    (h₂ : ∀ᶠ w in Filter.cofinite, (((u w)⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) ∈ w.adicCompletionIntegers K) :
    (FiniteAdeleRing R K)ˣ where
  val := ⟨fun w => (u w : w.adicCompletion K), h₁⟩
  inv := ⟨fun w => (((u w)⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K), h₂⟩
  val_inv := by
    apply RestrictedProduct.ext; intro w
    show (u w : w.adicCompletion K) * (((u w)⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1
    exact (u w).mul_inv
  inv_val := by
    apply RestrictedProduct.ext; intro w
    show (((u w)⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) * (u w : w.adicCompletion K) = 1
    exact (u w).inv_mul

theorem finUnitAt_finIdeleOfUnits (u : Π w : HeightOneSpectrum R, (w.adicCompletion K)ˣ) (h₁ h₂) (w : HeightOneSpectrum R) :
    finUnitAt w (finIdeleOfUnits u h₁ h₂) = u w := Units.ext rfl

theorem finUnitAt_mul (w : HeightOneSpectrum R) (u u' : (FiniteAdeleRing R K)ˣ) :
    finUnitAt w (u * u') = finUnitAt w u * finUnitAt w u' := map_mul _ u u'

theorem finIdele_ext {u u' : (FiniteAdeleRing R K)ˣ} (h : ∀ w, finUnitAt w u = finUnitAt w u') : u = u' :=
  Units.ext (RestrictedProduct.ext _ _ fun w => congrArg (fun z : (w.adicCompletion K)ˣ => (z : w.adicCompletion K)) (h w))

end bricks

section numberfield

variable {K : Type*} [Field K] [NumberField K]

noncomputable abbrev finPartOf (u : (AdeleRing (𝓞 K) K)ˣ) : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ((MulEquiv.prodUnits (M := InfiniteAdeleRing K) (N := FiniteAdeleRing (𝓞 K) K)) u).2

noncomputable abbrev infPartOf (u : (AdeleRing (𝓞 K) K)ˣ) : Π w : InfinitePlace K, (w.Completion)ˣ :=
  MulEquiv.piUnits ((MulEquiv.prodUnits (M := InfiniteAdeleRing K) (N := FiniteAdeleRing (𝓞 K) K)) u).1

noncomputable def ideleOf (a : Π w : InfinitePlace K, (w.Completion)ˣ) (f : (FiniteAdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing K) (N := FiniteAdeleRing (𝓞 K) K)).symm (MulEquiv.piUnits.symm a, f)

theorem ideleOf_snd_apply (a : Π w : InfinitePlace K, (w.Completion)ˣ) (f : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (ideleOf a f : AdeleRing (𝓞 K) K).2 w = (f : FiniteAdeleRing (𝓞 K) K) w := rfl

theorem ideleOf_fst_apply (a : Π w : InfinitePlace K, (w.Completion)ˣ) (f : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    (ideleOf a f : AdeleRing (𝓞 K) K).1 w = a w := rfl

theorem finPartOf_ideleOf (a : Π w : InfinitePlace K, (w.Completion)ˣ) (f : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    finPartOf (ideleOf a f) = f := by
  unfold ideleOf finPartOf; rw [MulEquiv.apply_symm_apply]

theorem infPartOf_ideleOf (a : Π w : InfinitePlace K, (w.Completion)ˣ) (f : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    infPartOf (ideleOf a f) = a := by
  unfold ideleOf infPartOf; rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem ideleOf_parts (u : (AdeleRing (𝓞 K) K)ˣ) : ideleOf (infPartOf u) (finPartOf u) = u := by
  unfold ideleOf infPartOf finPartOf
  rw [MulEquiv.symm_apply_apply, Prod.mk.eta, MulEquiv.symm_apply_apply]

theorem ideleOf_mul (a a' : Π w : InfinitePlace K, (w.Completion)ˣ) (f f' : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ideleOf (a * a') (f * f') = ideleOf a f * ideleOf a' f' := Units.ext rfl

end numberfield

section main

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

abbrev FIdx (v : HeightOneSpectrum (𝓞 E)) : Type := {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v}

abbrev AIdx (v : InfinitePlace E) : Type := {w : InfinitePlace K // w.comap (algebraMap E K) = v}

abbrev CU (v : HeightOneSpectrum (𝓞 E)) : Type :=
  Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localUnits E K v)
abbrev CI (v : HeightOneSpectrum (𝓞 E)) : Type :=
  Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v)
abbrev CA (v : InfinitePlace E) : Type :=
  Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
    (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))

noncomputable def eU (v : HeightOneSpectrum (𝓞 E)) : CU E K v ≃+ Additive (Π w : FIdx E K v, (w.1.adicCompletion K)ˣ) :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits_transportUnits_apply E K v).choose

theorem eU_spec (v : HeightOneSpectrum (𝓞 E)) (f : CU E K v) (y : K ≃ₐ[E] K) (w : FIdx E K v)
    (hy : y • w.1 = NumberField.PlaceAbove.above E K v) :
    NumberField.PlaceTransport.transportUnits y hy (Additive.toMul (eU E K v f) w) = Additive.toMul (f.1 y) :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits_transportUnits_apply E K v).choose_spec f y w hy

noncomputable def eI (v : HeightOneSpectrum (𝓞 E)) : CI E K v ≃+ Additive (Π w : FIdx E K v, (w.1.adicCompletionIntegers K)ˣ) :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply E K v).choose

theorem eI_spec (v : HeightOneSpectrum (𝓞 E)) (f : CI E K v) (y : K ≃ₐ[E] K) (w : FIdx E K v)
    (hy : y • w.1 = NumberField.PlaceAbove.above E K v) :
    NumberField.PlaceTransport.transportIntegerUnits y hy (Additive.toMul (eI E K v f) w) = Additive.toMul (f.1 y) :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply E K v).choose_spec f y w hy

noncomputable def eA (v : InfinitePlace E) : CA E K v ≃+ Additive (Π w : AIdx E K v, (w.1.Completion)ˣ) :=
  (NumberField.ArchIdele.exists_addEquiv_coind_localUnits_transportUnits_apply E K v).choose

theorem eA_spec (v : InfinitePlace E) (f : CA E K v) (y : K ≃ₐ[E] K) (w : AIdx E K v)
    (hy : y • w.1 = NumberField.ArchIdele.above E K v) :
    NumberField.InfinitePlaceTransport.transportUnits y hy (Additive.toMul (eA E K v f) w) = Additive.toMul (f.1 y) :=
  (NumberField.ArchIdele.exists_addEquiv_coind_localUnits_transportUnits_apply E K v).choose_spec f y w hy

variable {E K S}

abbrev xU (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) : CU E K v.1 := x (Sum.inl (Sum.inl v))
abbrev xI (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) : CI E K v.1 := x (Sum.inl (Sum.inr v))
abbrev xA (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) : CA E K v := x (Sum.inr v)

noncomputable def cU (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) (hv : w.under (𝓞 E) ∈ S) :
    (w.adicCompletion K)ˣ :=
  Additive.toMul (eU E K (w.under (𝓞 E)) (xU x ⟨w.under (𝓞 E), hv⟩)) ⟨w, rfl⟩

noncomputable def cI (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) (hv : w.under (𝓞 E) ∉ S) :
    (w.adicCompletionIntegers K)ˣ :=
  Additive.toMul (eI E K (w.under (𝓞 E)) (xI x ⟨w.under (𝓞 E), hv⟩)) ⟨w, rfl⟩

open Classical in
set_option synthInstance.maxHeartbeats 800000 in

noncomputable def cF (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) : (w.adicCompletion K)ˣ :=
  if hv : w.under (𝓞 E) ∈ S then cU x w hv
  else Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom (cI x w hv)

noncomputable def cA (x : NumberField.SIdele.obj E K S) (w : InfinitePlace K) : (w.Completion)ˣ :=
  Additive.toMul (eA E K (w.comap (algebraMap E K)) (xA x (w.comap (algebraMap E K)))) ⟨w, rfl⟩

theorem cU_add (x x' : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) (hv : w.under (𝓞 E) ∈ S) :
    cU (x + x') w hv = cU x w hv * cU x' w hv := by
  change Additive.toMul (eU E K (w.under (𝓞 E)) (xU x ⟨w.under (𝓞 E), hv⟩ + xU x' ⟨w.under (𝓞 E), hv⟩)) ⟨w, rfl⟩ = _
  rw [map_add, toMul_add, Pi.mul_apply]
  rfl

theorem cI_add (x x' : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) (hv : w.under (𝓞 E) ∉ S) :
    cI (x + x') w hv = cI x w hv * cI x' w hv := by
  change Additive.toMul (eI E K (w.under (𝓞 E)) (xI x ⟨w.under (𝓞 E), hv⟩ + xI x' ⟨w.under (𝓞 E), hv⟩)) ⟨w, rfl⟩ = _
  rw [map_add, toMul_add, Pi.mul_apply]
  rfl

set_option synthInstance.maxHeartbeats 800000 in
theorem cF_add (x x' : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) : cF (x + x') w = cF x w * cF x' w := by
  unfold cF
  split_ifs with hv
  · exact cU_add x x' w hv
  · rw [cI_add, map_mul]

theorem cA_add (x x' : NumberField.SIdele.obj E K S) (w : InfinitePlace K) : cA (x + x') w = cA x w * cA x' w := by
  change Additive.toMul (eA E K (w.comap (algebraMap E K)) (xA x (w.comap (algebraMap E K)) + xA x' (w.comap (algebraMap E K)))) ⟨w, rfl⟩ = _
  rw [map_add, toMul_add, Pi.mul_apply]
  rfl

set_option synthInstance.maxHeartbeats 800000 in
theorem coe_cF_of_not_mem (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) (hv : w.under (𝓞 E) ∉ S) :
    (cF x w : w.adicCompletion K) = ((cI x w hv : w.adicCompletionIntegers K) : w.adicCompletion K) := by
  simp only [cF, dif_neg hv]; rfl

set_option synthInstance.maxHeartbeats 800000 in
theorem coe_inv_cF_of_not_mem (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) (hv : w.under (𝓞 E) ∉ S) :
    (((cF x w)⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
      ((((cI x w hv)⁻¹ : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) : w.adicCompletion K) := by
  simp only [cF, dif_neg hv, ← map_inv]; rfl

variable (E K S) in
theorem finite_setOf_under_mem : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) ∈ S}.Finite := by
  have h : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) ∈ S} =
      ⋃ v ∈ (S : Set (HeightOneSpectrum (𝓞 E))), {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v} := by
    ext w; simp
  rw [h]
  refine S.finite_toSet.biUnion fun v _ => ?_
  have ho := NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K (NumberField.PlaceAbove.above E K v)
  rw [NumberField.SUnits.under_above] at ho
  rw [← ho]
  exact Set.finite_range _

theorem eventually_not_mem : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w.under (𝓞 E) ∉ S :=
  (finite_setOf_under_mem E K S).compl_mem_cofinite

set_option synthInstance.maxHeartbeats 800000 in

noncomputable def finPart (x : NumberField.SIdele.obj E K S) : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  finIdeleOfUnits (cF x)
    (eventually_not_mem.mono fun w hw => by rw [coe_cF_of_not_mem x w hw]; exact SetLike.coe_mem _)
    (eventually_not_mem.mono fun w hw => by rw [coe_inv_cF_of_not_mem x w hw]; exact SetLike.coe_mem _)

@[scoped simp] theorem finUnitAt_finPart (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) :
    finUnitAt w (finPart x) = cF x w := finUnitAt_finIdeleOfUnits _ _ _ w

noncomputable def Φu (x : NumberField.SIdele.obj E K S) : (AdeleRing (𝓞 K) K)ˣ := ideleOf (cA x) (finPart x)

theorem Φu_add (x x' : NumberField.SIdele.obj E K S) : Φu (x + x') = Φu x * Φu x' := by
  unfold Φu
  rw [← ideleOf_mul]
  congr 1
  · exact funext (cA_add x x')
  · exact finIdele_ext fun w => by rw [finUnitAt_mul, finUnitAt_finPart, finUnitAt_finPart, finUnitAt_finPart, cF_add]

variable (E K S) in

noncomputable def Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ :=
  AddMonoidHom.mk' (fun x => Additive.ofMul (Φu x)) fun x x' => by
    show Additive.ofMul (Φu (x + x')) = Additive.ofMul (Φu x) + Additive.ofMul (Φu x')
    rw [Φu_add]; rfl

theorem Φ_apply (x : NumberField.SIdele.obj E K S) : Additive.toMul (Φ E K S x) = Φu x := rfl

theorem Φu_snd_apply (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) :
    (Φu x : AdeleRing (𝓞 K) K).2 w = cF x w := rfl

theorem Φu_fst_apply (x : NumberField.SIdele.obj E K S) (w : InfinitePlace K) :
    (Φu x : AdeleRing (𝓞 K) K).1 w = cA x w := rfl

theorem finUnitAt_finPartOf_Φu (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) :
    finUnitAt w (finPartOf (Φu x)) = cF x w := by
  unfold Φu; rw [finPartOf_ideleOf, finUnitAt_finPart]

theorem infPartOf_Φu (x : NumberField.SIdele.obj E K S) : infPartOf (Φu x) = cA x := by
  unfold Φu; rw [infPartOf_ideleOf]

theorem exists_smul_eq_above {w : HeightOneSpectrum (𝓞 K)} {v : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 E) = v) :
    ∃ y : K ≃ₐ[E] K, y • w = NumberField.PlaceAbove.above E K v := by
  have ho := NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K (NumberField.PlaceAbove.above E K v)
  have hmem : w ∈ MulAction.orbit (K ≃ₐ[E] K) (NumberField.PlaceAbove.above E K v) := by
    rw [ho, Set.mem_setOf_eq, hw, NumberField.SUnits.under_above]
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y⁻¹, NumberField.PlaceTransport.inv_smul_eq_of_smul_eq hy⟩

theorem exists_smul_eq_above_inf {w : InfinitePlace K} {v : InfinitePlace E} (hw : w.comap (algebraMap E K) = v) :
    ∃ y : K ≃ₐ[E] K, y • w = NumberField.ArchIdele.above E K v :=
  InfinitePlace.exists_smul_eq_of_comap_eq (hw.trans (NumberField.ArchIdele.comap_above E K v).symm)

theorem cU_spec (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) {v : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 E) = v) (hv : v ∈ S) (y : K ≃ₐ[E] K) (hy : y • w = NumberField.PlaceAbove.above E K v) :
    NumberField.PlaceTransport.transportUnits y hy (cU x w (hw ▸ hv)) = Additive.toMul ((xU x ⟨v, hv⟩).1 y) := by
  subst hw
  exact eU_spec E K _ (xU x ⟨_, hv⟩) y ⟨w, rfl⟩ hy

theorem cI_spec (x : NumberField.SIdele.obj E K S) (w : HeightOneSpectrum (𝓞 K)) {v : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 E) = v) (hv : v ∉ S) (y : K ≃ₐ[E] K) (hy : y • w = NumberField.PlaceAbove.above E K v) :
    NumberField.PlaceTransport.transportIntegerUnits y hy (cI x w (hw ▸ hv)) = Additive.toMul ((xI x ⟨v, hv⟩).1 y) := by
  subst hw
  exact eI_spec E K _ (xI x ⟨_, hv⟩) y ⟨w, rfl⟩ hy

theorem cA_spec (x : NumberField.SIdele.obj E K S) (w : InfinitePlace K) {v : InfinitePlace E}
    (hw : w.comap (algebraMap E K) = v) (y : K ≃ₐ[E] K) (hy : y • w = NumberField.ArchIdele.above E K v) :
    NumberField.InfinitePlaceTransport.transportUnits y hy (cA x w) = Additive.toMul ((xA x v).1 y) := by
  subst hw
  exact eA_spec E K _ (xA x _) y ⟨w, rfl⟩ hy

end main

end SIdeleRealisation
p2m_reactivate "P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.SIdeleRealisation"

namespace SIdeleRealisation

set_option synthInstance.maxHeartbeats 800000

open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport NumberField.PlaceDecomp NumberField.InfPlaceDecomp

section main2

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
variable {S : Finset (HeightOneSpectrum (𝓞 E))}

omit [NumberField E] [IsGalois E K] in
theorem coe_transportUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (u : (w.adicCompletion K)ˣ) :
    (NumberField.PlaceTransport.transportUnits σ h u : w'.adicCompletion K) = NumberField.PlaceTransport.transport σ h u := rfl

omit [NumberField E] [IsGalois E K] in
theorem transportUnits_transportUnits (σ τ : K ≃ₐ[E] K) {w w' w'' : HeightOneSpectrum (𝓞 K)}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') (u : (w.adicCompletion K)ˣ) :
    NumberField.PlaceTransport.transportUnits σ h₂ (NumberField.PlaceTransport.transportUnits τ h₁ u) =
      NumberField.PlaceTransport.transportUnits (σ * τ) h₃ u := by
  refine Units.ext ?_
  change NumberField.PlaceTransport.transport σ h₂ (NumberField.PlaceTransport.transport τ h₁ (u : w.adicCompletion K)) =
    NumberField.PlaceTransport.transport (σ * τ) h₃ (u : w.adicCompletion K)
  rw [← NumberField.PlaceTransport.transport_trans_transport E K σ τ h₁ h₂ h₃]
  rfl

omit [NumberField E] [IsGalois E K] in
theorem transportIntegerUnits_transportIntegerUnits (σ τ : K ≃ₐ[E] K) {w w' w'' : HeightOneSpectrum (𝓞 K)}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') (u : (w.adicCompletionIntegers K)ˣ) :
    NumberField.PlaceTransport.transportIntegerUnits σ h₂ (NumberField.PlaceTransport.transportIntegerUnits τ h₁ u) =
      NumberField.PlaceTransport.transportIntegerUnits (σ * τ) h₃ u := by
  refine Units.ext (Subtype.ext ?_)
  change NumberField.PlaceTransport.transport σ h₂ (NumberField.PlaceTransport.transport τ h₁ ((u : w.adicCompletionIntegers K) : w.adicCompletion K)) =
    NumberField.PlaceTransport.transport (σ * τ) h₃ ((u : w.adicCompletionIntegers K) : w.adicCompletion K)
  rw [← NumberField.PlaceTransport.transport_trans_transport E K σ τ h₁ h₂ h₃]
  rfl

omit [NumberField E] [NumberField K] [IsGalois E K] in
theorem transportUnitsInf_transportUnitsInf (σ τ : K ≃ₐ[E] K) {w w' w'' : InfinitePlace K}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') (u : (w.Completion)ˣ) :
    NumberField.InfinitePlaceTransport.transportUnits σ h₂ (NumberField.InfinitePlaceTransport.transportUnits τ h₁ u) =
      NumberField.InfinitePlaceTransport.transportUnits (σ * τ) h₃ u := by
  refine Units.ext ?_
  change NumberField.InfinitePlaceTransport.transport σ h₂ (NumberField.InfinitePlaceTransport.transport τ h₁ (u : w.Completion)) =
    NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ (u : w.Completion)
  rw [← NumberField.InfinitePlaceTransport.transport_trans_transport E K σ τ h₁ h₂ h₃]
  rfl

theorem cF_rho (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : HeightOneSpectrum (𝓞 K)) (h : g • w = w') :
    cF ((NumberField.SIdele.obj E K S).ρ g x) w' = NumberField.PlaceTransport.transportUnits g h (cF x w) := by
  have hww : w'.under (𝓞 E) = w.under (𝓞 E) := by rw [← h]; exact NumberField.PlaceTransport.under_smul E K g w
  obtain ⟨y, hy⟩ := exists_smul_eq_above (E := E) (K := K) (w := w') rfl
  have hyg : (y * g) • w = NumberField.PlaceAbove.above E K (w'.under (𝓞 E)) := by rw [mul_smul, h, hy]
  by_cases hv : w'.under (𝓞 E) ∈ S
  · have hv' : w.under (𝓞 E) ∈ S := hww ▸ hv
    apply (NumberField.PlaceTransport.transportUnits y hy).injective
    simp only [cF, dif_pos hv, dif_pos hv']
    rw [cU_spec ((NumberField.SIdele.obj E K S).ρ g x) w' rfl hv y hy, transportUnits_transportUnits y g h hy hyg,
      cU_spec x w hww.symm hv (y * g) hyg]
    rfl
  · have hv' : w.under (𝓞 E) ∉ S := hww ▸ hv
    simp only [cF, dif_neg hv, dif_neg hv']
    have key : cI ((NumberField.SIdele.obj E K S).ρ g x) w' hv = NumberField.PlaceTransport.transportIntegerUnits g h (cI x w hv') := by
      apply (NumberField.PlaceTransport.transportIntegerUnits y hy).injective
      rw [cI_spec ((NumberField.SIdele.obj E K S).ρ g x) w' rfl hv y hy, transportIntegerUnits_transportIntegerUnits y g h hy hyg,
        cI_spec x w hww.symm hv (y * g) hyg]
      rfl
    rw [key]
    ext
    rfl

theorem cA_rho (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : InfinitePlace K) (h : g • w = w') :
    cA ((NumberField.SIdele.obj E K S).ρ g x) w' = NumberField.InfinitePlaceTransport.transportUnits g h (cA x w) := by
  have hww : w'.comap (algebraMap E K) = w.comap (algebraMap E K) := by
    rw [← h, InfinitePlace.smul_eq_comap, ← InfinitePlace.comap_comp]
    congr 1
    exact RingHom.ext fun x => g.symm.commutes x
  obtain ⟨y, hy⟩ := exists_smul_eq_above_inf (E := E) (K := K) (w := w') rfl
  have hyg : (y * g) • w = NumberField.ArchIdele.above E K (w'.comap (algebraMap E K)) := by rw [mul_smul, h, hy]
  apply (NumberField.InfinitePlaceTransport.transportUnits y hy).injective
  rw [cA_spec ((NumberField.SIdele.obj E K S).ρ g x) w' rfl y hy, transportUnitsInf_transportUnitsInf y g h hy hyg,
    cA_spec x w hww.symm (y * g) hyg]
  rfl

theorem conj_c_fin (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : HeightOneSpectrum (𝓞 K)) (h : g • w = w') :
    ((Additive.toMul (Φ E K S ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' =
      NumberField.PlaceTransport.transport g h (((Additive.toMul (Φ E K S x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) := by
  rw [Φ_apply, Φ_apply, Φu_snd_apply, Φu_snd_apply, cF_rho g x w w' h]
  rfl

theorem conj_c_inf (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : InfinitePlace K) (h : g • w = w') :
    ((Additive.toMul (Φ E K S ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' =
      NumberField.InfinitePlaceTransport.transport g h (((Additive.toMul (Φ E K S x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) := by
  rw [Φ_apply, Φ_apply, Φu_fst_apply, Φu_fst_apply, cA_rho g x w w' h]
  rfl

theorem injective_Φ : Function.Injective (Φ E K S) := by
  intro x x' hxx
  have hu : Φu x = Φu x' := congrArg Additive.toMul hxx
  have hF : ∀ w, cF x w = cF x' w := fun w => by rw [← finUnitAt_finPartOf_Φu, ← finUnitAt_finPartOf_Φu, hu]
  have hA : cA x = cA x' := by rw [← infPartOf_Φu, ← infPartOf_Φu, hu]
  funext i
  rcases i with (⟨v, hv⟩ | ⟨v, hv⟩) | v
  · apply (eU E K v).injective
    apply Additive.toMul.injective
    funext ⟨w, hw⟩
    subst hw
    have h1 := hF w
    simp only [cF, dif_pos hv] at h1
    exact h1
  · apply (eI E K v).injective
    apply Additive.toMul.injective
    funext ⟨w, hw⟩
    subst hw
    have h1 := hF w
    simp only [cF, dif_neg hv] at h1
    exact Units.ext (Subtype.ext (congrArg (fun z : (w.adicCompletion K)ˣ => (z : w.adicCompletion K)) h1))
  · apply (eA E K v).injective
    apply Additive.toMul.injective
    funext ⟨w, hw⟩
    subst hw
    exact congrFun hA w

theorem Φu_mem (x : NumberField.SIdele.obj E K S) :
    Φu x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff]
  intro w hw
  change ((finPart x : FiniteAdeleRing (𝓞 K) K) w ∈ _) ∧ (((finPart x)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w ∈ _
  refine ⟨?_, ?_⟩
  · change (cF x w : w.adicCompletion K) ∈ w.adicCompletionIntegers K
    rw [coe_cF_of_not_mem x w hw]; exact SetLike.coe_mem _
  · change (((cF x w)⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) ∈ w.adicCompletionIntegers K
    rw [coe_inv_cF_of_not_mem x w hw]; exact SetLike.coe_mem _

noncomputable def unitOfMem {w : HeightOneSpectrum (𝓞 K)} (z : (w.adicCompletion K)ˣ)
    (h₁ : (z : w.adicCompletion K) ∈ w.adicCompletionIntegers K)
    (h₂ : ((z⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) ∈ w.adicCompletionIntegers K) : (w.adicCompletionIntegers K)ˣ :=
  ⟨⟨(z : w.adicCompletion K), h₁⟩, ⟨((z⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K), h₂⟩, Subtype.ext z.mul_inv, Subtype.ext z.inv_mul⟩

omit [NumberField E] [IsGalois E K] in
theorem coe_coe_unitOfMem {w : HeightOneSpectrum (𝓞 K)} (z : (w.adicCompletion K)ˣ) (h₁ h₂) :
    ((unitOfMem z h₁ h₂ : w.adicCompletionIntegers K) : w.adicCompletion K) = z := rfl

omit [NumberField E] [IsGalois E K] in
theorem mem_and_mem {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (w : HeightOneSpectrum (𝓞 K)) (hw : w.under (𝓞 E) ∉ S) :
    (finUnitAt w (finPartOf u) : w.adicCompletion K) ∈ w.adicCompletionIntegers K ∧
      (((finUnitAt w (finPartOf u))⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) ∈ w.adicCompletionIntegers K :=
  (NumberField.AdeleRing.mem_unitIdelesOutside_iff _ u).1 hu w hw

noncomputable def pre (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) : NumberField.SIdele.obj E K S :=
  fun i => match i with
  | Sum.inl (Sum.inl v) => (eU E K v.1).symm (Additive.ofMul fun w => finUnitAt w.1 (finPartOf u))
  | Sum.inl (Sum.inr v) => (eI E K v.1).symm (Additive.ofMul fun w =>
      unitOfMem (finUnitAt w.1 (finPartOf u)) (mem_and_mem hu w.1 (fun h => v.2 (w.2 ▸ h))).1
        (mem_and_mem hu w.1 (fun h => v.2 (w.2 ▸ h))).2)
  | Sum.inr v => (eA E K v).symm (Additive.ofMul fun w => infPartOf u w.1)

theorem Φu_pre (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) : Φu (pre u hu) = u := by
  conv_rhs => rw [← ideleOf_parts u]
  unfold Φu
  congr 1
  · funext w
    simp only [cA, xA, pre, AddEquiv.apply_symm_apply, toMul_ofMul]
  · apply finIdele_ext
    intro w
    rw [finUnitAt_finPart]
    by_cases hv : w.under (𝓞 E) ∈ S
    · simp only [cF, dif_pos hv, cU, xU, pre, AddEquiv.apply_symm_apply, toMul_ofMul]
    · simp only [cF, dif_neg hv, cI, xI, pre, AddEquiv.apply_symm_apply, toMul_ofMul]
      ext; rfl

theorem range_Φ : (Φ E K S).range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact Φu_mem x
  · intro hu
    exact ⟨pre (Additive.toMul u) hu, congrArg Additive.ofMul (Φu_pre (Additive.toMul u) hu)⟩

omit [NumberField E] [IsGalois E K] in
theorem transport_algebraMap (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (k : K) :
    NumberField.PlaceTransport.transport σ h (algebraMap K (w.adicCompletion K) k) = algebraMap K (w'.adicCompletion K) (σ k) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [NumberField.PlaceTransport.transport_coe, WithVal.congr_apply]
  rfl

omit [NumberField E] [NumberField K] [IsGalois E K] in
theorem transportInf_algebraMap (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (k : K) :
    NumberField.InfinitePlaceTransport.transport σ h (algebraMap K w.Completion k) = algebraMap K w'.Completion (σ k) := by
  change NumberField.InfinitePlaceTransport.transport σ h (((WithAbs.equiv w.1).symm k : WithAbs w.1) : w.Completion) =
    (((WithAbs.equiv w'.1).symm (σ k) : WithAbs w'.1) : w'.Completion)
  rw [NumberField.InfinitePlaceTransport.transport_coe, WithAbs.congr_apply]
  rfl

omit [NumberField E] [NumberField K] [IsGalois E K] in
theorem coe_smul_val (y : K ≃ₐ[E] K) (u : Kˣ) : ((y • u : Kˣ) : K) = y (u : K) := rfl

theorem conj_d (a : NumberField.SUnits.sUnitsRep E K S) :
    Φ E K S ((NumberField.SIdele.diag E K S).hom a) =
      Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S a)) := by
  apply congrArg Additive.ofMul
  apply Units.ext
  change (Φu ((NumberField.SIdele.diag E K S).hom a) : AdeleRing (𝓞 K) K) =
    algebraMap K (AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S a : K)
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun w => ?_)
  ·
    change (cA ((NumberField.SIdele.diag E K S).hom a) w : w.Completion) = (algebraMap K (AdeleRing (𝓞 K) K) _).1 w
    have hR : (algebraMap K (AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S a : K)).1 w =
        algebraMap K w.Completion (NumberField.SUnits.val E K S a : K) := rfl
    rw [hR]
    obtain ⟨y, hy⟩ := exists_smul_eq_above_inf (E := E) (K := K) (w := w) rfl
    apply (NumberField.InfinitePlaceTransport.transport y hy).injective
    rw [transportInf_algebraMap]
    exact (congrArg Units.val (cA_spec ((NumberField.SIdele.diag E K S).hom a) w rfl y hy)).trans rfl
  ·
    change (cF ((NumberField.SIdele.diag E K S).hom a) w : w.adicCompletion K) = (algebraMap K (AdeleRing (𝓞 K) K) _).2 w
    have hR : (algebraMap K (AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S a : K)).2 w =
        algebraMap K (w.adicCompletion K) (NumberField.SUnits.val E K S a : K) := rfl
    rw [hR]
    obtain ⟨y, hy⟩ := exists_smul_eq_above (E := E) (K := K) (w := w) rfl
    apply (NumberField.PlaceTransport.transport y hy).injective
    rw [transport_algebraMap]
    by_cases hv : w.under (𝓞 E) ∈ S
    · rw [show (cF ((NumberField.SIdele.diag E K S).hom a) w : w.adicCompletion K) =
          (cU ((NumberField.SIdele.diag E K S).hom a) w hv : w.adicCompletion K) by simp only [cF, dif_pos hv]]
      exact (congrArg Units.val (cU_spec ((NumberField.SIdele.diag E K S).hom a) w rfl hv y hy)).trans rfl
    · rw [coe_cF_of_not_mem _ w hv]
      exact (congrArg (fun z : ((NumberField.PlaceAbove.above E K (w.under (𝓞 E))).adicCompletionIntegers K)ˣ =>
          ((z : (NumberField.PlaceAbove.above E K (w.under (𝓞 E))).adicCompletionIntegers K) :
            (NumberField.PlaceAbove.above E K (w.under (𝓞 E))).adicCompletion K))
        (cI_spec ((NumberField.SIdele.diag E K S).hom a) w rfl hv y hy)).trans
        (NumberField.SUnits.diagOut_hom_apply_apply_coe E K S ⟨w.under (𝓞 E), hv⟩ a y)

end main2
p2m_reactivate "P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.SIdeleRealisation"

end SIdeleRealisation
p2m_reactivate "P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.SIdeleRealisation"

namespace SIdeleRealisation
section values

set_option synthInstance.maxHeartbeats 800000

open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport NumberField.PlaceDecomp NumberField.InfPlaceDecomp

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
variable {S : Finset (HeightOneSpectrum (𝓞 E))}

theorem under_eq_of_smul_eq_above {w : HeightOneSpectrum (𝓞 K)} {v : HeightOneSpectrum (𝓞 E)} {y : K ≃ₐ[E] K}
    (hy : y • w = NumberField.PlaceAbove.above E K v) : w.under (𝓞 E) = v := by
  rw [← NumberField.PlaceTransport.under_smul E K y w, hy, NumberField.SUnits.under_above]

theorem comap_eq_of_smul_eq_above_inf {w : InfinitePlace K} {v : InfinitePlace E} {y : K ≃ₐ[E] K}
    (hy : y • w = NumberField.ArchIdele.above E K v) : w.comap (algebraMap E K) = v := by
  have h : (y • w).comap (algebraMap E K) = w.comap (algebraMap E K) := by
    rw [InfinitePlace.smul_eq_comap, ← InfinitePlace.comap_comp]
    congr 1
    exact RingHom.ext fun x => y.symm.commutes x
  rw [← h, hy, NumberField.ArchIdele.comap_above]

theorem value_fin_mem (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
    (hy : y • w = NumberField.PlaceAbove.above E K v.1) :
    NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ E K S x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
      ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
        ((NumberField.PlaceAbove.above E K v.1).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K) := by
  have hw : w.under (𝓞 E) = v.1 := under_eq_of_smul_eq_above hy
  have hv : w.under (𝓞 E) ∈ S := hw ▸ v.2
  rw [Φ_apply, Φu_snd_apply]
  simp only [cF, dif_pos hv]
  rw [← coe_transportUnits, cU_spec x w hw v.2 y hy]
  obtain ⟨v, hvS⟩ := v
  rfl

theorem value_fin_not_mem (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
    (hy : y • w = NumberField.PlaceAbove.above E K v.1) :
    NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ E K S x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
      (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
        ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
          (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K) := by
  have hw : w.under (𝓞 E) = v.1 := under_eq_of_smul_eq_above hy
  have hv : w.under (𝓞 E) ∉ S := hw ▸ v.2
  rw [Φ_apply, Φu_snd_apply]
  simp only [cF, dif_neg hv]
  have h := cI_spec x w hw v.2 y hy
  have h2 := congrArg (fun u : ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ =>
    (((u : (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K)) h
  exact h2

theorem value_inf (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
    (hy : y • w = NumberField.ArchIdele.above E K v) :
    NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ E K S x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) =
      ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K v).Completion)ˣ) :
        (NumberField.ArchIdele.above E K v).Completion) := by
  have hw : w.comap (algebraMap E K) = v := comap_eq_of_smul_eq_above_inf hy
  rw [Φ_apply, Φu_fst_apply]
  have h := cA_spec x w hw y hy
  exact congrArg (fun u : ((NumberField.ArchIdele.above E K v).Completion)ˣ => (u : (NumberField.ArchIdele.above E K v).Completion)) h

end values
p2m_reactivate "P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.SIdeleRealisation"
end SIdeleRealisation
p2m_reactivate "P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.SIdeleRealisation"

open IsDedekindDomain NumberField in
open scoped NumberField.PlaceTransport in
theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K) :
    ∃ Φ : (NumberField.SIdele.obj E K S) →+ Additive (AdeleRing (𝓞 K) K)ˣ,
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
        Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x)))) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) ∧

      (∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
        (hy : y • w = NumberField.PlaceAbove.above E K v.1),
        NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
          ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
            ((NumberField.PlaceAbove.above E K v.1).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K)) ∧
      (∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
        (hy : y • w = NumberField.PlaceAbove.above E K v.1),
        NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
          (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
            ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
              (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K)) ∧
      (∀ (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
        (hy : y • w = NumberField.ArchIdele.above E K v),
        NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) =
          ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K v).Completion)ˣ) :
            (NumberField.ArchIdele.above E K v).Completion)) := by
  refine ⟨SIdeleRealisation.Φ E K S, SIdeleRealisation.injective_Φ, SIdeleRealisation.range_Φ, fun g x => ?_, SIdeleRealisation.conj_d,
    SIdeleRealisation.value_fin_mem, SIdeleRealisation.value_fin_not_mem, SIdeleRealisation.value_inf⟩

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 K) E K
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum E K := Subsingleton.elim _ _
  apply Additive.toMul.injective
  rw [toMul_ofMul]
  apply Units.ext
  change ((Additive.toMul (SIdeleRealisation.Φ E K S ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
    (M4aHerbrand.GenuineDescent.genuineDescentDatum E K).act g ((Additive.toMul (SIdeleRealisation.Φ E K S x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  refine Prod.ext (funext fun w' => ?_) (RestrictedProduct.ext _ _ fun w' => ?_)
  · rw [SIdeleRealisation.conj_c_inf g x (g⁻¹ • w') w' (smul_inv_smul g w')]
    exact (M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply E K g _ (smul_inv_smul g w')).symm
  · change ((Additive.toMul (SIdeleRealisation.Φ E K S ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' =
      ((M4aHerbrand.GenuineDescent.genuineDescentDatum E K).act g
        ((Additive.toMul (SIdeleRealisation.Φ E K S x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w'
    rw [SIdeleRealisation.conj_c_fin g x (g⁻¹ • w') w' (smul_inv_smul g w')]
    exact (M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E K g _ (smul_inv_smul g w')).symm

end S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply
end P2MW
export P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply (solution)
