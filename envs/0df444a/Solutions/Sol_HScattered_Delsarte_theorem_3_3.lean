-- Prove2me | solution 1 for HScattered.Delsarte.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T10:51:20.589087+00:00
-- url     : https://prove2.me/submissions/2f78bd24-56e9-4d4d-b820-0dbfe38af8cb

import Mathlib
import Definitions.Def_HScattered_Delsarte_IsHScattered
import Definitions.Def_HScattered_Delsarte_DelsarteSetting

-- Complete module: HSDProof/SharedBasics.lean

noncomputable section
open scoped Classical

namespace HScattered.Delsarte.HSDFresh
end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeProjection.lean

noncomputable section
open scoped Classical
open Submodule
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]

def nativeProj (D : DelsarteSetting F K V) : V →ₗ[K] D.Λ :=
  D.Λ.projectionOnto D.Γ D.isCompl_Λ_Γ

theorem nativeProj_ker (D : DelsarteSetting F K V) :
    LinearMap.ker (nativeProj D) = D.Γ :=
  Submodule.ker_projectionOnto D.isCompl_Λ_Γ

theorem nativeProj_surjective (D : DelsarteSetting F K V) :
    Function.Surjective (nativeProj D) :=
  Submodule.projectionOnto_surjective D.isCompl_Λ_Γ

theorem nativeProj_W_image (D : DelsarteSetting F K V) :
    D.W.map ((nativeProj D).restrictScalars F) = D.U := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ((nativeProj D w : D.Λ) : V) ∈ D.W ⊔ D.Γ.restrictScalars F
    have hq := Submodule.sub_projection_mem D.isCompl_Λ_Γ w
    have hw' : w ∈ D.W ⊔ D.Γ.restrictScalars F := Submodule.mem_sup_left hw
    have hq' : w - (nativeProj D w : V) ∈ D.W ⊔ D.Γ.restrictScalars F :=
      Submodule.mem_sup_right hq
    simpa using (D.W ⊔ D.Γ.restrictScalars F).sub_mem hw' hq'
  · intro hx
    obtain ⟨w, hw, q, hq, he⟩ := Submodule.mem_sup.mp hx
    refine ⟨w, hw, ?_⟩
    have hp : nativeProj D (x : V) = x :=
      Submodule.projectionOnto_apply_left D.isCompl_Λ_Γ x
    have hz : nativeProj D q = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff D.isCompl_Λ_Γ).mpr hq
    change w + q = (x : V) at he
    rw [← he, map_add, hz, add_zero] at hp
    exact hp

theorem nativeProj_W_injective (D : DelsarteSetting F K V) :
    Function.Injective (((nativeProj D).restrictScalars F).comp D.W.subtype) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro w hw
  have hq : (w : V) ∈ D.Γ :=
    (Submodule.projectionOnto_apply_eq_zero_iff D.isCompl_Λ_Γ).mp hw
  have hz : (w : V) ∈ (⊥ : Submodule F V) := by
    rw [← D.W_inf_Γ]
    exact ⟨w.property, hq⟩
  simpa using hz

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/SubgeometryBasis.lean

noncomputable section
open scoped Classical
open Submodule Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V]

def formBasis (D : DelsarteSetting F K V) := Module.finBasis F D.W

def formVector (D : DelsarteSetting F K V) (i : Fin (finrank F D.W)) : V :=
  formBasis D i

theorem formVector_span_F (D : DelsarteSetting F K V) :
    span F (Set.range (formVector D)) = D.W := by
  have hb := (formBasis D).span_eq
  have hm := congrArg (Submodule.map D.W.subtype) hb
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hm
  rw [← Set.range_comp] at hm
  exact hm

theorem formVector_span_K (D : DelsarteSetting F K V) :
    span K (Set.range (formVector D)) = ⊤ := by
  rw [← Submodule.span_span_of_tower F K, formVector_span_F, D.span_W]

def ambientBasis (D : DelsarteSetting F K V) : Basis (Fin (finrank F D.W)) K V :=
  basisOfTopLeSpanOfCardEqFinrank (formVector D)
    (formVector_span_K D).ge (by simpa using D.finrank_W)

@[simp] theorem ambientBasis_apply (D : DelsarteSetting F K V)
    (i : Fin (finrank F D.W)) : ambientBasis D i = formVector D i := by
  exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i

theorem formVector_mem (D : DelsarteSetting F K V) (i : Fin (finrank F D.W)) :
    formVector D i ∈ D.W := (formBasis D i).property

omit [FiniteDimensional F V] in
theorem native_U_finrank (D : DelsarteSetting F K V) :
    finrank F D.U = finrank K V := by
  have he := LinearMap.finrank_range_of_inj (nativeProj_W_injective D)
  rw [LinearMap.range_comp, Submodule.range_subtype, nativeProj_W_image] at he
  exact he.trans D.finrank_W

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/CoordinateInclusion.lean

namespace HScattered.Delsarte.HSDFresh

variable (F K : Type*) {I : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def fieldCoords : (I → F) →ₗ[F] (I → K) where
  toFun v i := algebraMap F K (v i)
  map_add' v w := by ext i; exact map_add (algebraMap F K) _ _
  map_smul' a v := by
    ext i
    change algebraMap F K (a * v i) = a • algebraMap F K (v i)
    rw [map_mul, Algebra.smul_def]

@[simp] theorem fieldCoords_apply (v : I → F) (i : I) :
    fieldCoords F K v i = algebraMap F K (v i) := rfl

theorem fieldCoords_injective : Function.Injective (fieldCoords F K (I := I)) := by
  intro v w h
  funext i
  exact (algebraMap F K).injective (congrFun h i)

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeCoordinates.lean

noncomputable section
open scoped Classical BigOperators
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V]

theorem ambient_synthesis_field (D : DelsarteSetting F K V)
    (a : Fin (finrank F D.W) → F) :
    (ambientBasis D).equivFun.symm (fieldCoords F K a) =
      ((formBasis D).equivFun.symm a : V) := by
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply]
  simp only [fieldCoords_apply, ambientBasis_apply, Submodule.coe_sum,
    Submodule.coe_smul, IsScalarTower.algebraMap_smul, formVector]

theorem ambient_coordinates_form (D : DelsarteSetting F K V) (w : D.W) :
    (ambientBasis D).equivFun (w : V) =
      fieldCoords F K ((formBasis D).equivFun w) := by
  apply (ambientBasis D).equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, ambient_synthesis_field,
    LinearEquiv.symm_apply_apply]

theorem ambient_synthesis_mem_W_iff (D : DelsarteSetting F K V)
    (a : Fin (finrank F D.W) → K) :
    (ambientBasis D).equivFun.symm a ∈ D.W ↔
      a ∈ LinearMap.range (fieldCoords F K) := by
  constructor
  · intro h
    let w : D.W := ⟨(ambientBasis D).equivFun.symm a, h⟩
    refine ⟨(formBasis D).equivFun w, ?_⟩
    rw [← ambient_coordinates_form]
    exact (ambientBasis D).equivFun.apply_symm_apply a
  · rintro ⟨b, rfl⟩
    rw [ambient_synthesis_field]
    exact Subtype.coe_prop _

def nativeGenerator (D : DelsarteSetting F K V) :
    (Fin (finrank F D.W) → K) →ₗ[K] D.Λ :=
  (nativeProj D).comp (ambientBasis D).equivFun.symm.toLinearMap

theorem nativeGenerator_surjective (D : DelsarteSetting F K V) :
    Function.Surjective (nativeGenerator D) :=
  (nativeProj_surjective D).comp (ambientBasis D).equivFun.symm.surjective

theorem nativeGenerator_ker (D : DelsarteSetting F K V) :
    LinearMap.ker (nativeGenerator D) =
      D.Γ.comap (ambientBasis D).equivFun.symm.toLinearMap := by
  rw [nativeGenerator, LinearMap.ker_comp, nativeProj_ker]

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/CompanionField.lean

noncomputable section
open scoped Classical
open Submodule
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]

theorem form_zero_of_on_W (D : DelsarteSetting F K V) (v : V)
    (hv : ∀ w ∈ D.W, D.β v w = 0) : v = 0 := by
  apply D.nondegenerate v
  have hs : Submodule.span K (D.W : Set V) ≤ LinearMap.ker (D.β v) :=
    Submodule.span_le.mpr hv
  rw [D.span_W] at hs
  intro w
  exact hs (Submodule.mem_top)

theorem exists_form_pair (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) :
    ∃ w ∈ D.W, ∃ z ∈ D.W, D.β w z ≠ 0 := by
  obtain ⟨w, hw, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  by_contra hh
  push Not at hh
  exact hn (form_zero_of_on_W D w (hh w hw))

theorem companion_mem_range (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) (a : F) :
    D.σ (algebraMap F K a) ∈ Set.range (algebraMap F K) := by
  obtain ⟨w, hw, z, hz, hn⟩ := exists_form_pair D hW
  obtain ⟨b, hb⟩ := D.mem_range_algebraMap w hw z hz
  obtain ⟨c, hc⟩ := D.mem_range_algebraMap w hw (a • z) (D.W.smul_mem a hz)
  have hb0 : b ≠ 0 := by
    intro h
    apply hn
    rw [← hb, h, map_zero]
  refine ⟨c / b, ?_⟩
  have he : algebraMap F K c = D.σ (algebraMap F K a) * algebraMap F K b := by
    rw [hc, hb]
    rw [← IsScalarTower.algebraMap_smul K a z, map_smulₛₗ]
    rfl
  rw [map_div₀, he]
  exact mul_div_cancel_right₀ _ (by simpa using (algebraMap F K).injective.ne hb0)

def companionFun (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) (a : F) : F :=
  Classical.choose (companion_mem_range D hW a)

theorem companionFun_spec (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) (a : F) :
    algebraMap F K (companionFun D hW a) = D.σ (algebraMap F K a) :=
  Classical.choose_spec (companion_mem_range D hW a)

def companionHom (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) : F →+* F where
  toFun := companionFun D hW
  map_one' := by
    apply (algebraMap F K).injective
    simp only [companionFun_spec, map_one]
  map_mul' a b := by
    apply (algebraMap F K).injective
    simp only [map_mul, companionFun_spec]
  map_zero' := by
    apply (algebraMap F K).injective
    simp only [companionFun_spec, map_zero]
  map_add' a b := by
    apply (algebraMap F K).injective
    simp only [map_add, companionFun_spec]

@[simp] theorem companionHom_spec (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) (a : F) :
    algebraMap F K (companionHom D hW a) = D.σ (algebraMap F K a) :=
  Classical.choose_spec (companion_mem_range D hW a)

def companionEquiv [Fintype F] (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) : F ≃+* F :=
  RingEquiv.ofBijective (companionHom D hW)
    ⟨(companionHom D hW).injective, Finite.surjective_of_injective (companionHom D hW).injective⟩

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/CoordinateRank.lean

open scoped BigOperators

namespace HScattered.Delsarte.HSDFresh

variable (F : Type*) {K I : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def coordRank (v : I → K) : ℕ :=
  Module.finrank F (Submodule.span F (Set.range v))

 theorem coord_mem_span (v : I → K) (i : I) :
    v i ∈ Submodule.span F (Set.range v) := Submodule.subset_span ⟨i, rfl⟩

variable [FiniteDimensional F K]

theorem coordRank_le_of_mem (T : Submodule F K) {v : I → K}
    (hv : ∀ i, v i ∈ T) : coordRank F v ≤ Module.finrank F T := by
  apply Submodule.finrank_mono
  exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)

theorem coordRank_eq_zero_iff (v : I → K) : coordRank F v = 0 ↔ v = 0 := by
  rw [coordRank, Submodule.finrank_eq_zero]
  constructor
  · intro h
    funext i
    have hi := coord_mem_span F v i
    rw [h] at hi
    exact hi
  · intro h
    subst v
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp)
    · exact bot_le

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/CoordinateLinear.lean

noncomputable section
open scoped Classical BigOperators
namespace HScattered.Delsarte.HSDFresh
variable {F K I J : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Fintype I] [DecidableEq I]

theorem coordRank_linear_le (L : (I → K) →ₗ[K] (J → K))
    (hL : ∀ i j, L (Pi.single j 1) i ∈ Set.range (algebraMap F K)) (v : I → K) :
    coordRank F (L v) ≤ coordRank F v := by
  apply coordRank_le_of_mem F (Submodule.span F (Set.range v))
  intro i
  have hv : v = ∑ j, v j • Pi.single j (1 : K) := by
    ext j
    simp [Pi.single_apply]
  have hLv : L v i = ∑ j, v j * L (Pi.single j 1) i := by
    conv_lhs => rw [hv, map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hLv]
  apply Submodule.sum_mem
  intro j _
  obtain ⟨a, ha⟩ := hL i j
  have hh := (Submodule.span F (Set.range v)).smul_mem a (coord_mem_span F v j)
  rw [← ha]
  simpa only [Algebra.smul_def, mul_comm] using hh

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/FieldLinearTransport.lean

noncomputable section
open scoped Classical BigOperators
namespace HScattered.Delsarte.HSDFresh
variable {F K I : Type*} [Field F] [Field K] [Algebra F K] [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem fieldCoords_single (j : I) :
    fieldCoords F K (Pi.single j 1) = Pi.single j 1 := by
  ext i
  simp [Pi.single_apply]

omit [Fintype I] [DecidableEq I] in
theorem fieldCoords_range_iff (v : I → K) :
    v ∈ Set.range (fieldCoords F K) ↔ ∀ i, v i ∈ Set.range (algebraMap F K) := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact ⟨a i, rfl⟩
  · intro h
    choose a ha using h
    exact ⟨a, funext ha⟩

theorem field_map_of_entries (L : (I → K) →ₗ[K] (I → K))
    (hL : ∀ i j, L (Pi.single j 1) i ∈ Set.range (algebraMap F K)) :
    Set.MapsTo L (Set.range (fieldCoords F K)) (Set.range (fieldCoords F K)) := by
  rintro _ ⟨a, rfl⟩
  apply (fieldCoords_range_iff _).mpr
  intro i
  have hv : fieldCoords F K a = ∑ j, (algebraMap F K (a j)) • Pi.single j (1 : K) := by
    ext j
    simp [Pi.single_apply, Algebra.smul_def]
  rw [hv, map_sum, Finset.sum_apply]
  change _ ∈ LinearMap.range (Algebra.linearMap F K)
  apply Submodule.sum_mem
  intro j _
  obtain ⟨b, hb⟩ := hL i j
  refine ⟨a j * b, ?_⟩
  change algebraMap F K (a j * b) = _
  rw [map_mul]
  simp only [LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
  exact congrArg (fun z => algebraMap F K (a j) * z) hb

theorem field_inverse_entries [Fintype F] (e : (I → K) ≃ₗ[K] (I → K))
    (h : Set.MapsTo e (Set.range (fieldCoords F K)) (Set.range (fieldCoords F K))) :
    ∀ i j, e.symm (Pi.single j 1) i ∈ Set.range (algebraMap F K) := by
  have hf : (Set.range (fieldCoords F K (I := I))).Finite := Set.finite_range _
  have hs := (hf.injOn_iff_bijOn_of_mapsTo h).mp e.injective.injOn
  intro i j
  have hj : Pi.single j (1 : K) ∈ Set.range (fieldCoords F K) :=
    ⟨Pi.single j 1, fieldCoords_single j⟩
  obtain ⟨v, hv, he⟩ := hs.surjOn hj
  have he' : e.symm (Pi.single j 1) = v := by rw [← he, e.symm_apply_apply]
  rw [he']
  exact (fieldCoords_range_iff v).mp hv i

theorem coordRank_field_equiv [Fintype F] [FiniteDimensional F K]
    (e : (I → K) ≃ₗ[K] (I → K))
    (h : ∀ i j, e (Pi.single j 1) i ∈ Set.range (algebraMap F K)) (v : I → K) :
    coordRank F (e v) = coordRank F v := by
  apply le_antisymm (coordRank_linear_le e.toLinearMap h v)
  have hi := field_inverse_entries e (field_map_of_entries e.toLinearMap h)
  simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    coordRank_linear_le e.symm.toLinearMap hi (e v)

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/GramCoordinates.lean

noncomputable section
open scoped Classical BigOperators
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V]

def gramMap (D : DelsarteSetting F K V) :
    (Fin (finrank F D.W) → K) →ₗ[K] (Fin (finrank F D.W) → K) :=
  LinearMap.pi fun i => ∑ j, (D.β (formVector D i) (formVector D j)) • LinearMap.proj j

@[simp] theorem gramMap_apply (D : DelsarteSetting F K V)
    (a : Fin (finrank F D.W) → K) (i : Fin (finrank F D.W)) :
    gramMap D a i = ∑ j, D.β (formVector D i) (formVector D j) * a j := by
  simp [gramMap]

theorem form_zero_of_basis_left (D : DelsarteSetting F K V) (v : V)
    (hv : ∀ i, D.β (formVector D i) v = 0) : v = 0 := by
  have hs : Submodule.span K (Set.range (formVector D)) ≤ LinearMap.ker (D.β.flip v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hv i
  rw [formVector_span_K] at hs
  apply D.nondegenerate v
  intro w
  exact D.reflexive w v (hs Submodule.mem_top)

theorem gramMap_formula (D : DelsarteSetting F K V) (x : V)
    (i : Fin (finrank F D.W)) :
    gramMap D (fun j => D.σ ((ambientBasis D).equivFun x j)) i =
      D.β (formVector D i) x := by
  rw [gramMap_apply]
  conv_rhs => rw [← (ambientBasis D).sum_equivFun x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smulₛₗ, ambientBasis_apply]
  exact mul_comm _ _

theorem gramMap_injective (D : DelsarteSetting F K V) :
    Function.Injective (gramMap D) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro a ha
  let x := (ambientBasis D).equivFun.symm (fun j => D.σ.symm (a j))
  have hcoord : (fun j => D.σ ((ambientBasis D).equivFun x j)) = a := by
    funext j
    change D.σ ((ambientBasis D).equivFun
      ((ambientBasis D).equivFun.symm (fun j => D.σ.symm (a j))) j) = a j
    rw [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hx : x = 0 := by
    apply form_zero_of_basis_left D
    intro i
    rw [← gramMap_formula, hcoord]
    exact congrFun ha i
  have he := congrArg (ambientBasis D).equivFun hx
  have he' : (fun j => D.σ.symm (a j)) = 0 := by
    change (ambientBasis D).equivFun
      ((ambientBasis D).equivFun.symm (fun j => D.σ.symm (a j))) = _ at he
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using he
  funext j
  have hj := congrFun he' j
  apply D.σ.symm.injective
  simpa using hj

theorem gramMap_entries (D : DelsarteSetting F K V)
    (i j : Fin (finrank F D.W)) :
    gramMap D (Pi.single j 1) i ∈ Set.range (algebraMap F K) := by
  simpa [Pi.single_apply] using
    D.mem_range_algebraMap (formVector D i) (formVector_mem D i)
      (formVector D j) (formVector_mem D j)

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/FiniteDimensions.lean

noncomputable section
namespace HScattered.Delsarte.HSDFresh
variable {K V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem finrank_eq_of_equiv (e : V ≃ W) :
    Module.finrank K V = Module.finrank K W := by
  apply Nat.pow_right_injective (a := Nat.card K)
    (by have h := Fintype.one_lt_card (α := K); rw [Nat.card_eq_fintype_card]; omega)
  change Nat.card K ^ Module.finrank K V = Nat.card K ^ Module.finrank K W
  rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank]
  exact Nat.card_congr e

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/CoordinateAutomorphism.lean

noncomputable section
open scoped Classical
namespace HScattered.Delsarte.HSDFresh
variable {F K I : Type*} [Field F] [Field K] [Algebra F K]

def compatibleFieldEquiv (σ : K ≃+* K) (τ : F ≃+* F)
    (h : ∀ a, σ (algebraMap F K a) = algebraMap F K (τ a)) :
    haveI := RingHomInvPair.of_ringEquiv τ
    haveI := RingHomInvPair.symm (τ : F →+* F) (τ.symm : F →+* F)
    K ≃ₛₗ[(τ : F →+* F)] K := by
  letI := RingHomInvPair.of_ringEquiv τ
  letI := RingHomInvPair.symm (τ : F →+* F) (τ.symm : F →+* F)
  exact {
    toFun := σ
    invFun := σ.symm
    left_inv := σ.left_inv
    right_inv := σ.right_inv
    map_add' := σ.map_add
    map_smul' a x := by
      change σ (a • x) = τ a • σ x
      simp only [Algebra.smul_def, map_mul, h] }

theorem coordRank_automorphism [Fintype F] [FiniteDimensional F K]
    (σ : K ≃+* K) (τ : F ≃+* F)
    (h : ∀ a, σ (algebraMap F K a) = algebraMap F K (τ a)) (v : I → K) :
    coordRank F (fun i => σ (v i)) = coordRank F v := by
  let := RingHomInvPair.of_ringEquiv τ
  let := RingHomInvPair.symm (τ : F →+* F) (τ.symm : F →+* F)
  let e := compatibleFieldEquiv σ τ h
  have he := finrank_eq_of_equiv (K := F)
    (e.submoduleMap (Submodule.span F (Set.range v))).toEquiv
  rw [Submodule.map_span] at he
  have hr : e '' Set.range v = Set.range (fun i => σ (v i)) := by
    exact (Set.range_comp e v).symm
  change Module.finrank F (Submodule.span F (Set.range v)) =
    Module.finrank F (Submodule.span F (e '' Set.range v)) at he
  rw [hr] at he
  exact he.symm

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeColumn.lean

noncomputable section
open scoped Classical BigOperators
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V]

def gramEquiv [Fintype K] (D : DelsarteSetting F K V) :
    (Fin (finrank F D.W) → K) ≃ₗ[K] (Fin (finrank F D.W) → K) :=
  LinearEquiv.ofBijective (gramMap D)
    ⟨gramMap_injective D, Finite.surjective_of_injective (gramMap_injective D)⟩

def nativeColumn (D : DelsarteSetting F K V) (v : V) : Fin (finrank F D.W) → K :=
  fun i => D.β (formVector D i) v

theorem nativeColumn_eq (D : DelsarteSetting F K V) (v : V) :
    nativeColumn D v = gramMap D (fun i => D.σ ((ambientBasis D).equivFun v i)) := by
  funext i
  exact (gramMap_formula D v i).symm

theorem nativeColumn_ne_zero (D : DelsarteSetting F K V) {v : V} (hv : v ≠ 0) :
    nativeColumn D v ≠ 0 := by
  intro h
  apply hv
  apply form_zero_of_basis_left D
  intro i
  exact congrFun h i

theorem nativeColumn_rank [Fintype F] [Fintype K] [FiniteDimensional F K]
    (D : DelsarteSetting F K V) (hW : D.W ≠ ⊥) (v : V) :
    coordRank F (nativeColumn D v) = coordRank F ((ambientBasis D).equivFun v) := by
  classical
  rw [nativeColumn_eq]
  have hentries : ∀ i j, gramEquiv D (Pi.single j 1) i ∈ Set.range (algebraMap F K) := by
    intro i j
    change gramMap D (Pi.single j 1) i ∈ Set.range (algebraMap F K)
    exact gramMap_entries D i j
  have hg := coordRank_field_equiv (F := F) (gramEquiv D)
    hentries
    (fun i => D.σ ((ambientBasis D).equivFun v i))
  change coordRank F (gramMap D _) = _ at hg
  rw [hg]
  apply coordRank_automorphism D.σ (companionEquiv D hW)
  intro a
  exact (companionHom_spec D hW a).symm

theorem nativeColumn_dot (D : DelsarteSetting F K V) (v x : V) :
    (∑ i, (ambientBasis D).equivFun v i * nativeColumn D x i) = D.β v x := by
  conv_rhs => rw [← (ambientBasis D).sum_equivFun v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, ambientBasis_apply, nativeColumn]

theorem nativeColumn_orth (D : DelsarteSetting F K V) (x : V)
    (hx : x ∈ D.orth D.Γ) (c : Fin (finrank F D.W) → K)
    (hc : c ∈ LinearMap.ker (nativeGenerator D)) :
    (∑ i, c i * nativeColumn D x i) = 0 := by
  have hc' : (ambientBasis D).equivFun.symm c ∈ D.Γ := by
    rw [nativeGenerator_ker] at hc
    exact hc
  have hz : D.β x ((ambientBasis D).equivFun.symm c) = 0 := by
    have hh := (iInf_le (fun s : D.Γ => LinearMap.ker (D.β.flip (s : V))) ⟨_, hc'⟩) hx
    exact hh
  have he := nativeColumn_dot D ((ambientBasis D).equivFun.symm c) x
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.trans (D.reflexive _ _ hz)

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeGenerator.lean

noncomputable section
open scoped Classical
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V]

theorem nativeGenerator_field (D : DelsarteSetting F K V) :
    ((nativeGenerator D).restrictScalars F).comp (fieldCoords F K) =
      (((nativeProj D).restrictScalars F).comp D.W.subtype).comp
        (formBasis D).equivFun.symm.toLinearMap := by
  apply LinearMap.ext
  intro a
  change nativeProj D ((ambientBasis D).equivFun.symm (fieldCoords F K a)) = _
  rw [ambient_synthesis_field]
  rfl

theorem nativeGenerator_field_injective (D : DelsarteSetting F K V) :
    Function.Injective (((nativeGenerator D).restrictScalars F).comp (fieldCoords F K)) := by
  rw [nativeGenerator_field]
  exact (nativeProj_W_injective D).comp (formBasis D).equivFun.symm.injective

theorem nativeGenerator_field_range (D : DelsarteSetting F K V) :
    LinearMap.range (((nativeGenerator D).restrictScalars F).comp (fieldCoords F K)) = D.U := by
  rw [nativeGenerator_field, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearMap.range_comp,
    Submodule.range_subtype, nativeProj_W_image]

theorem nativeGenerator_ker_finrank (D : DelsarteSetting F K V) :
    finrank K (LinearMap.ker (nativeGenerator D)) + finrank K D.Λ = finrank F D.W := by
  have he := (nativeGenerator D).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (nativeGenerator_surjective D), finrank_top,
    Module.finrank_pi] at he
  simp only [Fintype.card_fin] at he
  omega

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/CoordinateRows.lean

open scoped BigOperators

namespace HScattered.Delsarte.HSDFresh

variable {F K I J : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Fintype J]

noncomputable def coordinateRows (v : I → K)
    (b : Module.Basis J F (Submodule.span F (Set.range v))) (j : J) (i : I) : F :=
  b.repr ⟨v i, coord_mem_span F v i⟩ j

omit [FiniteDimensional F K] [Fintype J] in
theorem coordinateRows_independent (v : I → K)
    (b : Module.Basis J F (Submodule.span F (Set.range v))) :
    LinearIndependent F (coordinateRows v b) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hg j hj
  let T := Submodule.span F (Set.range v)
  let L : T →ₗ[F] F := ∑ a ∈ s, g a • b.coord a
  have hL : L = 0 := by
    apply LinearMap.ext_on ((Submodule.span_range_subtype_eq_top_iff T
      (coord_mem_span F v)).mpr rfl)
    rintro _ ⟨i, rfl⟩
    have hi := congrFun hg i
    simpa [L, coordinateRows, Module.Basis.coord_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hi
  have he := LinearMap.congr_fun hL (b j)
  simpa [L, Module.Basis.coord_apply, Finsupp.single_apply, hj] using he

omit [FiniteDimensional F K] in
theorem coordinateRows_reconstruct (v : I → K)
    (b : Module.Basis J F (Submodule.span F (Set.range v))) :
    (∑ j, (b j : K) • fieldCoords F K (coordinateRows v b j)) = v := by
  classical
  funext i
  have he := congrArg Subtype.val (b.sum_repr ⟨v i, coord_mem_span F v i⟩)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fieldCoords_apply, coordinateRows]
  change ∑ j, (b j : K) * algebraMap F K (b.repr ⟨v i, coord_mem_span F v i⟩ j) = v i
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def, mul_comm] using he

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/LowerScattered.lean

namespace HScattered.Delsarte.HSDFresh

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional K V] [FiniteDimensional F K]

theorem scattered_intersection_le {h : ℕ} {U : Submodule F V}
    (hU : IsHScattered F K h U) (S : Submodule K V)
    (hS : Module.finrank K S ≤ h) :
    Module.finrank F ↥(S.restrictScalars F ⊓ U) ≤ Module.finrank K S := by
  let : FiniteDimensional F V := FiniteDimensional.trans F K V
  have hgeneral : ∀ q : ℕ, ∀ S : Submodule K V,
      h - Module.finrank K S = q → Module.finrank K S ≤ h →
      Module.finrank F ↥(S.restrictScalars F ⊓ U) ≤ Module.finrank K S := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro S hq hS
      by_cases he : Module.finrank K S = h
      · exact (hU.2.2.2 S he).trans_eq he.symm
      have hlt : Module.finrank K S < h := by omega
      obtain ⟨u, hu, huS⟩ : ∃ u ∈ U, u ∉ S := by
        by_contra! hc
        have hs : Submodule.span K (U : Set V) ≤ S := Submodule.span_le.mpr hc
        rw [hU.2.2.1] at hs
        have heq : S = ⊤ := top_le_iff.mp hs
        have hdim : Module.finrank K S = Module.finrank K V := by rw [heq]; exact finrank_top K V
        have hh := hU.2.1
        omega
      let T : Submodule K V := S ⊔ Submodule.span K {u}
      have hT : Module.finrank K T = Module.finrank K S + 1 :=
        Submodule.finrank_sup_span_singleton huS
      have hb := ih (h - Module.finrank K T) (by omega) T rfl (by omega)
      have huI : u ∉ S.restrictScalars F ⊓ U := fun hx => huS hx.1
      have hdim := Submodule.finrank_sup_span_singleton huI
      have hsub : (S.restrictScalars F ⊓ U) ⊔ Submodule.span F {u} ≤
          T.restrictScalars F ⊓ U := by
        apply sup_le
        · intro x hx
          exact ⟨(show S ≤ T from le_sup_left) hx.1, hx.2⟩
        · apply Submodule.span_le.mpr
          intro x hx
          have hx' : x = u := Set.mem_singleton_iff.mp hx
          subst x
          exact ⟨(show Submodule.span K {u} ≤ T from le_sup_right) (Submodule.mem_span_singleton_self u), hu⟩
      have hm := Submodule.finrank_mono hsub
      omega
  exact hgeneral (h - Module.finrank K S) S rfl hS

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/ScatteredKernel.lean

open scoped BigOperators

namespace HScattered.Delsarte.HSDFresh

variable {F K I V : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype I] [AddCommGroup V] [Module K V] [Module F V]
  [IsScalarTower F K V] [FiniteDimensional K V] [FiniteDimensional F K]

omit [Fintype I] in
theorem scattered_kernel_rank {h : ℕ} {U : Submodule F V}
    (hU : IsHScattered F K h U) (G : (I → K) →ₗ[K] V)
    (hGI : Function.Injective ((G.restrictScalars F).comp (fieldCoords F K)))
    (hGU : ∀ w : I → F, G (fieldCoords F K w) ∈ U)
    {v : I → K} (hv : v ≠ 0) (hGv : G v = 0) : h + 1 < coordRank F v := by
  classical
  let : FiniteDimensional F V := FiniteDimensional.trans F K V
  by_contra! hsmall
  let T := Submodule.span F (Set.range v)
  let b := Module.finBasis F T
  let w := coordinateRows v b
  let H := (G.restrictScalars F).comp (fieldCoords F K)
  let z := fun j => H (w j)
  have hw : LinearIndependent F w := coordinateRows_independent v b
  have hz : LinearIndependent F z := hw.map' H (LinearMap.ker_eq_bot.mpr hGI)
  have hrecon : ∑ j, (b j : K) • z j = 0 := by
    have he := congrArg G (coordinateRows_reconstruct v b)
    rw [map_sum, hGv] at he
    simp only [map_smul] at he
    exact he
  have hpos : 0 < Module.finrank F T := by
    have hn := (coordRank_eq_zero_iff F v).not.mpr hv
    change Module.finrank F T ≠ 0 at hn
    omega
  have hdep : ¬ LinearIndependent K z := by
    intro hind
    have he := linearIndependent_iff'.mp hind Finset.univ (fun j => (b j : K)) hrecon
    let j : Fin (Module.finrank F T) := ⟨0, hpos⟩
    have hj := he j (Finset.mem_univ j)
    exact b.ne_zero j (Subtype.ext hj)
  let S := Submodule.span K (Set.range z)
  have hdim : Module.finrank K S < Module.finrank F T := by
    have hle := finrank_range_le_card (R := K) z
    change Module.finrank K S ≤ Fintype.card (Fin (Module.finrank F T)) at hle
    have hne : Module.finrank K S ≠ Module.finrank F T := by
      intro he
      apply hdep
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      change Fintype.card (Fin (Module.finrank F T)) = Module.finrank K S
      rw [Fintype.card_fin]
      exact he.symm
    simp only [Fintype.card_fin] at hle
    omega
  have hinc : Submodule.span F (Set.range z) ≤ S.restrictScalars F ⊓ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨Submodule.subset_span ⟨j, rfl⟩, hGU (w j)⟩
  have hlow := Submodule.finrank_mono hinc
  rw [finrank_span_eq_card hz, Fintype.card_fin] at hlow
  have hbound := scattered_intersection_le hU S (by change Module.finrank F T ≤ h + 1 at hsmall; omega)
  omega

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/CoordinateQuotient.lean

open scoped BigOperators

namespace HScattered.Delsarte.HSDFresh

variable {F K I : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def coordQuotient (T : Submodule F K) : (I → K) →ₗ[F] (I → K ⧸ T) where
  toFun v i := T.mkQ (v i)
  map_add' v w := by ext i; exact map_add T.mkQ _ _
  map_smul' a v := by ext i; exact map_smul T.mkQ _ _

@[simp] theorem coordQuotient_apply (T : Submodule F K) (v : I → K) (i : I) :
    coordQuotient T v i = T.mkQ (v i) := rfl

noncomputable def codeQuotient (C : Submodule K (I → K)) (T : Submodule F K) :
    C →ₗ[F] (I → K ⧸ T) :=
  (coordQuotient T).comp (C.subtype.restrictScalars F)

variable [FiniteDimensional F K]

theorem codeQuotient_injective (C : Submodule K (I → K)) (T : Submodule F K)
    (hC : ∀ v ∈ C, v ≠ 0 → Module.finrank F T < coordRank F v) :
    Function.Injective (codeQuotient C T) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply Subtype.ext
  by_contra hne
  have hmem : ∀ i, (v : I → K) i ∈ T := by
    intro i
    have hi := congrFun hv i
    exact (Submodule.Quotient.mk_eq_zero T).mp hi
  exact (hC v v.property hne).not_ge (coordRank_le_of_mem F T hmem)

variable [Fintype I]

theorem codeQuotient_dimension_bound (C : Submodule K (I → K)) (T : Submodule F K)
    (hC : ∀ v ∈ C, v ≠ 0 → Module.finrank F T < coordRank F v) :
    Module.finrank F C ≤ Fintype.card I * Module.finrank F (K ⧸ T) := by
  have h := LinearMap.finrank_le_finrank_of_injective (codeQuotient_injective C T hC)
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id] using h

theorem codeQuotient_surjective (C : Submodule K (I → K)) (T : Submodule F K)
    (hC : ∀ v ∈ C, v ≠ 0 → Module.finrank F T < coordRank F v)
    (hdim : Module.finrank F C = Fintype.card I * Module.finrank F (K ⧸ T)) :
    Function.Surjective (codeQuotient C T) := by
  have : FiniteDimensional F C := Module.Finite.of_injective
    (C.subtype.restrictScalars F) C.subtype_injective
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (codeQuotient_injective C T hC)
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id] using hdim

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/MultiplicationPairing.lean

namespace HScattered.Delsarte.HSDFresh

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def multiplicationPairing (ℓ : K →ₗ[F] F) : LinearMap.BilinForm F K where
  toFun x :=
    { toFun := fun y => ℓ (x * y)
      map_add' := by intro y z; simp only [mul_add, map_add]
      map_smul' := by intro a y; simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro x y
    ext z
    change ℓ ((x + y) * z) = ℓ (x * z) + ℓ (y * z)
    rw [add_mul, map_add]
  map_smul' := by
    intro a x
    ext y
    change ℓ ((a • x) * y) = a • ℓ (x * y)
    rw [smul_mul_assoc, map_smul]

@[simp] theorem multiplicationPairing_apply (ℓ : K →ₗ[F] F) (x y : K) :
    multiplicationPairing ℓ x y = ℓ (x * y) := rfl

theorem multiplicationPairing_nondegenerate (ℓ : K →ₗ[F] F) (hℓ : ℓ 1 = 1) :
    (multiplicationPairing ℓ).Nondegenerate := by
  constructor
  · intro x hx
    by_contra h
    have hz := hx x⁻¹
    simp [h, hℓ] at hz
  · intro y hy
    by_contra h
    have hz := hy y⁻¹
    simp [h, hℓ] at hz

theorem exists_normalized_functional : ∃ ℓ : K →ₗ[F] F, ℓ 1 = 1 :=
  Module.Projective.exists_dual_eq_one F one_ne_zero

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/SubspaceDimension.lean

namespace HScattered.Delsarte.HSDFresh

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem exists_subspace_dim (S : Submodule F V) {m : ℕ}
    (hm : m ≤ Module.finrank F S) :
    ∃ T : Submodule F V, T ≤ S ∧ Module.finrank F T = m := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hm
  let w : Fin m → V := fun i => (v i : V)
  have hw : LinearIndependent F w := hv.map' S.subtype S.ker_subtype
  refine ⟨Submodule.span F (Set.range w), ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).property)
  · simpa only [Fintype.card_fin] using finrank_span_eq_card hw

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/SingletonDuality.lean

open scoped BigOperators

namespace HScattered.Delsarte.HSDFresh

variable {F K I : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Fintype I]

theorem singleton_dual_rank (C : Submodule K (I → K)) (d : ℕ)
    (hd : d ≤ Module.finrank F K)
    (hC : ∀ v ∈ C, v ≠ 0 → d < coordRank F v)
    (hdim : Module.finrank F C = Fintype.card I * (Module.finrank F K - d))
    (b : I → K) (hb : b ≠ 0)
    (horth : ∀ c ∈ C, ∑ i, c i * b i = 0) :
    Module.finrank F K - d < coordRank F b := by
  classical
  by_contra! hsmall
  obtain ⟨ℓ, hℓ⟩ := exists_normalized_functional (F := F) (K := K)
  let R : Submodule F K := Submodule.span F (Set.range b)
  let A := (multiplicationPairing ℓ).orthogonal R
  have hA : d ≤ Module.finrank F A := by
    have he := LinearMap.BilinForm.finrank_orthogonal
      (multiplicationPairing_nondegenerate ℓ hℓ) R
    change Module.finrank F A = Module.finrank F K - coordRank F b at he
    omega
  obtain ⟨T, hTA, hT⟩ := exists_subspace_dim A hA
  have hCT : ∀ v ∈ C, v ≠ 0 → Module.finrank F T < coordRank F v := by
    simpa only [hT] using hC
  have hquot : Module.finrank F (K ⧸ T) = Module.finrank F K - d := by
    have he := Submodule.finrank_quotient_add_finrank T
    omega
  have hsurj := codeQuotient_surjective C T hCT (hdim.trans (by rw [hquot]))
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra! hh
    exact hb (funext hh)
  let y : I → K := Pi.single i (b i)⁻¹
  obtain ⟨c, hc⟩ := hsurj (coordQuotient T y)
  have hterm (j : I) : ℓ ((c : I → K) j * b j) = ℓ (y j * b j) := by
    have hdiff : (c : I → K) j - y j ∈ T := by
      apply (Submodule.Quotient.mk_eq_zero T).mp
      change T.mkQ ((c : I → K) j - y j) = 0
      rw [map_sub]
      have he := congrFun hc j
      change T.mkQ ((c : I → K) j) = T.mkQ (y j) at he
      rw [he, sub_self]
    have hz := hTA hdiff (b j) (coord_mem_span F b j)
    change ℓ (b j * ((c : I → K) j - y j)) = 0 at hz
    rw [mul_sub, map_sub] at hz
    simpa only [mul_comm] using sub_eq_zero.mp hz
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hterm j)
  rw [← map_sum, horth c c.property, map_zero] at he
  have hy : (∑ j, ℓ (y j * b j)) = 1 := by
    simp only [y, Pi.single_apply, ite_mul, zero_mul]
    simp only [apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_mul_cancel₀ hi, hℓ]
  rw [hy] at he
  exact zero_ne_one he

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeRankBound.lean

noncomputable section
open scoped Classical BigOperators
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V] [FiniteDimensional K V] [FiniteDimensional F K]

theorem native_kernel_rank (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U)
    (v : Fin (finrank F D.W) → K) (hv : v ≠ 0)
    (hc : v ∈ LinearMap.ker (nativeGenerator D)) : h + 1 < coordRank F v := by
  apply scattered_kernel_rank hU (nativeGenerator D) (nativeGenerator_field_injective D) _ hv hc
  intro a
  rw [← nativeGenerator_field_range D]
  exact LinearMap.mem_range_self _ a

omit [FiniteDimensional K V] in
theorem native_kernel_dimension (D : DelsarteSetting F K V) (h : ℕ)
    (hd : h + 1 ≤ finrank F K)
    (he : (h + 1) * finrank F D.U = finrank K D.Λ * finrank F K) :
    finrank F (LinearMap.ker (nativeGenerator D)) =
      finrank F D.W * (finrank F K - (h + 1)) := by
  have hk := nativeGenerator_ker_finrank D
  have ht := Module.finrank_mul_finrank F K (LinearMap.ker (nativeGenerator D))
  rw [native_U_finrank, ← D.finrank_W] at he
  have hs := Nat.sub_add_cancel hd
  nlinarith

omit [FiniteDimensional K V] [FiniteDimensional F K] in
theorem native_W_ne_bot (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U) : D.W ≠ ⊥ := by
  intro he
  have hk := nativeGenerator_ker_finrank D
  have hw0 : finrank F D.W = 0 := by rw [he, finrank_bot]
  have hh := hU.2.1
  omega

theorem native_orth_rank [Fintype F] [Fintype K]
    (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U) (hd : h + 1 ≤ finrank F K)
    (he : (h + 1) * finrank F D.U = finrank K D.Λ * finrank F K)
    (x : V) (hx : x ∈ D.orth D.Γ) (hn : x ≠ 0) :
    finrank F K - (h + 1) < coordRank F ((ambientBasis D).equivFun x) := by
  have hb := singleton_dual_rank (LinearMap.ker (nativeGenerator D)) (h + 1) hd
    (fun v hv hn => native_kernel_rank D hU v hn hv)
    (by simpa only [Fintype.card_fin] using native_kernel_dimension D h hd he)
    (nativeColumn D x) (nativeColumn_ne_zero D hn) (nativeColumn_orth D x hx)
  rw [nativeColumn_rank D (native_W_ne_bot D hU) x] at hb
  exact hb

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/KernelScattered.lean

open scoped BigOperators

namespace HScattered.Delsarte.HSDFresh

variable {F K I V : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype I] [AddCommGroup V] [Module K V] [Module F V]
  [IsScalarTower F K V] [FiniteDimensional K V] [FiniteDimensional F K]

theorem kernel_scattered_intersection {h : ℕ} (U : Submodule F V)
    (G : (I → K) →ₗ[K] V)
    (hGU : ∀ u ∈ U, ∃ w : I → F, G (fieldCoords F K w) = u)
    (hker : ∀ v : I → K, v ≠ 0 → G v = 0 → h + 1 < coordRank F v)
    (S : Submodule K V) (hS : Module.finrank K S = h) :
    Module.finrank F ↥(S.restrictScalars F ⊓ U) ≤ h := by
  classical
  let : FiniteDimensional F V := FiniteDimensional.trans F K V
  by_contra! hlarge
  obtain ⟨z, hz⟩ := exists_linearIndependent_of_le_finrank (show h + 1 ≤
    Module.finrank F ↥(S.restrictScalars F ⊓ U) by omega)
  choose w hw using fun j => hGU (z j) (z j).property.2
  let H := (G.restrictScalars F).comp (fieldCoords F K)
  have hzV : LinearIndependent F (fun j => (z j : V)) :=
    hz.map' (S.restrictScalars F ⊓ U).subtype (S.restrictScalars F ⊓ U).ker_subtype
  have hwF : LinearIndependent F w := by
    have he : (fun j => H (w j)) = (fun j => (z j : V)) := funext hw
    rw [← he] at hzV
    exact hzV.of_comp
  have hwK : LinearIndependent K (fun j => fieldCoords F K (w j)) :=
    linearIndependent_algebraMap_comp_iff.mpr hwF
  have hdep : ¬LinearIndependent K (fun j => (z j : V)) := by
    intro hc
    have hsub : Submodule.span K (Set.range fun j => (z j : V)) ≤ S :=
      Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact (z j).property.1)
    have hh := Submodule.finrank_mono hsub
    rw [finrank_span_eq_card hc, Fintype.card_fin, hS] at hh
    omega
  obtain ⟨a, ha, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let v : I → K := ∑ j, a j • fieldCoords F K (w j)
  have hv : v ≠ 0 := by
    intro he
    exact hj (Fintype.linearIndependent_iff.mp hwK a he j)
  have hGv : G v = 0 := by
    simp only [v, map_sum, map_smul, hw]
    exact ha
  have hr : coordRank F v ≤ h + 1 := by
    apply (coordRank_le_of_mem F (Submodule.span F (Set.range a)) (fun i => ?_)).trans
      (by
        have hh := finrank_range_le_card (R := F) a
        change Module.finrank F (Submodule.span F (Set.range a)) ≤ Fintype.card (Fin (h + 1)) at hh
        rw [Fintype.card_fin] at hh
        exact hh)
    change (∑ j, a j • fieldCoords F K (w j)) i ∈ _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fieldCoords_apply]
    apply Submodule.sum_mem
    intro j _
    have he : a j * algebraMap F K (w j i) = (w j i) • a j := by
      rw [Algebra.smul_def, mul_comm]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact (not_lt_of_ge hr) (hker v hv hGv)

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/DotOrthogonal.lean

noncomputable section
open scoped Classical BigOperators
namespace HScattered.Delsarte.HSDFresh
variable {K I : Type*} [Field K] [Fintype I]

def dotForm : LinearMap.BilinForm K (I → K) := dotProductBilin K K

theorem dotForm_nondegenerate : (dotForm (K := K) (I := I)).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    simpa [dotForm, dotProduct, Pi.single_apply] using h
  · intro y hy
    funext i
    have h := hy (Pi.single i 1)
    simpa [dotForm, dotProduct, Pi.single_apply] using h

def dotOrth (C : Submodule K (I → K)) : Submodule K (I → K) :=
  (dotForm (K := K)).orthogonal C

theorem mem_dotOrth (C : Submodule K (I → K)) (b : I → K) :
    b ∈ dotOrth C ↔ ∀ c ∈ C, ∑ i, c i * b i = 0 := Iff.rfl

theorem dotOrth_finrank (C : Submodule K (I → K)) :
    Module.finrank K (dotOrth C) = Fintype.card I - Module.finrank K C := by
  have h := LinearMap.BilinForm.finrank_orthogonal
    (dotForm_nondegenerate (K := K) (I := I)) C
  change Module.finrank K (dotForm.orthogonal C) = _
  rw [h]
  congr 1
  exact Module.finrank_fintype_fun_eq_card K

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/OrthogonalDimension.lean

noncomputable section
open scoped Classical BigOperators
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V] [FiniteDimensional K V] [Fintype K]

def nativeColumnEquiv (D : DelsarteSetting F K V) : V ≃ (Fin (finrank F D.W) → K) :=
  ((ambientBasis D).equivFun.toEquiv.trans
    (Equiv.piCongrRight fun _ => D.σ.toEquiv)).trans (gramEquiv D).toEquiv

omit [FiniteDimensional K V] in
theorem nativeColumnEquiv_apply (D : DelsarteSetting F K V) (x : V) :
    nativeColumnEquiv D x = nativeColumn D x := (nativeColumn_eq D x).symm

omit [FiniteDimensional K V] [Fintype K] in
theorem nativeColumn_orth_iff (D : DelsarteSetting F K V) (x : V) :
    x ∈ D.orth D.Γ ↔ nativeColumn D x ∈ dotOrth (LinearMap.ker (nativeGenerator D)) := by
  rw [mem_dotOrth]
  constructor
  · intro hx c hc
    exact nativeColumn_orth D x hx c hc
  · intro h
    change x ∈ ⨅ s : D.Γ, LinearMap.ker (D.β.flip (s : V))
    rw [Submodule.mem_iInf]
    intro s
    have hc : (ambientBasis D).equivFun (s : V) ∈ LinearMap.ker (nativeGenerator D) := by
      rw [nativeGenerator_ker]
      change (ambientBasis D).equivFun.symm ((ambientBasis D).equivFun (s : V)) ∈ D.Γ
      simpa only [LinearEquiv.symm_apply_apply] using s.property
    have hz := h _ hc
    rw [nativeColumn_dot] at hz
    exact D.reflexive _ _ hz

theorem native_orth_finrank (D : DelsarteSetting F K V) :
    finrank K (D.orth D.Γ) = finrank K D.Λ := by
  let e := (nativeColumnEquiv D).subtypeEquiv
    (p := fun x => x ∈ D.orth D.Γ)
    (q := fun b => b ∈ dotOrth (LinearMap.ker (nativeGenerator D)))
    (fun x => by rw [nativeColumnEquiv_apply]; exact nativeColumn_orth_iff D x)
  have he := finrank_eq_of_equiv (K := K) e
  rw [dotOrth_finrank, Fintype.card_fin] at he
  have hdim := nativeGenerator_ker_finrank D
  omega

theorem native_quotient_finrank (D : DelsarteSetting F K V) :
    finrank K (V ⧸ D.orth D.Γ) + finrank K D.Λ = finrank K V := by
  rw [← native_orth_finrank D]
  exact Submodule.finrank_quotient_add_finrank _

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeDual.lean

noncomputable section
open scoped Classical BigOperators
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V] [FiniteDimensional K V] [FiniteDimensional F K]

omit [FiniteDimensional F V] [FiniteDimensional K V] in
theorem coordRank_field_le_one {I : Type*} (a : I → F) :
    coordRank F (fieldCoords F K a) ≤ 1 := by
  have hh := coordRank_le_of_mem F (LinearMap.range (Algebra.linearMap F K))
    (v := fieldCoords F K a) (fun i => ⟨a i, rfl⟩)
  have hd := LinearMap.finrank_range_of_inj (show Function.Injective (Algebra.linearMap F K) from (algebraMap F K).injective)
  rw [Module.finrank_self] at hd
  rwa [hd] at hh

omit [FiniteDimensional F V] [FiniteDimensional K V] [FiniteDimensional F K] in
theorem native_dual_span (D : DelsarteSetting F K V) :
    Submodule.span K (D.dual : Set (V ⧸ D.orth D.Γ)) = ⊤ := by
  change Submodule.span K (((D.orth D.Γ).mkQ) '' (D.W : Set V)) = ⊤
  rw [← Submodule.map_span, D.span_W, Submodule.map_top,
    Submodule.range_mkQ]

def dualGenerator (D : DelsarteSetting F K V) :
    (Fin (finrank F D.W) → K) →ₗ[K] (V ⧸ D.orth D.Γ) :=
  (D.orth D.Γ).mkQ.comp (ambientBasis D).equivFun.symm.toLinearMap

omit [FiniteDimensional K V] [FiniteDimensional F K] in
theorem dualGenerator_field_surj (D : DelsarteSetting F K V)
    (u : V ⧸ D.orth D.Γ) (hu : u ∈ D.dual) :
    ∃ a : Fin (finrank F D.W) → F, dualGenerator D (fieldCoords F K a) = u := by
  obtain ⟨w, hw, he⟩ := hu
  refine ⟨(formBasis D).equivFun ⟨w, hw⟩, ?_⟩
  change (D.orth D.Γ).mkQ ((ambientBasis D).equivFun.symm (fieldCoords F K _)) = u
  rw [ambient_synthesis_field, LinearEquiv.symm_apply_apply]
  exact he

theorem native_dual_injective [Fintype F] [Fintype K]
    (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U) (hd : h + 3 ≤ finrank F K)
    (he : (h + 1) * finrank F D.U = finrank K D.Λ * finrank F K) :
    Function.Injective (((D.orth D.Γ).mkQ.restrictScalars F).comp D.W.subtype) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro w hw
  by_contra hn
  have hn' : (w : V) ≠ 0 := by simpa using hn
  have hw' : (w : V) ∈ D.orth D.Γ := (Submodule.Quotient.mk_eq_zero _).mp hw
  have hr := native_orth_rank D hU (by omega) he w hw' hn'
  rw [ambient_coordinates_form] at hr
  have hl := coordRank_field_le_one (K := K) ((formBasis D).equivFun w)
  omega

theorem native_dual_finrank [Fintype F] [Fintype K]
    (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U) (hd : h + 3 ≤ finrank F K)
    (he : (h + 1) * finrank F D.U = finrank K D.Λ * finrank F K) :
    finrank F D.dual = finrank K V := by
  have hi := LinearMap.finrank_range_of_inj (native_dual_injective D hU hd he)
  rw [LinearMap.range_comp, Submodule.range_subtype] at hi
  exact hi.trans D.finrank_W

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeDualScattered.lean

noncomputable section
open scoped Classical
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V] [FiniteDimensional K V] [FiniteDimensional F K]
  [Fintype F] [Fintype K]

omit [FiniteDimensional F K] [Fintype F] in
theorem native_dual_dimension_lower (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U) (hd : h + 3 ≤ finrank F K)
    (he : (h + 1) * finrank F D.U = finrank K D.Λ * finrank F K) :
    finrank F K - (h + 1) ≤ finrank K (V ⧸ D.orth D.Γ) := by
  have hq := native_quotient_finrank D
  rw [native_U_finrank] at he
  have hs := Nat.sub_add_cancel (show h + 1 ≤ finrank F K by omega)
  have hr := hU.2.1
  have hm : (h + 1) * (finrank F K - (h + 1)) ≤
      finrank K D.Λ * (finrank F K - (h + 1)) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem native_dual_scattered (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U) (hd : h + 3 ≤ finrank F K)
    (he : (h + 1) * finrank F D.U = finrank K D.Λ * finrank F K) :
    IsHScattered F K (finrank F K - h - 2) D.dual := by
  have hq := native_dual_dimension_lower D hU hd he
  refine ⟨by omega, by omega, native_dual_span D, ?_⟩
  intro S hS
  apply kernel_scattered_intersection D.dual (dualGenerator D)
    (dualGenerator_field_surj D) _ S hS
  intro a ha hz
  let x := (ambientBasis D).equivFun.symm a
  have hx : x ∈ D.orth D.Γ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hn : x ≠ 0 := by
    intro hh
    apply ha
    have hh' := congrArg (ambientBasis D).equivFun hh
    change (ambientBasis D).equivFun ((ambientBasis D).equivFun.symm a) = _ at hh'
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using hh'
  have hb := native_orth_rank D hU (by omega) he x hx hn
  change finrank F K - (h + 1) < coordRank F
    ((ambientBasis D).equivFun ((ambientBasis D).equivFun.symm a)) at hb
  rw [LinearEquiv.apply_symm_apply] at hb
  have hid : finrank F K - h - 2 + 1 = finrank F K - (h + 1) := by omega
  rwa [hid]

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/BasisGenerator.lean

open scoped BigOperators

namespace HScattered.Delsarte.HSDFresh

variable {F K V J : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [Fintype J]

noncomputable def basisGenerator {U : Submodule F V} (b : Module.Basis J F U) :
    (J → K) →ₗ[K] V := Fintype.linearCombination K (fun j => (b j : V))

theorem basisGenerator_field {U : Submodule F V} (b : Module.Basis J F U) (a : J → F) :
    basisGenerator b (fieldCoords F K a) = (b.equivFun.symm a : V) := by
  classical
  rw [Module.Basis.equivFun_symm_apply]
  simp only [basisGenerator, Fintype.linearCombination_apply, fieldCoords_apply,
    Submodule.coe_sum, Submodule.coe_smul, IsScalarTower.algebraMap_smul]

theorem basisGenerator_field_injective {U : Submodule F V} (b : Module.Basis J F U) :
    Function.Injective (((basisGenerator b).restrictScalars F).comp (fieldCoords F K)) := by
  intro a c he
  change basisGenerator b (fieldCoords F K a) = basisGenerator b (fieldCoords F K c) at he
  rw [basisGenerator_field, basisGenerator_field] at he
  exact b.equivFun.symm.injective (Subtype.ext he)

theorem basisGenerator_field_mem {U : Submodule F V} (b : Module.Basis J F U) (a : J → F) :
    basisGenerator b (fieldCoords F K a) ∈ U := by
  rw [basisGenerator_field]
  exact (b.equivFun.symm a).property

theorem basisGenerator_field_lift {U : Submodule F V} (b : Module.Basis J F U)
    (u : V) (hu : u ∈ U) : ∃ a : J → F, basisGenerator b (fieldCoords F K a) = u := by
  refine ⟨b.equivFun ⟨u, hu⟩, ?_⟩
  rw [basisGenerator_field, LinearEquiv.symm_apply_apply]

theorem basisGenerator_surjective {U : Submodule F V} (b : Module.Basis J F U)
    (hspan : Submodule.span K (U : Set V) = ⊤) : Function.Surjective (basisGenerator (K := K) b) := by
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro u hu
  obtain ⟨a, ha⟩ := basisGenerator_field_lift (K := K) b u hu
  exact ⟨fieldCoords F K a, ha⟩

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/GeneratorSingleton.lean

namespace HScattered.Delsarte.HSDFresh

variable {F K I V : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype I] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [FiniteDimensional F K]

omit [FiniteDimensional K V] in
theorem generator_singleton_bound (G : (I → K) →ₗ[K] V)
    (hsurj : Function.Surjective G) (d : ℕ) (hd : d ≤ Module.finrank F K)
    (hker : ∀ v : I → K, v ≠ 0 → G v = 0 → d < coordRank F v) :
    Fintype.card I * d ≤ Module.finrank F K * Module.finrank K V := by
  obtain ⟨T, _, hT⟩ := exists_subspace_dim (⊤ : Submodule F K)
    (show d ≤ Module.finrank F (⊤ : Submodule F K) by simpa only [finrank_top] using hd)
  have hC : ∀ v ∈ LinearMap.ker G, v ≠ 0 → Module.finrank F T < coordRank F v := by
    intro v hv hn
    rw [hT]
    exact hker v hn hv
  have hb := codeQuotient_dimension_bound (LinearMap.ker G) T hC
  have hq := Submodule.finrank_quotient_add_finrank T
  have hr := G.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi] at hr
  have ht := Module.finrank_mul_finrank F K (LinearMap.ker G)
  rw [← ht] at hb
  nlinarith

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/ScatteredSingleton.lean

namespace HScattered.Delsarte.HSDFresh

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional K V] [FiniteDimensional F K]

theorem scattered_singleton_bound {h : ℕ} {U : Submodule F V}
    (hU : IsHScattered F K h U) (hd : h + 1 ≤ Module.finrank F K) :
    Module.finrank F U * (h + 1) ≤ Module.finrank F K * Module.finrank K V := by
  let : FiniteDimensional F V := FiniteDimensional.trans F K V
  let b := Module.finBasis F U
  have hb := generator_singleton_bound (basisGenerator b)
    (basisGenerator_surjective b hU.2.2.1) (h + 1) hd
    (fun v hv hGv => scattered_kernel_rank hU (basisGenerator b)
      (basisGenerator_field_injective b) (basisGenerator_field_mem b) hv hGv)
  simpa only [Fintype.card_fin] using hb

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeMaximum.lean

noncomputable section
open scoped Classical
open Module
namespace HScattered.Delsarte.HSDFresh
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional F V] [FiniteDimensional K V] [FiniteDimensional F K]
  [Fintype F] [Fintype K]

theorem native_dual_maximum (D : DelsarteSetting F K V) {h : ℕ}
    (hU : IsHScattered F K h D.U) (hd : h + 3 ≤ finrank F K)
    (he : (h + 1) * finrank F D.U = finrank K D.Λ * finrank F K) :
    IsMaximumHScattered F K (finrank F K - h - 2) D.dual := by
  refine ⟨native_dual_scattered D hU hd he, ?_⟩
  intro U hU'
  have hb := scattered_singleton_bound hU' (show finrank F K - h - 2 + 1 ≤ finrank F K by omega)
  rw [native_dual_finrank D hU hd he]
  have hq := native_quotient_finrank D
  rw [native_U_finrank] at he
  have hs : finrank F K - h - 2 + 1 + (h + 1) = finrank F K := by omega
  have hp : 0 < finrank F K - h - 2 + 1 := by omega
  nlinarith

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/NativeConclusion.lean

noncomputable section
namespace HScattered.Delsarte.HSDFresh

theorem native_theorem_3_3 {F K 𝕍 : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍]
    [Fintype F] [Fintype K] [FiniteDimensional K 𝕍]
    (D : DelsarteSetting F K 𝕍) (h r n : ℕ)
    (hr : Module.finrank K D.Λ = r) (hn : Module.finrank F K = n)
    (hU : IsMaximumHScattered F K h D.U)
    (hdim : (h + 1) * Module.finrank F D.U = r * n)
    (hnh : h + 3 ≤ n) :
    IsMaximumHScattered F K (n - h - 2) D.dual ∧
      Module.finrank F D.dual = Module.finrank K 𝕍 ∧
      Module.finrank K (𝕍 ⧸ D.orth D.Γ) + r = Module.finrank K 𝕍 := by
  let : FiniteDimensional F K := inferInstance
  let : FiniteDimensional F 𝕍 := FiniteDimensional.trans F K 𝕍
  have hd : h + 3 ≤ Module.finrank F K := by omega
  have he : (h + 1) * Module.finrank F D.U =
      Module.finrank K D.Λ * Module.finrank F K := by simpa only [hr, hn] using hdim
  refine ⟨?_, native_dual_finrank D hU.1 hd he, ?_⟩
  · simpa only [hn] using native_dual_maximum D hU.1 hd he
  · simpa only [hr] using native_quotient_finrank D

end HScattered.Delsarte.HSDFresh

-- Complete module: HSDProof/FinalRoot.lean

namespace HScattered.Delsarte

/-- Theorem 3.3 (arXiv:1906.10590v2, p. 9): in the setting of §3, let `U = ⟨W, Γ⟩_{𝔽_q} ∩ Λ` be a
maximum h-scattered `𝔽_q`-subspace of `Λ = V(r, qⁿ)` of dimension `rn/(h + 1)`, with `n ≥ h + 3`.
Then its Delsarte dual `Ū = W + Γ^⊥` is a maximum `(n − h − 2)`-scattered `𝔽_q`-subspace of
`𝕍 / Γ^⊥`; moreover `Ū` has dimension `k = dim 𝕍 = rn/(h + 1)` and `𝕍 / Γ^⊥` has dimension
`rn/(h + 1) − r` (stated as `dim (𝕍 / Γ^⊥) + r = k`). -/
theorem theorem_3_3 {F K 𝕍 : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍]
    [Fintype F] [Fintype K] [FiniteDimensional K 𝕍]
    (D : DelsarteSetting F K 𝕍) (h r n : ℕ)
    (hr : Module.finrank K D.Λ = r) (hn : Module.finrank F K = n)
    (hU : IsMaximumHScattered F K h D.U)
    (hdim : (h + 1) * Module.finrank F D.U = r * n)
    (hnh : h + 3 ≤ n) :
    IsMaximumHScattered F K (n - h - 2) D.dual ∧
      Module.finrank F D.dual = Module.finrank K 𝕍 ∧
      Module.finrank K (𝕍 ⧸ D.orth D.Γ) + r = Module.finrank K 𝕍 := by
  exact HSDFresh.native_theorem_3_3 D h r n hr hn hU hdim hnh

end HScattered.Delsarte


open HScattered.Delsarte
open scoped BigOperators
theorem solution {F K 𝕍 : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍]
    [Fintype F] [Fintype K] [FiniteDimensional K 𝕍]
    (D : DelsarteSetting F K 𝕍) (h r n : ℕ)
    (hr : Module.finrank K D.Λ = r) (hn : Module.finrank F K = n)
    (hU : IsMaximumHScattered F K h D.U)
    (hdim : (h + 1) * Module.finrank F D.U = r * n)
    (hnh : h + 3 ≤ n) :
    IsMaximumHScattered F K (n - h - 2) D.dual ∧
      Module.finrank F D.dual = Module.finrank K 𝕍 ∧
      Module.finrank K (𝕍 ⧸ D.orth D.Γ) + r = Module.finrank K 𝕍 := by
  exact HScattered.Delsarte.theorem_3_3 D h r n hr hn hU hdim hnh
