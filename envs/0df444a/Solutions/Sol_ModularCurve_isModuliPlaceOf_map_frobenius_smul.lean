-- Prove2me | solution 1 for ModularCurve.isModuliPlaceOf_map_frobenius_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9bcad274-49a4-51ff-89eb-f401af654454

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open scoped Pointwise

universe u

namespace IsModuliPlaceOfFrobSmulSol

section Twist

def Tw {κ : Type u} [Field κ] (_τ : κ ≃+* κ) (Ω : Type u) : Type u := Ω

variable {κ : Type u} [Field κ] (τ : κ ≃+* κ) (Ω : Type u)

scoped instance [h : Field Ω] : Field (Tw τ Ω) := h
scoped instance [h : DecidableEq Ω] : DecidableEq (Tw τ Ω) := h
scoped instance [Field Ω] [Algebra κ Ω] : Algebra κ (Tw τ Ω) :=
  ((algebraMap κ Ω).comp τ.symm.toRingHom).toAlgebra

theorem algebraMap_tw [Field Ω] [Algebra κ Ω] (c : κ) :
    algebraMap κ (Tw τ Ω) c = (algebraMap κ Ω (τ.symm c) : Ω) := rfl

variable {Ω} in

def twPlace [Field Ω] [Algebra κ Ω] (V : Place κ Ω) : Place κ (Tw τ Ω) where
  toValuationSubring := (V.toValuationSubring : ValuationSubring Ω)
  algebraMap_mem' c := V.algebraMap_mem' (τ.symm c)
  ne_top' := V.ne_top'
  isPrincipalIdealRing' := V.isPrincipalIdealRing'

end Twist

section Datum

variable {κ : Type u} [Field κ] [DecidableEq κ] {N : ℕ} {x : ModuliPoint N κ}
  {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra κ Ω]
  (σ : SemilinearAut κ ↥(modularFunctionFieldFullC κ N))

def twEmb (D : ModuliTestDatum κ N x Ω) :
    modularFunctionFieldFullC κ N →ₐ[κ] Tw (SemilinearAut.baseAut σ) Ω where
  toFun f := (D.emb ((SemilinearAut.toRingAut σ).symm f) : Ω)
  map_one' := show D.emb ((SemilinearAut.toRingAut σ).symm 1) = (1 : Ω) by rw [map_one, map_one]
  map_mul' f g := show D.emb ((SemilinearAut.toRingAut σ).symm (f * g)) =
      (D.emb ((SemilinearAut.toRingAut σ).symm f) * D.emb ((SemilinearAut.toRingAut σ).symm g) : Ω) by
    rw [map_mul, map_mul]
  map_zero' := show D.emb ((SemilinearAut.toRingAut σ).symm 0) = (0 : Ω) by rw [map_zero, map_zero]
  map_add' f g := show D.emb ((SemilinearAut.toRingAut σ).symm (f + g)) =
      (D.emb ((SemilinearAut.toRingAut σ).symm f) + D.emb ((SemilinearAut.toRingAut σ).symm g) : Ω) by
    rw [map_add, map_add]
  commutes' c := by
    show D.emb ((SemilinearAut.toRingAut σ).symm (algebraMap κ _ c)) =
      (algebraMap κ Ω ((SemilinearAut.baseAut σ).symm c) : Ω)
    have h : (SemilinearAut.toRingAut σ).symm (algebraMap κ (modularFunctionFieldFullC κ N) c) =
        algebraMap κ (modularFunctionFieldFullC κ N) ((SemilinearAut.baseAut σ).symm c) :=
      SemilinearAut.commutes σ⁻¹ c
    rw [h, D.emb.commutes]

theorem twEmb_apply (D : ModuliTestDatum κ N x Ω) (f : modularFunctionFieldFullC κ N) :
    twEmb σ D f = (D.emb ((SemilinearAut.toRingAut σ).symm f) : Ω) := rfl

def twDatum (hfix : ∀ (d : ℕ) [NeZero d] (hd : d ∣ N), σ • jqNFull κ N d hd = jqNFull κ N d hd)
    (D : ModuliTestDatum κ N x Ω) (x' : ModuliPoint N κ)
    (hx' : ModuliPoint.map (SemilinearAut.baseAut σ : κ →+* κ) x = x') :
    ModuliTestDatum κ N x' (Tw (SemilinearAut.baseAut σ) Ω) where
  W := twPlace (SemilinearAut.baseAut σ) D.W
  curve := D.curve
  map_Δ_ne_zero := D.map_Δ_ne_zero
  gen := D.gen
  addOrderOf_gen := D.addOrderOf_gen
  res := (SemilinearAut.baseAut σ : κ →+* κ).comp D.res
  res_algebraMap c := by
    show SemilinearAut.baseAut σ (D.res _) = c
    have : (algebraMap κ (ResidueField (twPlace (SemilinearAut.baseAut σ) D.W).toValuationSubring) c) =
        algebraMap κ (ResidueField D.W.toValuationSubring) ((SemilinearAut.baseAut σ).symm c) := rfl
    rw [this, D.res_algebraMap]
    exact (SemilinearAut.baseAut σ).apply_symm_apply c
  reduction := by
    letI := Classical.decEq (ResidueField (twPlace (SemilinearAut.baseAut σ) D.W).toValuationSubring)
    obtain ⟨hord, hx⟩ := D.reduction
    refine ⟨hord, ?_⟩
    rw [ModuliPoint.map_comp]
    exact (congrArg (ModuliPoint.map (SemilinearAut.baseAut σ : κ →+* κ)) hx).trans hx'
  emb := twEmb σ D
  emb_jqNFull Ω' _ _ _ inst d _ hd := by
    have h1 : twEmb σ D (jqNFull κ N d hd) = (D.emb (jqNFull κ N d hd) : Ω) := by
      rw [twEmb_apply]
      congr 1
      rw [RingEquiv.symm_apply_eq]
      exact (hfix d hd).symm
    rw [h1]
    exact @ModuliTestDatum.emb_jqNFull κ _ _ N x Ω _ _ _ D Ω' _ _ _ inst d _ hd

theorem mem_twDatum_place_iff
    (hfix : ∀ (d : ℕ) [NeZero d] (hd : d ∣ N), σ • jqNFull κ N d hd = jqNFull κ N d hd)
    (D : ModuliTestDatum κ N x Ω) (x' : ModuliPoint N κ)
    (hx' : ModuliPoint.map (SemilinearAut.baseAut σ : κ →+* κ) x = x')
    (f : modularFunctionFieldFullC κ N) :
    f ∈ (twDatum σ hfix D x' hx').W.toValuationSubring.comap (twDatum σ hfix D x' hx').emb.toRingHom ↔
      (D.emb (σ⁻¹ • f) : Ω) ∈ D.W.toValuationSubring :=
  Iff.rfl

theorem isModuliPlaceOf_smul
    (hfix : ∀ (d : ℕ) [NeZero d] (hd : d ∣ N), σ • jqNFull κ N d hd = jqNFull κ N d hd)
    (x' : ModuliPoint N κ) (hx' : ModuliPoint.map (SemilinearAut.baseAut σ : κ →+* κ) x = x')
    {v : Place κ ↥(modularFunctionFieldFullC κ N)} (hv : IsModuliPlaceOf κ N x v) :
    IsModuliPlaceOf κ N x' (σ • v) := by
  obtain ⟨Ω, _, _, _, D, hD⟩ := hv
  refine ⟨Tw (SemilinearAut.baseAut σ) Ω, inferInstance, inferInstance, inferInstance,
    twDatum σ hfix D x' hx', ?_⟩
  refine SetLike.ext fun f => ?_
  rw [mem_twDatum_place_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hD, ValuationSubring.mem_comap]
  exact Iff.rfl

end Datum

section Coeff

variable {κ : Type u} [Field κ] (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (N : ℕ)
  (σ : SemilinearAut κ ↥(modularFunctionFieldFullC κ N))
  (hσ : ∀ x : ↥(modularFunctionFieldFullC κ N),
    ((σ • x : ↥(modularFunctionFieldFullC κ N)) : LaurentSeries κ) =
      coeffMap (frobenius κ q') (x : LaurentSeries κ))
include hσ

theorem baseAut_eq_frobenius : (SemilinearAut.baseAut σ : κ →+* κ) = frobenius κ q' := by
  refine RingHom.ext fun c => ?_
  apply (algebraMap κ (LaurentSeries κ)).injective
  have h1 := hσ (algebraMap κ (modularFunctionFieldFullC κ N) c)
  rw [SemilinearAut.smul_algebraMap] at h1
  have e1 : ∀ a : κ, ((algebraMap κ (modularFunctionFieldFullC κ N) a :
      modularFunctionFieldFullC κ N) : LaurentSeries κ) = algebraMap κ (LaurentSeries κ) a :=
    fun _ => rfl
  rw [e1, e1, coeffMap_algebraMap] at h1
  exact h1

theorem smul_jqNFull (d : ℕ) [NeZero d] (hd : d ∣ N) : σ • jqNFull κ N d hd = jqNFull κ N d hd :=
  Subtype.ext (by rw [hσ, coe_jqNFull, coeffSemilinearAut.coeffMap_jqNModC])

end Coeff

end IsModuliPlaceOfFrobSmulSol
p2m_reactivate "P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul.IsModuliPlaceOfFrobSmulSol"

end
p2m_reactivate "P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul.IsModuliPlaceOfFrobSmulSol"

open ModularCurve AlgebraicCurve IsModuliPlaceOfFrobSmulSol in
theorem solution {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (N : ℕ) [NeZero N]
    (σ : SemilinearAut κ ↥(modularFunctionFieldFullC κ N))
    (hσ : ∀ x : ↥(modularFunctionFieldFullC κ N),
      ((σ • x : ↥(modularFunctionFieldFullC κ N)) : LaurentSeries κ) = coeffMap (frobenius κ q') (x : LaurentSeries κ))
    (x : ModuliPoint N κ) (v : Place κ ↥(modularFunctionFieldFullC κ N))
    (hv : IsModuliPlaceOf κ N x v) :
    IsModuliPlaceOf κ N (ModuliPoint.map (frobenius κ q') x) (σ • v) :=
  isModuliPlaceOf_smul σ (fun d _ hd => smul_jqNFull q' N σ hσ d hd) _
    (by rw [baseAut_eq_frobenius q' N σ hσ]) hv

end S_ModularCurve_isModuliPlaceOf_map_frobenius_smul
end P2MW
export P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul (solution)
