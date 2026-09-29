-- Prove2me | solution 1 for Module.free_coker_and_ker_baseChange_of_ker_le_range_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d7d8b441-33a9-5d75-bf16-49bb4be0937e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField

set_option autoImplicit false

universe u v

open TensorProduct

namespace BC0Free

variable {R : Type u} [CommRing R]

section Split

variable {K M B : Type v} [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M]
  [AddCommGroup B] [Module R B]

theorem lTensor_split (i : K →ₗ[R] M) (r : M →ₗ[R] K) (p : M →ₗ[R] B) (s : B →ₗ[R] M)
    (hri : r ∘ₗ i = LinearMap.id) (hps : p ∘ₗ s = LinearMap.id) (hpi : p ∘ₗ i = 0)
    (hsum : i ∘ₗ r + s ∘ₗ p = LinearMap.id)
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (i.lTensor A) ∧ LinearMap.range (i.lTensor A) = LinearMap.ker (p.lTensor A) := by
  have hri' : (r.lTensor A) ∘ₗ (i.lTensor A) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hri, LinearMap.lTensor_id]
  have hpi' : (p.lTensor A) ∘ₗ (i.lTensor A) = 0 := by
    rw [← LinearMap.lTensor_comp, hpi, LinearMap.lTensor_zero]
  have hsum' : (i.lTensor A) ∘ₗ (r.lTensor A) + (s.lTensor A) ∘ₗ (p.lTensor A) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_add, hsum, LinearMap.lTensor_id]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg (r.lTensor A) hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hri', LinearMap.id_apply, LinearMap.id_apply] at this
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hpi', LinearMap.zero_apply]
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      refine ⟨r.lTensor A x, ?_⟩
      have h := LinearMap.congr_fun hsum' x
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hx, map_zero, add_zero,
        LinearMap.id_apply] at h
      exact h

end Split

section Main

variable [IsLocalRing R]
  {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup C2] [Module R C2] [Module.Finite R C1] [Module.Free R C1] [Module.Finite R C2] [Module.Free R C2]

local notation "κ" => IsLocalRing.ResidueField R

noncomputable def dbar (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0) :
    (C1 ⧸ LinearMap.range d0) →ₗ[R] C2 :=
  (LinearMap.range d0).liftQ d1 (by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply])

theorem dbar_comp_mkQ (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0) :
    dbar d0 d1 hdd ∘ₗ (LinearMap.range d0).mkQ = d1 :=
  (LinearMap.range d0).liftQ_mkQ _ _

theorem lTensor_dbar_injective (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hH1 : LinearMap.ker (d1.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range (d0.baseChange (IsLocalRing.ResidueField R))) :
    Function.Injective ((dbar d0 d1 hdd).lTensor κ) := by

  have hex : Function.Exact (d0.lTensor κ) ((LinearMap.range d0).mkQ.lTensor κ) :=
    lTensor_exact κ (LinearMap.exact_map_mkQ_range d0) (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective ((LinearMap.range d0).mkQ.lTensor κ) :=
    LinearMap.lTensor_surjective κ (Submodule.mkQ_surjective _)
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, dbar_comp_mkQ] at hx

  have hy : y ∈ LinearMap.ker (d1.baseChange κ) := by
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor]; exact hx
  have hy' := hH1 hy
  obtain ⟨z, hz⟩ := hy'
  rw [Submodule.mem_bot]
  have : y ∈ LinearMap.range (d0.lTensor κ) := ⟨z, by rw [← hz, LinearMap.baseChange_eq_ltensor]⟩
  rw [← LinearMap.mem_ker]
  exact (hex y).mpr this |> fun h => by rw [LinearMap.mem_ker]; exact h

theorem free_coker (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hH1 : LinearMap.ker (d1.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range (d0.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (C1 ⧸ LinearMap.range d0) := by
  haveI : Module.Finite R (C1 ⧸ LinearMap.range d0) := Module.Finite.quotient R _
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective (dbar d0 d1 hdd)).mpr
    (lTensor_dbar_injective d0 d1 hdd hH1)
  haveI : Module.Projective R (C1 ⧸ LinearMap.range d0) := Module.Projective.of_split _ _ hl'
  haveI : Module.Flat R (C1 ⧸ LinearMap.range d0) := Module.Flat.of_projective
  exact Module.free_of_flat_of_isLocalRing

theorem ker_baseChange (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hH1 : LinearMap.ker (d1.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range (d0.baseChange (IsLocalRing.ResidueField R)))
    (A : Type u) [CommRing A] [Algebra R A] :
    LinearMap.range ((LinearMap.ker d0).subtype.baseChange A) = LinearMap.ker (d0.baseChange A) ∧
      Function.Injective ((LinearMap.ker d0).subtype.baseChange A) := by
  haveI := free_coker d0 d1 hdd hH1

  obtain ⟨sQ, hsQ⟩ := Module.projective_lifting_property (LinearMap.range d0).mkQ
    (LinearMap.id : (C1 ⧸ LinearMap.range d0) →ₗ[R] _) (Submodule.mkQ_surjective _)

  let B := LinearMap.range d0
  have hmemB : ∀ c : C1, c - sQ (B.mkQ c) ∈ B := by
    intro c
    have h0 : B.mkQ (c - sQ (B.mkQ c)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hsQ, LinearMap.id_apply, sub_self]
    rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h0
  let rB : C1 →ₗ[R] B :=
    { toFun := fun c => ⟨c - sQ (B.mkQ c), hmemB c⟩
      map_add' := fun x y => by ext; simp only [map_add, Submodule.coe_add]; abel
      map_smul' := fun a x => by ext; simp only [map_smul, RingHom.id_apply, Submodule.coe_smul, smul_sub] }
  have hrB : rB ∘ₗ B.subtype = LinearMap.id := by
    ext ⟨b, hb⟩
    simp only [rB, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.id_apply]
    rw [(Submodule.Quotient.mk_eq_zero B).mpr hb |> fun h => show sQ (B.mkQ b) = 0 by
      rw [Submodule.mkQ_apply, h, map_zero], sub_zero]
  haveI : Module.Projective R B := Module.Projective.of_split B.subtype rB hrB

  obtain ⟨sB, hsB⟩ := Module.projective_lifting_property d0.rangeRestrict (LinearMap.id : B →ₗ[R] B)
    d0.surjective_rangeRestrict

  let K := LinearMap.ker d0
  have hmemK : ∀ c : C0, c - sB (d0.rangeRestrict c) ∈ K := by
    intro c
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    have := congrArg Subtype.val (LinearMap.congr_fun hsB (d0.rangeRestrict c))
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at this
    exact this.symm
  let rK : C0 →ₗ[R] K :=
    { toFun := fun c => ⟨c - sB (d0.rangeRestrict c), hmemK c⟩
      map_add' := fun x y => by ext; simp only [map_add, Submodule.coe_add]; abel
      map_smul' := fun a x => by ext; simp only [map_smul, RingHom.id_apply, Submodule.coe_smul, smul_sub] }
  have hrK : rK ∘ₗ K.subtype = LinearMap.id := by
    ext ⟨k, hk⟩
    simp only [rK, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.id_apply]
    have : d0.rangeRestrict k = 0 := Subtype.ext (by simp at hk ⊢; exact hk)
    rw [this, map_zero, sub_zero]
  have hps : d0.rangeRestrict ∘ₗ sB = LinearMap.id := hsB
  have hpi : d0.rangeRestrict ∘ₗ K.subtype = 0 := by
    ext ⟨k, hk⟩
    exact (LinearMap.mem_ker.mp hk)
  have hsum : K.subtype ∘ₗ rK + sB ∘ₗ d0.rangeRestrict = LinearMap.id := by
    ext c
    simp only [rK, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.id_apply, sub_add_cancel]
  obtain ⟨hinj, hrange⟩ := lTensor_split K.subtype rK d0.rangeRestrict sB hrK hps hpi hsum A

  obtain ⟨hinjB, -⟩ := lTensor_split B.subtype rB B.mkQ sQ hrB hsQ
    (by ext b; exact (Submodule.Quotient.mk_eq_zero B).mpr b.2)
    (by ext c; simp only [rB, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.id_apply, sub_add_cancel]) A
  refine ⟨?_, ?_⟩
  ·
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    have hx : x ∈ LinearMap.range (K.subtype.lTensor A) ↔ x ∈ LinearMap.ker (d0.rangeRestrict.lTensor A) := by
      rw [hrange]
    rw [LinearMap.mem_range, LinearMap.mem_ker] at hx
    rw [hx]

    have hd0 : d0.lTensor A = (B.subtype.lTensor A) ∘ₗ (d0.rangeRestrict.lTensor A) := by
      rw [← LinearMap.lTensor_comp]; rfl
    rw [hd0, LinearMap.comp_apply]
    constructor
    · intro h; rw [h, map_zero]
    · intro h; exact hinjB (by rw [h, map_zero])
  · intro x y hxy
    apply hinj
    have := hxy
    rwa [LinearMap.baseChange_eq_ltensor] at this

end Main

end BC0Free

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2] [Module.Finite R C1] [Module.Free R C1] [Module.Finite R C2] [Module.Free R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hH1 : LinearMap.ker (d1.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range (d0.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (C1 ⧸ LinearMap.range d0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        LinearMap.range ((LinearMap.ker d0).subtype.baseChange A) = LinearMap.ker (d0.baseChange A) ∧
          Function.Injective ((LinearMap.ker d0).subtype.baseChange A) :=
  ⟨BC0Free.free_coker d0 d1 hdd hH1, fun A _ _ => BC0Free.ker_baseChange d0 d1 hdd hH1 A⟩

end S_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField
end P2MW
export P2MW.S_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField (solution)
