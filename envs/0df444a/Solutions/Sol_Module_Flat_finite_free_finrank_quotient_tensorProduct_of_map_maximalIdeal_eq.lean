-- Prove2me | solution 1 for Module.Flat.finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/dcf38d64-884d-56d7-a5b5-2f7b29346e90

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000

open IsLocalRing TensorProduct

theorem solution
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)]
    (m : ℕ) (hm : 0 < m) :
    Module.Finite (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧ Module.Free (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧
      Module.finrank (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) = Module.finrank (ResidueField V) (ResidueField D) := by
  classical
  have hItop : maximalIdeal V ^ m ≠ ⊤ := by
    intro h
    have : maximalIdeal V ^ m ≤ maximalIdeal V := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hm)
    rw [h, top_le_iff] at this
    exact (maximalIdeal.isMaximal V).ne_top this
  haveI : Nontrivial (V ⧸ maximalIdeal V ^ m) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (V ⧸ maximalIdeal V ^ m) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

  have hfinV : Module.Finite V ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := by

    set I : Ideal V := maximalIdeal V with hI

    haveI : Module.Finite V (ResidueField V) := Module.Finite.of_surjective (Algebra.linearMap V (ResidueField V))
      (by intro y; obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective y; exact ⟨v, rfl⟩)
    haveI : Module.Finite V (ResidueField D) := Module.Finite.trans (ResidueField V) (ResidueField D)
    have hID : (I • ⊤ : Submodule V D) = (maximalIdeal D).restrictScalars V := by
      rw [hI, Ideal.smul_top_eq_map, hVD]

    let ρ : D →ₗ[V] ResidueField D := (Algebra.linearMap D (ResidueField D)).restrictScalars V
    have hρsurj : Function.Surjective ρ := fun y => by obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y; exact ⟨d, rfl⟩
    have hρker : LinearMap.ker ρ = (I • ⊤ : Submodule V D) := by
      rw [hID]; ext d
      simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem]
      exact IsLocalRing.residue_eq_zero_iff d
    obtain ⟨S₀, hS₀fg, hS₀⟩ : ∃ S₀ : Submodule V D, S₀.FG ∧ S₀ ⊔ (I • ⊤ : Submodule V D) = ⊤ := by
      obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite V (ResidueField D))

      have hlift : ∀ y : ResidueField D, ∃ d : D, ρ d = y := hρsurj
      choose ℓ hℓ using hlift
      refine ⟨Submodule.span V (Finset.image ℓ t : Set D), ⟨_, rfl⟩, ?_⟩
      rw [eq_top_iff]
      intro d _
      have hd : ρ d ∈ Submodule.span V (t : Set (ResidueField D)) := by rw [ht]; exact Submodule.mem_top
      have : Submodule.span V (t : Set (ResidueField D)) = Submodule.map ρ (Submodule.span V (Finset.image ℓ t : Set D)) := by
        rw [Submodule.map_span]; congr 1; ext y; simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        constructor
        · intro hy; exact ⟨ℓ y, ⟨y, hy, rfl⟩, hℓ y⟩
        · rintro ⟨d', ⟨y', hy', rfl⟩, rfl⟩; rw [hℓ]; exact hy'
      rw [this, Submodule.mem_map] at hd
      obtain ⟨d₀, hd₀, hdd⟩ := hd
      have hdiff : d - d₀ ∈ (I • ⊤ : Submodule V D) := by rw [← hρker, LinearMap.mem_ker, map_sub, hdd, sub_self]
      have : d = d₀ + (d - d₀) := by abel
      rw [this]
      exact Submodule.add_mem_sup hd₀ hdiff

    have hSk : ∀ k : ℕ, S₀ ⊔ (I ^ k • ⊤ : Submodule V D) = ⊤ := by
      intro k
      induction k with
      | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact sup_top_eq _
      | succ k ih =>
        have h1 : (I ^ k • ⊤ : Submodule V D) ≤ S₀ ⊔ (I ^ (k + 1) • ⊤ : Submodule V D) := by
          conv_lhs => rw [← hS₀]
          rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
          exact sup_le_sup_right Submodule.smul_le_right _
        refine eq_top_iff.mpr ?_
        calc (⊤ : Submodule V D) = S₀ ⊔ (I ^ k • ⊤ : Submodule V D) := ih.symm
          _ ≤ S₀ ⊔ (I ^ (k + 1) • ⊤ : Submodule V D) := sup_le le_sup_left h1

    have hfq : Module.Finite V (D ⧸ (I ^ m • ⊤ : Submodule V D)) := by
      rw [Module.finite_def]
      have : (⊤ : Submodule V (D ⧸ (I ^ m • ⊤ : Submodule V D))) = Submodule.map (I ^ m • ⊤ : Submodule V D).mkQ S₀ := by
        have htop : Submodule.map (I ^ m • ⊤ : Submodule V D).mkQ ⊤ = ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]
        have h := congrArg (Submodule.map (I ^ m • ⊤ : Submodule V D).mkQ) (hSk m)
        rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, htop] at h
        exact h.symm
      rw [this]; exact hS₀fg.map _
    exact Module.Finite.equiv (TensorProduct.quotTensorEquivQuotSMul D (I ^ m)).symm
  haveI : Module.Finite (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := Module.Finite.of_restrictScalars_finite V (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)

  haveI : Module.Free (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := Module.free_of_flat_of_isLocalRing
  refine ⟨inferInstance, inferInstance, ?_⟩

  have hle : maximalIdeal V ^ m ≤ maximalIdeal V := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hm)
  letI algK : Algebra (V ⧸ maximalIdeal V ^ m) (ResidueField V) := (Ideal.Quotient.factor hle).toAlgebra
  haveI : IsScalarTower V (V ⧸ maximalIdeal V ^ m) (ResidueField V) := IsScalarTower.of_algebraMap_eq (fun v => rfl)

  have hb1 : Module.finrank (ResidueField V) ((ResidueField V) ⊗[(V ⧸ maximalIdeal V ^ m)] ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)) = Module.finrank (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]

  let e2 : ((ResidueField V) ⊗[(V ⧸ maximalIdeal V ^ m)] ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)) ≃ₗ[(ResidueField V)] ((ResidueField V) ⊗[V] D) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange V (V ⧸ maximalIdeal V ^ m) (ResidueField V) (ResidueField V) D

  let φ : ((ResidueField V) ⊗[V] D) →ₐ[(ResidueField V)] (ResidueField D) :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField V) (ResidueField D)) (IsScalarTower.toAlgHom V D (ResidueField D)) (fun x y => Commute.all _ _)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨(1 : (ResidueField V)) ⊗ₜ[V] d, ?_⟩
    show φ ((1 : (ResidueField V)) ⊗ₜ[V] d) = residue D d
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hker : (maximalIdeal D) ≤ RingHom.ker ((Algebra.TensorProduct.includeRight : D →ₐ[V] (ResidueField V) ⊗[V] D).toRingHom) := by
    rw [← hVD, Ideal.map_le_iff_le_comap]
    intro v hv
    show ((1 : (ResidueField V)) ⊗ₜ[V] (algebraMap V D v) : (ResidueField V) ⊗[V] D) = 0
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rw [show algebraMap V (ResidueField V) v = 0 from (IsLocalRing.residue_eq_zero_iff v).mpr hv, TensorProduct.zero_tmul]
  let ψ : (ResidueField D) →+* ((ResidueField V) ⊗[V] D) := Ideal.Quotient.lift (maximalIdeal D)
    ((Algebra.TensorProduct.includeRight : D →ₐ[V] (ResidueField V) ⊗[V] D).toRingHom) (fun a ha => hker ha)
  have hψφ : ∀ z, ψ (φ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul k d =>
      obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective k
      rw [Algebra.TensorProduct.lift_tmul]
      show ψ ((Algebra.ofId (ResidueField V) (ResidueField D)) (residue V v) * residue D d) = residue V v ⊗ₜ[V] d
      have h1 : (Algebra.ofId (ResidueField V) (ResidueField D)) (residue V v) * residue D d = residue D (algebraMap V D v * d) := by
        rw [map_mul]; congr 1
      rw [h1]
      show (Ideal.Quotient.lift (maximalIdeal D) _ _) (Ideal.Quotient.mk (maximalIdeal D) (algebraMap V D v * d)) = _
      rw [Ideal.Quotient.lift_mk]
      show ((1 : (ResidueField V)) ⊗ₜ[V] (algebraMap V D v * d) : (ResidueField V) ⊗[V] D) = residue V v ⊗ₜ[V] d
      rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl
  have hφinj : Function.Injective φ := fun a b h => by rw [← hψφ a, ← hψφ b, h]
  let e3 : ((ResidueField V) ⊗[V] D) ≃ₗ[(ResidueField V)] (ResidueField D) := LinearEquiv.ofBijective φ.toLinearMap ⟨hφinj, hφsurj⟩
  rw [← hb1, LinearEquiv.finrank_eq (e2.trans e3)]

end S_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq
end P2MW
export P2MW.S_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq (solution)
