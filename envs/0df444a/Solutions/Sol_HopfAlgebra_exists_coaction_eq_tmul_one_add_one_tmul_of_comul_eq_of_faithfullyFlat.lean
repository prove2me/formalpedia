-- Prove2me | solution 1 for HopfAlgebra.exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/06d7b786-572f-59e8-81f8-f64d6223fcd9

import Mathlib
import Theorems.Thm_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle
import Theorems.Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat

set_option autoImplicit false

open TensorProduct

universe u

namespace P2mPrimDescent

variable {K : Type u} [Field K] {R S H : Type u} [CommRing R] [CommRing S] [CommRing H]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S] [HopfAlgebra K H]

theorem smul_eq_tmul_one_mul (r : R) (y : S ⊗[K] H) : r • y = (algebraMap R S r ⊗ₜ[K] (1 : H)) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

noncomputable def shearEquiv (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) : (S ⊗[R] S) ≃ₗ[R] (S ⊗[K] H) :=
  LinearEquiv.ofBijective
    { toFun := σ
      map_add' := fun x y => map_add σ x y
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, map_mul, hσ_left,
          smul_eq_tmul_one_mul] } hσ

@[scoped simp] theorem shearEquiv_apply (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) (x : S ⊗[R] S) : shearEquiv σ hσ hσ_left x = σ x := rfl

noncomputable def doubleShear (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) (t : S ⊗[R] (S ⊗[R] S)) : S ⊗[K] (H ⊗[K] H) :=
  Algebra.TensorProduct.assoc K K K S H H
    (LinearEquiv.rTensor H ((shearEquiv σ hσ hσ_left).restrictScalars K)
      ((TensorProduct.AlgebraTensorModule.assoc K R R S S H).symm
        (TensorProduct.congr (LinearEquiv.refl R S) (shearEquiv σ hσ hσ_left) t)))

theorem doubleShear_injective (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) : Function.Injective (doubleShear σ hσ hσ_left) :=
  (Algebra.TensorProduct.assoc K K K S H H).injective.comp <|
    (LinearEquiv.rTensor H ((shearEquiv σ hσ hσ_left).restrictScalars K)).injective.comp <|
      (TensorProduct.AlgebraTensorModule.assoc K R R S S H).symm.injective.comp
        (TensorProduct.congr (LinearEquiv.refl R S) (shearEquiv σ hσ hσ_left)).injective

theorem doubleShear_add (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) (t t' : S ⊗[R] (S ⊗[R] S)) :
    doubleShear σ hσ hσ_left (t + t') = doubleShear σ hσ hσ_left t + doubleShear σ hσ hσ_left t' := by
  simp only [doubleShear, map_add]

theorem doubleShear_tmul (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) (a x : S) (y : H) (z : S ⊗[R] S)
    (hz : σ z = x ⊗ₜ[K] y) :
    doubleShear σ hσ hσ_left (a ⊗ₜ[R] z) =
      Algebra.TensorProduct.assoc K K K S H H (σ (a ⊗ₜ[R] x) ⊗ₜ[K] y) := by
  have h2 : (TensorProduct.AlgebraTensorModule.assoc K R R S S H).symm (a ⊗ₜ[R] (x ⊗ₜ[K] y)) = (a ⊗ₜ[R] x) ⊗ₜ[K] y := by
    rw [LinearEquiv.symm_apply_eq, TensorProduct.AlgebraTensorModule.assoc_tmul]
  simp only [doubleShear, TensorProduct.congr_tmul, LinearEquiv.refl_apply, shearEquiv_apply, hz, h2,
    LinearEquiv.rTensor_tmul, LinearEquiv.restrictScalars_apply]

end P2mPrimDescent
p2m_reactivate "P2MW.S_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat.P2mPrimDescent"

namespace P2mPrimDescent

variable {K : Type u} [Field K] {R S H : Type u} [CommRing R] [CommRing S] [CommRing H]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S] [HopfAlgebra K H]

theorem doubleShear_tmul' (ρ : S →ₐ[K] S ⊗[K] H) (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) (hσ_right : ∀ s : S, σ (1 ⊗ₜ[R] s) = ρ s)
    (a : S) (z : S ⊗[R] S) :
    doubleShear σ hσ hσ_left (a ⊗ₜ[R] z) =
      (a ⊗ₜ[K] ((1 : H) ⊗ₜ[K] (1 : H))) *
        Algebra.TensorProduct.assoc K K K S H H (Algebra.TensorProduct.map ρ (AlgHom.id K H) (σ z)) := by
  suffices hw : ∀ w : S ⊗[K] H, doubleShear σ hσ hσ_left (a ⊗ₜ[R] (shearEquiv σ hσ hσ_left).symm w) =
      (a ⊗ₜ[K] ((1 : H) ⊗ₜ[K] (1 : H))) *
        Algebra.TensorProduct.assoc K K K S H H (Algebra.TensorProduct.map ρ (AlgHom.id K H) w) by
    have := hw (σ z)
    rwa [show (shearEquiv σ hσ hσ_left).symm (σ z) = z from (shearEquiv σ hσ hσ_left).symm_apply_apply z] at this
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, mul_zero, doubleShear]
  | tmul x y =>
      rw [doubleShear_tmul σ hσ hσ_left a x y _ (by rw [← shearEquiv_apply σ hσ hσ_left, LinearEquiv.apply_symm_apply]),
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      have hax : σ (a ⊗ₜ[R] x) = (a ⊗ₜ[K] (1 : H)) * ρ x := by
        rw [← hσ_left, ← hσ_right, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hax, show ((a ⊗ₜ[K] (1 : H)) * ρ x) ⊗ₜ[K] y = ((a ⊗ₜ[K] (1 : H)) ⊗ₜ[K] (1 : H)) * (ρ x ⊗ₜ[K] y) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, Algebra.TensorProduct.assoc_tmul]
  | add w w' hw hw' => rw [map_add, TensorProduct.tmul_add, doubleShear_add, hw, hw', map_add, map_add, mul_add]

end P2mPrimDescent
p2m_reactivate "P2MW.S_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat.P2mPrimDescent"

open P2mPrimDescent in
theorem solution
    {K : Type u} [Field K] {R S H : Type u} [CommRing R] [CommRing S] [CommRing H]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S] [Module.FaithfullyFlat R S]
    [HopfAlgebra K H]
    (ρ : S →ₐ[K] S ⊗[K] H)
    (hρR : ∀ r : R, ρ (algebraMap R S r) = algebraMap R S r ⊗ₜ[K] (1 : H))
    (hcounit : ∀ s : S,
      (Algebra.TensorProduct.rid K K S) (Algebra.TensorProduct.map (AlgHom.id K S) (Bialgebra.counitAlgHom K H) (ρ s)) = s)
    (hcoassoc : ∀ s : S,
      (Algebra.TensorProduct.assoc K K K S H H) (Algebra.TensorProduct.map ρ (AlgHom.id K H) (ρ s)) =
        Algebra.TensorProduct.map (AlgHom.id K S) (Bialgebra.comulAlgHom K H) (ρ s))
    (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) (hσ_right : ∀ s : S, σ (1 ⊗ₜ[R] s) = ρ s)
    (h : H) (hh : Coalgebra.comul (R := K) h = h ⊗ₜ[K] 1 + 1 ⊗ₜ[K] h) :
    (∃ s : S, ρ s = s ⊗ₜ[K] 1 + (1 : S) ⊗ₜ[K] h) ∧
      (∀ s : S, ρ s = s ⊗ₜ[K] 1 → s ∈ Set.range (algebraMap R S)) := by
  classical
  refine ⟨?_, fun s hs => ?_⟩
  ·
    let c : S ⊗[R] S := (shearEquiv σ hσ hσ_left).symm ((1 : S) ⊗ₜ[K] h)
    have hσc : σ c = (1 : S) ⊗ₜ[K] h := by
      rw [← shearEquiv_apply σ hσ hσ_left, LinearEquiv.apply_symm_apply]

    have L12 : ∀ u : S ⊗[R] S, doubleShear σ hσ hσ_left (Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) u) =
        Algebra.TensorProduct.assoc K K K S H H (σ u ⊗ₜ[K] (1 : H)) := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.zero_tmul, doubleShear]
      | tmul a b =>
          rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply]
          exact doubleShear_tmul σ hσ hσ_left a b 1 _ (hσ_left b)
      | add u u' hu hu' => rw [map_add, doubleShear_add, hu, hu', map_add, TensorProduct.add_tmul, map_add]
    have L13 : ∀ u : S ⊗[R] S, doubleShear σ hσ hσ_left (Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) u) =
        Algebra.TensorProduct.map (AlgHom.id K S) (Bialgebra.comulAlgHom K H) (σ u) := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp only [map_zero, doubleShear]
      | tmul a b =>
          rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply]
          show doubleShear σ hσ hσ_left (a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] b)) = _
          rw [doubleShear_tmul' ρ σ hσ hσ_left hσ_right, hσ_right, hcoassoc b]
          have hab : σ (a ⊗ₜ[R] b) = (a ⊗ₜ[K] (1 : H)) * ρ b := by
            rw [← hσ_left, ← hσ_right, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [hab, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def]
      | add u u' hu hu' => rw [map_add, doubleShear_add, hu, hu', map_add, map_add]
    have L23 : ∀ u : S ⊗[R] S, doubleShear σ hσ hσ_left ((Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) u) =
        Algebra.TensorProduct.assoc K K K S H H (Algebra.TensorProduct.map ρ (AlgHom.id K H) (σ u)) := by
      intro u
      rw [Algebra.TensorProduct.includeRight_apply]
      show doubleShear σ hσ hσ_left ((1 : S) ⊗ₜ[R] u) = _
      rw [doubleShear_tmul' ρ σ hσ hσ_left hσ_right, ← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def,
        one_mul]

    have hc : Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c +
          (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c =
        Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c := by
      have e12 : Algebra.TensorProduct.assoc K K K S H H ((((1 : S) ⊗ₜ[K] h) ⊗ₜ[K] (1 : H))) =
          (1 : S) ⊗ₜ[K] (h ⊗ₜ[K] (1 : H)) := by rw [Algebra.TensorProduct.assoc_tmul]
      have e23 : Algebra.TensorProduct.assoc K K K S H H
          (Algebra.TensorProduct.map ρ (AlgHom.id K H) ((1 : S) ⊗ₜ[K] h)) = (1 : S) ⊗ₜ[K] ((1 : H) ⊗ₜ[K] h) := by
        rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, Algebra.TensorProduct.one_def,
          Algebra.TensorProduct.assoc_tmul]
      have e13 : Algebra.TensorProduct.map (AlgHom.id K S) (Bialgebra.comulAlgHom K H) ((1 : S) ⊗ₜ[K] h) =
          (1 : S) ⊗ₜ[K] (h ⊗ₜ[K] (1 : H) + (1 : H) ⊗ₜ[K] h) := by
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply, hh]
      apply doubleShear_injective σ hσ hσ_left
      rw [doubleShear_add, L12, L23, L13, hσc, e12, e23, e13, TensorProduct.tmul_add]
    obtain ⟨s, hsc⟩ := Module.FaithfullyFlat.exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle c hc
    refine ⟨-s, ?_⟩
    have hσs := congrArg σ hsc
    rw [hσc, map_sub, hσ_left, hσ_right] at hσs

    have hρs : ρ s = s ⊗ₜ[K] 1 - (1 : S) ⊗ₜ[K] h := by rw [hσs]; abel
    rw [map_neg, hρs, TensorProduct.neg_tmul]
    abel
  ·
    have h1 : σ ((1 : S) ⊗ₜ[R] s) = σ (s ⊗ₜ[R] (1 : S)) := by rw [hσ_right, hσ_left, hs]
    have h2 : s ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] s := (hσ.1 h1).symm
    obtain ⟨r, hr⟩ := Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul (A := R) h2
    exact ⟨r, hr⟩

end S_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat
end P2MW
export P2MW.S_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat (solution)
