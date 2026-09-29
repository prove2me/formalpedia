-- Prove2me | solution 1 for MvFormalGroup.exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/18e4000d-4d5e-532f-a1bf-ee26eb073905

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace Tangent

variable {R : Type u} [CommRing R] {d : ℕ}

private theorem antidiagonal_one_eq :
    Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (0 : ℕ))} := by
  ext ⟨a, b⟩
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

private theorem sum_antidiagonal_single_one {M : Type*} [AddCommMonoid M] (j : Fin d)
    (G : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) → M) :
    ∑ y ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.single j 1), G y =
      G (0, Finsupp.single j 1) + G (Finsupp.single j 1, 0) := by
  classical
  rw [Finsupp.antidiagonal_single, Finset.sum_map, antidiagonal_one_eq,
    Finset.sum_pair (by simp)]
  simp

private theorem coeff_single_mul (j : Fin d) (G G' : MvPowerSeries (Fin d) R) :
    coeff (Finsupp.single j 1) (G * G') =
      constantCoeff G * coeff (Finsupp.single j 1) G' +
        coeff (Finsupp.single j 1) G * constantCoeff G' := by
  classical
  rw [coeff_mul, sum_antidiagonal_single_one]
  simp only [coeff_zero_eq_constantCoeff]

private theorem coeff_single_mem_of_mem_span_nthSeries (F : MvFormalGroup d R) (n : ℕ)
    {G : MvPowerSeries (Fin d) R} (hG : G ∈ Ideal.span (Set.range (F.nthSeries n))) (i : Fin d) :
    coeff (Finsupp.single i 1) G ∈ Ideal.span {(n : R)} := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hG
  rw [map_sum]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [smul_eq_mul, coeff_single_mul, ← coeff_zero_eq_constantCoeff_apply (F.nthSeries n k),
    coeff_zero_eq_constantCoeff_apply, MvFormalGroup.constantCoeff_nthSeries F n k, mul_zero, add_zero]
  have hlin : coeff (Finsupp.single i 1) (F.nthSeries n k) = if k = i then (n : R) else 0 := by
    have := congrFun (congrFun (MvFormalGroup.linearPart_nthSeries F n) k) i
    rw [MvFormalGroup.linearPart, Matrix.of_apply] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_ite, nsmul_eq_mul, mul_one, smul_zero]
  rw [hlin]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [mul_zero]; exact Ideal.zero_mem _

private noncomputable def cc0 (𝓞 : Type*) [CommRing 𝓞] (d : ℕ) : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 :=
  { (constantCoeff : MvPowerSeries (Fin d) 𝓞 →+* 𝓞) with
    commutes' := fun r => by
      show constantCoeff (algebraMap 𝓞 (MvPowerSeries (Fin d) 𝓞) r) = r
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C] }

private theorem cc0_apply {𝓞 : Type*} [CommRing 𝓞] (G : MvPowerSeries (Fin d) 𝓞) :
    cc0 𝓞 d G = constantCoeff G := rfl

end Tangent

open Tangent in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (v : ℕ) (hv : 0 < v)
    (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    :
    ∃ D : Fin d → CartierDual (ZMod p) (ZMod p ⊗[𝓞] R),
      (∀ i j, D i ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = if i = j then 1 else 0) ∧
      (∀ i (a b : ZMod p ⊗[𝓞] R), D i (a * b) =
        D i a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D i b) := by
  classical

  have _hp := hp
  have _hπeval := hπeval

  haveI : IsAdicComplete (Ideal.span {(p : R)}) R :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p R
  haveI : IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R ⊗[𝓞] R)
  have hε : ∀ j, Coalgebra.counit (R := 𝓞) (π (X j)) = 0 :=
    MvFormalGroup.counit_apply_eq_zero_of_comul_eq_adicEval p F R (fun j => π (X j)) hπX hπΔ

  have hεπ : ∀ G : MvPowerSeries (Fin d) 𝓞, Coalgebra.counit (R := 𝓞) (π G) = constantCoeff G := by
    intro G
    let χ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 := (Bialgebra.counitAlgHom 𝓞 R).comp π
    have hχ : ∀ s, χ (X s) ∈ (Ideal.span {(p : 𝓞)}).radical := fun s => by
      show Coalgebra.counit (R := 𝓞) (π (X s)) ∈ _
      rw [hε]; exact Ideal.zero_mem _
    have hχ' : ∀ s, Tangent.cc0 𝓞 d (X s) ∈ (Ideal.span {(p : 𝓞)}).radical := fun s => by
      rw [Tangent.cc0_apply, constantCoeff_X]; exact Ideal.zero_mem _
    have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
      (Ideal.span {(p : 𝓞)}) χ hχ G
    have h2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
      (Ideal.span {(p : 𝓞)}) (Tangent.cc0 𝓞 d) hχ' G
    have e1 : (fun s => χ (X s)) = fun _ => (0 : 𝓞) := funext fun s => hε s
    have e2 : (fun s => Tangent.cc0 𝓞 d (X s)) = fun _ => (0 : 𝓞) :=
      funext fun s => by rw [Tangent.cc0_apply, constantCoeff_X]
    rw [e1] at h1
    rw [e2, Tangent.cc0_apply] at h2
    exact h1.trans h2.symm

  let lam : Fin d → MvPowerSeries (Fin d) 𝓞 →ₗ[𝓞] ZMod p := fun i =>
    (Algebra.linearMap 𝓞 (ZMod p)).comp (coeff (Finsupp.single i 1))
  have hlam : ∀ i G, lam i G = algebraMap 𝓞 (ZMod p) (coeff (Finsupp.single i 1) G) := fun i G => rfl
  have hlam_eq : ∀ i (G G' : MvPowerSeries (Fin d) 𝓞), π G = π G' → lam i G = lam i G' := by
    intro i G G' hGG'
    rw [← sub_eq_zero, ← map_sub, hlam, ← RingHom.mem_ker, hker]
    have hmem : G - G' ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, hGG', sub_self]
    rw [hkerπ] at hmem
    have h := Tangent.coeff_single_mem_of_mem_span_nthSeries F (p ^ v) hmem i
    refine Ideal.span_singleton_le_span_singleton.mpr ?_ h
    rw [Nat.cast_pow]
    exact dvd_pow_self _ hv.ne'

  let μ : Fin d → R →ₗ[𝓞] ZMod p := fun i =>
    { toFun := fun r => lam i (Function.surjInv hπ r)
      map_add' := fun r s => by
        rw [← map_add]
        apply hlam_eq
        rw [map_add, Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ]
      map_smul' := fun c r => by
        rw [RingHom.id_apply, ← map_smul]
        apply hlam_eq
        rw [map_smul, Function.surjInv_eq hπ, Function.surjInv_eq hπ] }
  have hμ : ∀ i G, μ i (π G) = lam i G := fun i G =>
    hlam_eq i _ _ (Function.surjInv_eq hπ (π G))

  let del : Fin d → ZMod p ⊗[𝓞] R →ₗ[ZMod p] ZMod p := fun i =>
    (Algebra.TensorProduct.lmul'' 𝓞 (S := ZMod p)).toLinearMap ∘ₗ (μ i).baseChange (ZMod p)
  have hdel : ∀ i (c : ZMod p) (G : MvPowerSeries (Fin d) 𝓞),
      del i (c ⊗ₜ[𝓞] π G) = c * algebraMap 𝓞 (ZMod p) (coeff (Finsupp.single i 1) G) := by
    intro i c G
    show Algebra.TensorProduct.lmul'' 𝓞 (S := ZMod p) ((μ i).baseChange (ZMod p) (c ⊗ₜ[𝓞] π G)) = _
    rw [LinearMap.baseChange_tmul]
    show Algebra.TensorProduct.lmul' 𝓞 (S := ZMod p) (c ⊗ₜ[𝓞] (μ i) (π G)) = _
    rw [Algebra.TensorProduct.lmul'_apply_tmul, hμ]
    rfl
  refine ⟨fun i => CartierDual.ofDual (ZMod p) (ZMod p ⊗[𝓞] R) (del i), ?_, ?_⟩
  · intro i j
    rw [CartierDual.ofDual_apply, hdel, coeff_index_single_X, one_mul]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg hij, map_zero]
  · intro i a b
    simp only [CartierDual.ofDual_apply]

    have hcounit : ∀ (c : ZMod p) (G : MvPowerSeries (Fin d) 𝓞),
        Coalgebra.counit (R := ZMod p) (c ⊗ₜ[𝓞] π G) = algebraMap 𝓞 (ZMod p) (constantCoeff G) * c := by
      intro c G
      rw [TensorProduct.counit_tmul, hεπ, Algebra.smul_def]
      rfl
    induction a using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, zero_add]
    | add x y hx hy =>
      rw [add_mul, map_add, hx, hy, map_add, map_add]
      ring
    | tmul c r =>
      induction b using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, add_zero]
      | add x y hx hy =>
        rw [mul_add, map_add, hx, hy, map_add, map_add]
        ring
      | tmul c' r' =>
        obtain ⟨G, rfl⟩ := hπ r
        obtain ⟨G', rfl⟩ := hπ r'
        rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, hdel, hdel, hdel, hcounit, hcounit,
          Tangent.coeff_single_mul, map_add, map_mul, map_mul]
        ring

end S_MvFormalGroup_exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries
end P2MW
export P2MW.S_MvFormalGroup_exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries (solution)
