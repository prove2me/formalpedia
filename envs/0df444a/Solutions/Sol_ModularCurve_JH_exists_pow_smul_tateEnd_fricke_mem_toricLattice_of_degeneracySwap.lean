-- Prove2me | solution 1 for ModularCurve.JH.exists_pow_smul_tateEnd_fricke_mem_toricLattice_of_degeneracySwap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c5d3c612-809a-5f06-8072-087bea9f3214

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JH_exists_pow_smul_tateEnd_fricke_mem_toricLattice_of_degeneracySwap

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace WSTABRAT

section Core

variable {R : Type*} [CommRing R] {T T' : Type*} [AddCommGroup T] [Module R T]
  [AddCommGroup T'] [Module R T'] {ι : Type*}

theorem core (I : ι → Prop) (rep : ι → T →ₗ[R] T) (χ : ι → R) (q : R) (k : ℕ)
    (Tt Old : Submodule R T) (push₀ push₁ : T →ₗ[R] T') (W : T →ₗ[R] T) (W' : T' →ₗ[R] T')
    (hw3 : ∀ v, W (W v) = v) (hw3' : ∀ y, W' (W' y) = y)
    (hwI : ∀ τ, I τ → ∀ v, W (rep τ v) = rep τ (W v))
    (hTOR : ∀ τ, I τ → ∀ x ∈ Tt, rep τ x = χ τ • x)
    (hPUSH : ∀ x ∈ Tt, push₀ x = 0 ∧ push₁ x = 0)
    (hCUT : ∀ τ, I τ → ∀ v, q ^ k • (rep τ v - v) ∈ Tt ⊔ Old)
    (hOLD : ∀ o ∈ Old, push₀ o = 0 → push₁ o = 0 → o = 0)
    (hSWAP : ∀ x, push₁ (W x) = W' (push₀ x))
    (τ₀ : ι) (hτ₀ : I τ₀) (hCYC : χ τ₀ = 1 + q) :
    ∀ x ∈ Tt, q ^ (k + 1) • W x ∈ Tt := by
  intro x hx

  have hEig : rep τ₀ (W x) = χ τ₀ • W x := by
    rw [← hwI τ₀ hτ₀, hTOR τ₀ hτ₀ x hx, map_smul]

  have hP1 : push₁ (W x) = 0 := by
    rw [hSWAP, (hPUSH x hx).1, map_zero]
  have hP0 : push₀ (W x) = 0 := by
    have h := hSWAP (W x)
    rw [hw3, (hPUSH x hx).2] at h
    have h' : push₀ (W x) = W' (W' (push₀ (W x))) := (hw3' _).symm
    rw [← h, map_zero] at h'
    exact h'

  have hdiff : rep τ₀ (W x) - W x = q • W x := by
    rw [hEig, hCYC, add_smul, one_smul, add_sub_cancel_left]
  have hmem := hCUT τ₀ hτ₀ (W x)
  rw [hdiff] at hmem
  obtain ⟨t, ht, o, ho, hto⟩ := Submodule.mem_sup.1 hmem
  have ho0 : push₀ o = 0 := by
    have h := congrArg push₀ hto
    rw [map_add, (hPUSH t ht).1, zero_add, map_smul, map_smul, hP0, smul_zero, smul_zero] at h
    exact h
  have ho1 : push₁ o = 0 := by
    have h := congrArg push₁ hto
    rw [map_add, (hPUSH t ht).2, zero_add, map_smul, map_smul, hP1, smul_zero, smul_zero] at h
    exact h
  rw [hOLD o ho ho0 ho1, add_zero] at hto
  rw [pow_succ, mul_smul, ← hto]
  exact ht

end Core

section Lifts

variable (p M : ℕ) [Fact p.Prime] (H : Subgroup (ZMod M)ˣ)

theorem tateEnd_w_coe (w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H)
    (x : TateModule p (JH M H)) (n : ℕ) :
    ((JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)) x :
        TateModule p (JH M H)) : ℕ → JH M H) n =
      SemilinearAut.ofAlgAut w • (x : ℕ → JH M H) n := rfl

theorem tateGaloisRep_coe (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : TateModule p (JH M H)) (n : ℕ) :
    ((JH.tateGaloisRep M H p σ x : TateModule p (JH M H)) : ℕ → JH M H) n =
      σ • (x : ℕ → JH M H) n := rfl

theorem lift_w3 (w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H)
    (hw3 : ∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x)
    (v : TateModule p (JH M H)) :
    JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w))
      (JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)) v) = v := by
  refine Subtype.ext (funext fun n => ?_)
  simp only [tateEnd_w_coe]
  exact hw3 _

theorem lift_wI (w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : ∀ x : JH M H, SemilinearAut.ofAlgAut w • (σ • x) = σ • (SemilinearAut.ofAlgAut w • x))
    (v : TateModule p (JH M H)) :
    JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w))
        (JH.tateGaloisRep M H p σ v) =
      JH.tateGaloisRep M H p σ
        (JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)) v) := by
  refine Subtype.ext (funext fun n => ?_)
  simp only [tateEnd_w_coe, tateGaloisRep_coe]
  exact h _

end Lifts

end WSTABRAT

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Tt : Submodule ℤ_[p] (TateModule p (JH M H)))
    (push₀ push₁ : TateModule p (JH M H) →ₗ[ℤ_[p]] TateModule p (JH (M / p) (infSubgroup p M H hpM)))
    (pull₀ pull₁ : TateModule p (JH (M / p) (infSubgroup p M H hpM)) →ₗ[ℤ_[p]] TateModule p (JH M H))

    (w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H)
    (hw3 : ∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x)
    (hwI : ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x : JH M H,
      SemilinearAut.ofAlgAut w • (σ • x) = σ • (SemilinearAut.ofAlgAut w • x))
    (w' : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≃ₐ[AlgebraicClosure ℚ]
      xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
    (hw3' : ∀ y : JH (M / p) (infSubgroup p M H hpM), SemilinearAut.ofAlgAut w' • (SemilinearAut.ofAlgAut w' • y) = y)

    (hTOR : ∀ τ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x ∈ Tt,
      JH.tateGaloisRep M H p τ x = ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)

    (hPUSH : ∀ x ∈ Tt, push₀ x = 0 ∧ push₁ x = 0)

    (hCUT : ∃ k : ℕ, ∀ τ ∈ Pl.inertiaSubgroupIn ℚ, ∀ v : TateModule p (JH M H),
      (((p : ℕ) : ℤ_[p]) ^ k) • (JH.tateGaloisRep M H p τ v - v) ∈ Tt ⊔ (LinearMap.range pull₀ ⊔ LinearMap.range pull₁))

    (hOLD : ∀ o ∈ LinearMap.range pull₀ ⊔ LinearMap.range pull₁, push₀ o = 0 → push₁ o = 0 → o = 0)

    (hSWAP : ∀ x : TateModule p (JH M H),
      push₁ (JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)) x) =
        JH.tateEnd (M / p) (infSubgroup p M H hpM) p
          (DistribSMul.toAddMonoidHom (JH (M / p) (infSubgroup p M H hpM)) (SemilinearAut.ofAlgAut w')) (push₀ x))

    (hCYC : ∃ τ₀ ∈ Pl.inertiaSubgroupIn ℚ,
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ₀.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p])) :
    ∃ k : ℕ, ∀ x ∈ Tt,
      (((p : ℕ) : ℤ_[p]) ^ k) • JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)) x ∈ Tt := by
  obtain ⟨k, hk⟩ := hCUT
  obtain ⟨τ₀, hτ₀, hχ⟩ := hCYC
  exact ⟨k + 1, WSTABRAT.core (fun τ => τ ∈ Pl.inertiaSubgroupIn ℚ) (fun τ => JH.tateGaloisRep M H p τ)
    (fun τ => ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]))
    ((p : ℕ) : ℤ_[p]) k Tt (LinearMap.range pull₀ ⊔ LinearMap.range pull₁) push₀ push₁
    (JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)))
    (JH.tateEnd (M / p) (infSubgroup p M H hpM) p
      (DistribSMul.toAddMonoidHom (JH (M / p) (infSubgroup p M H hpM)) (SemilinearAut.ofAlgAut w')))
    (WSTABRAT.lift_w3 p M H w hw3) (WSTABRAT.lift_w3 p (M / p) (infSubgroup p M H hpM) w' hw3')
    (fun τ hτ v => WSTABRAT.lift_wI p M H w τ (hwI τ hτ) v)
    hTOR hPUSH hk hOLD hSWAP τ₀ hτ₀ hχ⟩

end S_ModularCurve_JH_exists_pow_smul_tateEnd_fricke_mem_toricLattice_of_degeneracySwap
end P2MW
export P2MW.S_ModularCurve_JH_exists_pow_smul_tateEnd_fricke_mem_toricLattice_of_degeneracySwap (solution)
