-- Prove2me | solution 1 for MvFormalGroup.counit_apply_eq_zero_of_comul_eq_adicEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b7a56352-741c-50bf-b62c-8ed47ae6cda9

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map toPowerSeries adicEval map_adicEval Points Points.val_add"
namespace EPS0
p2m_open "MvFormalGroup"

open scoped TensorProduct
open MvPowerSeries

variable {𝓞 : Type*} [CommRing 𝓞] {R : Type*} [CommRing R] [Bialgebra 𝓞 R]

private noncomputable def ψ : R ⊗[𝓞] R →ₐ[𝓞] R :=
  (Algebra.TensorProduct.lid 𝓞 R).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom 𝓞 R) (AlgHom.id 𝓞 R))

private theorem ψ_tmul (a b : R) : ψ (a ⊗ₜ[𝓞] b) = Coalgebra.counit (R := 𝓞) a • b := by
  simp [ψ]

private theorem ψ_comul (r : R) : ψ (Coalgebra.comul (R := 𝓞) r) = r := by
  have h : ∀ t : R ⊗[𝓞] R, ψ t =
      Algebra.TensorProduct.lid 𝓞 R ((Coalgebra.counit (R := 𝓞) (A := R)).rTensor R t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [ψ_tmul, LinearMap.rTensor_tmul, Algebra.TensorProduct.lid_tmul]
    | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]
  rw [h, Coalgebra.rTensor_counit_comul, Algebra.TensorProduct.lid_tmul, one_smul]

private theorem map_span_natCast_le_radical {A B : Type*} [CommRing A] [CommRing B] [Algebra 𝓞 A]
    [Algebra 𝓞 B] (φ : A →ₐ[𝓞] B) (p : ℕ) :
    ∀ s ∈ Ideal.span {(p : A)}, φ s ∈ (Ideal.span {(p : B)}).radical := by
  intro s hs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine Ideal.le_radical ?_
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem map_mem_radical_span_natCast {A B : Type*} [CommRing A] [CommRing B] [Algebra 𝓞 A]
    [Algebra 𝓞 B] (φ : A →ₐ[𝓞] B) (p : ℕ) {s : A} (hs : s ∈ (Ideal.span {(p : A)}).radical) :
    φ s ∈ (Ideal.span {(p : B)}).radical := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hk
  refine ⟨k, ?_⟩
  rw [← map_pow, ← ht, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end MvFormalGroup.EPS0

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞)
    (R : Type v) [CommRing R] [Bialgebra 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (x : Fin d → R) (hx : ∀ i, x i ∈ (Ideal.span {(p : R)}).radical)
    (hΔ : ∀ i, Coalgebra.comul (R := 𝓞) (x i) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] x j))
        (F.toPowerSeries i)) :
    ∀ i, Coalgebra.counit (R := 𝓞) (x i) = 0 := by
  classical
  intro i₀

  let ε : R →ₐ[𝓞] 𝓞 := Bialgebra.counitAlgHom 𝓞 R
  have hε : ∀ r, ε r = Coalgebra.counit (R := 𝓞) r := fun r => rfl
  let J₂ : Ideal (R ⊗[𝓞] R) := Ideal.span {(p : R ⊗[𝓞] R)}
  let J₁ : Ideal R := Ideal.span {(p : R)}
  let J₀ : Ideal 𝓞 := Ideal.span {(p : 𝓞)}

  have hx₂ : ∀ s, Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] x j) s ∈ J₂.radical := by
    rintro (j | j)
    · have h := MvFormalGroup.EPS0.map_mem_radical_span_natCast
        (Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R) p (hx j)
      rwa [Algebra.TensorProduct.includeLeft_apply] at h
    · have h := MvFormalGroup.EPS0.map_mem_radical_span_natCast
        (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R) p (hx j)
      rwa [Algebra.TensorProduct.includeRight_apply] at h

  let c : Fin d → 𝓞 := fun j => ε (x j)
  have hc : ∀ j, c j ∈ J₀.radical := fun j =>
    MvFormalGroup.EPS0.map_mem_radical_span_natCast ε p (hx j)
  have step1 : ∀ i, x i = MvFormalGroup.adicEval J₁
      (Sum.elim (fun j => algebraMap 𝓞 R (c j)) x) (F.toPowerSeries i) := by
    intro i
    have h := congrArg MvFormalGroup.EPS0.ψ (hΔ i)
    rw [MvFormalGroup.EPS0.ψ_comul,
      MvFormalGroup.map_adicEval J₂ J₁ MvFormalGroup.EPS0.ψ ⟨{(p : R ⊗[𝓞] R)}, by simp [J₂]⟩
        (MvFormalGroup.EPS0.map_span_natCast_le_radical _ p) hx₂] at h
    convert h using 2
    funext s
    rcases s with j | j
    · simp only [Sum.elim_inl]
      rw [MvFormalGroup.EPS0.ψ_tmul, Algebra.smul_def, mul_one]
      rfl
    · simp only [Sum.elim_inr]
      rw [MvFormalGroup.EPS0.ψ_tmul, Bialgebra.counit_one, one_smul]

  have hx₁ : ∀ s, Sum.elim (fun j => algebraMap 𝓞 R (c j)) x s ∈ J₁.radical := by
    rintro (j | j)
    · exact MvFormalGroup.EPS0.map_mem_radical_span_natCast (Algebra.ofId 𝓞 R) p (hc j)
    · exact hx j
  have step2 : ∀ i, c i = MvFormalGroup.adicEval J₀ (Sum.elim c c) (F.toPowerSeries i) := by
    intro i
    have h := congrArg ε (step1 i)
    rw [MvFormalGroup.map_adicEval J₁ J₀ ε ⟨{(p : R)}, by simp [J₁]⟩
        (MvFormalGroup.EPS0.map_span_natCast_le_radical _ p) hx₁] at h
    convert h using 2
    funext s
    rcases s with j | j
    · simp only [Sum.elim_inl]
      rw [AlgHom.commutes]
      rfl
    · rfl

  let P : MvFormalGroup.Points F 𝓞 J₀ := ⟨c, hc⟩
  have hP : P = P + P := by
    ext i
    rw [MvFormalGroup.Points.val_add]
    exact step2 i
  have hP0 : P = 0 := add_left_cancel (a := P) (by rw [add_zero]; exact hP.symm)
  have : c i₀ = 0 := by
    have h := congrArg (fun Q : MvFormalGroup.Points F 𝓞 J₀ => Q.val i₀) hP0
    exact h
  exact this

end S_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval
end P2MW
export P2MW.S_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval (solution)
