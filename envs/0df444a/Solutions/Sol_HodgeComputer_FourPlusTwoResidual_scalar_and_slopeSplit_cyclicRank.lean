-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.scalar_and_slopeSplit_cyclicRank
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:48.519433+00:00
-- url     : https://prove2.me/submissions/a636f488-3fee-44ff-8145-74bb46f43323

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
noncomputable section

namespace FP5CyclicSlope

lemma aeval_mem_cyclicSpan {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (Q : Polynomial K) :
    (Polynomial.aeval T Q) v ∈ Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) v) := by
  let S := Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) v)
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, LinearMap.smul_apply]
    exact S.smul_mem c (Submodule.subset_span ⟨n, rfl⟩)

lemma pow_mem_cyclicSpan_of_mem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v x : V)
    (hx : x ∈ Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) v)) :
    ∀ m : ℕ, (T ^ m) x ∈ Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) v) := by
  let S := Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) v)
  have hT : ∀ y ∈ S, T y ∈ S := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨n, rfl⟩
      have hsucc : T ((T ^ n) v) = (T ^ (n + 1)) v := by
        rw [← Module.End.mul_apply, ← pow_succ']
      rw [hsucc]
      exact Submodule.subset_span ⟨n + 1, rfl⟩
    · simp
    · intro a b _ _ ha hb; rw [map_add]; exact S.add_mem ha hb
    · intro c a _ ha; rw [map_smul]; exact S.smul_mem c ha
  intro m
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    have hsucc : (T ^ (m + 1)) x = T ((T ^ m) x) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hsucc]
    exact hT _ ih

end FP5CyclicSlope

theorem solution :
    (∀ {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
      (exponent : ι → ℕ) (C D Y : Module.End K V) (c : K) (v : V),
      LinearMap.ker (C - c • 1) = Submodule.span K {v} →
      Submodule.span K (Set.range fun i ↦ (D ^ exponent i) v) = ⊤ →
      Commute C Y → Commute Y D →
      ∃ a : K, Y = a • (1 : Module.End K V)) ∧
    (∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V]
      (T : Module.End K V) (W₀ W₁ : Submodule K V)
      (P₀ P₁ : Polynomial K) (a₀ a₁ : V),
      W₀ ⊔ W₁ = ⊤ →
      W₀ ≤ Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) a₀) →
      W₁ ≤ Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) a₁) →
      (Polynomial.aeval T P₀) a₀ = 0 →
      (Polynomial.aeval T P₁) a₁ = 0 →
      IsCoprime P₀ P₁ →
      Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) (a₀ + a₁)) = ⊤) := by
  refine ⟨?_, ?_⟩
  · intro K V ι _ _ _ exponent C D Y c v hline hspan hC hD
    have line : C.eigenspace c = Submodule.span K {v} := Module.End.eigenspace_def.trans hline
    exact
      let hv := line.ge (Submodule.mem_span_singleton_self v)
      let hy := Module.End.mapsTo_genEigenspace_of_comm hC c 1 hv
      (Submodule.mem_span_singleton.mp (line.le hy)).elim fun a ha ↦
        ⟨a, LinearMap.ext_on_range hspan fun i ↦
          calc
            Y ((D ^ exponent i) v) = (D ^ exponent i) (Y v) :=
              LinearMap.congr_fun (hD.pow_right _).eq v
            _ = a • (D ^ exponent i) v :=
              (congrArg (D ^ exponent i) ha.symm).trans ((D ^ exponent i).map_smul a v)⟩
  · intro K V _ _ _ T W₀ W₁ P₀ P₁ a₀ a₁ hW hspan₀ hspan₁ hP₀ hP₁ hcop
    let S := Submodule.span K (Set.range fun n : ℕ ↦ (T ^ n) (a₀ + a₁))
    obtain ⟨U₀, U₁, hU⟩ := hcop
    have hproj_mem : (Polynomial.aeval T (U₁ * P₁)) (a₀ + a₁) ∈ S :=
      FP5CyclicSlope.aeval_mem_cyclicSpan T (a₀ + a₁) (U₁ * P₁)
    have hkill₁ : (Polynomial.aeval T (U₁ * P₁)) a₁ = 0 := by
      rw [map_mul, Module.End.mul_apply, hP₁, map_zero]
    have hfix₀ : (Polynomial.aeval T (U₁ * P₁)) a₀ = a₀ := by
      have h1 := congrArg (fun Q => (Polynomial.aeval T Q) a₀) hU
      rw [map_add, map_one, LinearMap.add_apply, Module.End.one_apply,
        map_mul (Polynomial.aeval T) U₀ P₀, Module.End.mul_apply, hP₀, map_zero, zero_add] at h1
      exact h1
    have ha₀_mem : a₀ ∈ S := by
      have heq : (Polynomial.aeval T (U₁ * P₁)) (a₀ + a₁) = a₀ := by
        rw [map_add, hfix₀, hkill₁, add_zero]
      rwa [heq] at hproj_mem
    have hsum_mem : a₀ + a₁ ∈ S :=
      Submodule.subset_span ⟨0, by simp⟩
    have ha₁_mem : a₁ ∈ S := by
      simpa [add_sub_cancel_left] using S.sub_mem hsum_mem ha₀_mem
    have hW₀_le : W₀ ≤ S := hspan₀.trans (Submodule.span_le.mpr (by
      rintro _ ⟨n, rfl⟩
      exact FP5CyclicSlope.pow_mem_cyclicSpan_of_mem T (a₀ + a₁) a₀ ha₀_mem n))
    have hW₁_le : W₁ ≤ S := hspan₁.trans (Submodule.span_le.mpr (by
      rintro _ ⟨n, rfl⟩
      exact FP5CyclicSlope.pow_mem_cyclicSpan_of_mem T (a₀ + a₁) a₁ ha₁_mem n))
    exact top_unique (hW ▸ sup_le hW₀_le hW₁_le)
