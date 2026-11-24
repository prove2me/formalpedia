-- Prove2me | solution 1 for GlobalTheory.Phase.GaussSum.ph_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:56:39.234577+00:00
-- url     : https://prove2.me/submissions/56be4561-1837-421e-9338-6571cbf4ab01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
import Theorems.Thm_GlobalTheory_Phase_GaussSum_pow_four
import Theorems.Thm_GlobalTheory_Phase_GaussSum_isMu_mul
import Theorems.Thm_GlobalTheory_Phase_GaussSum_isMu_norm
import Theorems.Thm_GlobalTheory_Phase_ph_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum
namespace GlobalTheory.Phase.GaussSum
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  intro M _ _ f ⟨h1, h3⟩
  have hmu : ∀ x, IsMu (f x) := fun x => h1 x trivial
  let u : M → Circle := fun x => ⟨f x, mem_sphere_zero_iff_norm.2 (isMu_norm (hmu x))⟩
  let p : M → Additive Circle := fun x => Additive.ofMul (u x)
  have hp : ∀ x y z, p (x + y + z) + p x + p y + p z = p (x + y) + p (y + z) + p (x + z) + p 0 := by
    intro x y z
    have : u (x + y + z) * u x * u y * u z = u (x + y) * u (y + z) * u (x + z) * u 0 :=
      Circle.ext (by simp only [Circle.coe_mul]; exact h3 x trivial y trivial z trivial)
    exact congrArg Additive.ofMul this
  let β : M →+ M →+ Additive Circle := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => p (x + y) - p x - p y + p 0)
      (fun y z => by
        have := hp x y z
        rw [← add_assoc]
        rw [← sub_eq_zero] at this ⊢; rw [← this]; abel))
    (fun x y => by
      ext1 z
      have := hp x y z
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← sub_eq_zero] at this ⊢; rw [← this]; abel)
  let e : Additive Circle → ℂ := fun t => ((Additive.toMul t : Circle) : ℂ)
  have he : ∀ s t, e (s + t) = e s * e t := fun s t => by simp [e]
  have hc : ∀ t, e (-t) = conj (e t) := fun t => by
    simp only [e, toMul_neg]; exact Circle.coe_inv_eq_conj _
  have hf : ∀ x, f x = f 0 * e (p x - p 0) := by
    intro x
    have : e (p 0 + (p x - p 0)) = e (p x) := by congr 1; abel
    rw [he] at this
    exact this.symm
  have hmu' : ∀ x, IsMu (e (p x - p 0)) := by
    intro x
    rw [sub_eq_add_neg, he, hc]
    refine isMu_mul (hmu x) ?_
    obtain ⟨m, hm, h⟩ := hmu 0
    exact ⟨m, hm, by rw [← map_pow]; change conj (f 0 ^ m) = 1; rw [h, map_one]⟩
  have hsum : ∑ x, f x = f 0 * ∑ x, e (p x - p 0) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => hf x
  rw [hsum]
  rcases pow_four e he hc (by simp [e]) (fun x => p x - p 0) β (fun x y => by
    simp only [β, AddMonoidHom.mk'_apply]; abel) with h | ⟨a, h⟩
  · rw [pow_eq_zero_iff (by norm_num)] at h
    rw [h, mul_zero]; exact ph_zero
  · set S := ∑ x, e (p x - p 0)
    have hz : IsMu (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) := by
      refine isMu_mul ?_ ?_
      · obtain ⟨m, hm, h⟩ := hmu 0
        exact ⟨m, hm, by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]⟩
      · rw [Fin.prod_univ_four]
        exact isMu_mul (isMu_mul (isMu_mul (hmu' _) (hmu' _)) (hmu' _)) (hmu' _)
    obtain ⟨m, hm, hz⟩ := hz
    refine ⟨8 * m, by omega, ?_⟩
    have h8 : (f 0 * S) ^ 8 = (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) * ((‖f 0 * S‖ : ℝ) : ℂ) ^ 8 := by
      have hn : ((‖S‖ : ℝ) : ℂ) ^ 8 = S ^ 4 * conj (S ^ 4) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]; push_cast; ring
      rw [norm_mul, isMu_norm (hmu 0), one_mul, hn]
      linear_combination f 0 ^ 8 * S ^ 4 * h
    rw [pow_mul, h8, mul_pow, hz, one_mul, pow_mul]
end GlobalTheory.Phase.GaussSum
