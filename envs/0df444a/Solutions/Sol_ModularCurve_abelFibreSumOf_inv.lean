-- Prove2me | solution 1 for ModularCurve.abelFibreSumOf_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/414e048f-601d-5bb4-aca9-3f3f5e72004c

import Mathlib
import Definitions.Def_ModularCurve_AbelFibreSumOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_abelFibreSumOf_inv

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace AbelFibreInvOf

open ModularCurve

theorem meromorphicOrderAt_inv_sub_inv {F : ℍ → ℂ} {t : ℂ} (ht : t ≠ 0) {τ : ℍ} {n : ℤ}
    (hn : 0 < n)
    (h : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = n) :
    meromorphicOrderAt (fun z : ℂ => (F (ofComplex z))⁻¹ - t⁻¹) (τ : ℂ) = n := by
  set G : ℂ → ℂ := fun z => F (ofComplex z) - t with hG
  set g : ℂ → ℂ := fun z => F (ofComplex z) with hg

  have hGm : MeromorphicAt G (τ : ℂ) := by
    by_contra hc
    have h0 := meromorphicOrderAt_of_not_meromorphicAt hc
    rw [h] at h0
    exact hn.ne' (by exact_mod_cast h0)
  have hgG : g = G + fun _ => t := by
    funext z; simp [hg, hG]
  have hcm : MeromorphicAt (fun _ : ℂ => t) (τ : ℂ) := MeromorphicAt.const t _
  have hgm : MeromorphicAt g (τ : ℂ) := by rw [hgG]; exact hGm.add hcm

  have hct : meromorphicOrderAt (fun _ : ℂ => t) (τ : ℂ) = 0 := by
    classical
    rw [meromorphicOrderAt_const, if_neg ht]
  have hg0 : meromorphicOrderAt g (τ : ℂ) = 0 := by
    rw [hgG, meromorphicOrderAt_add_eq_right_of_lt hGm (by rw [hct, h]; exact_mod_cast hn), hct]

  have hgne : ∀ᶠ z in 𝓝[≠] (τ : ℂ), g z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hgm).1 (by rw [hg0]; exact WithTop.zero_ne_top)
  have heq : (fun z : ℂ => (F (ofComplex z))⁻¹ - t⁻¹) =ᶠ[𝓝[≠] (τ : ℂ)]
      (-G) * (fun z => t * g z)⁻¹ := by
    filter_upwards [hgne] with z hz
    have hz' : F (ofComplex z) ≠ 0 := hz
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.inv_apply, hG, hg]
    rw [inv_sub_inv hz' ht, div_eq_mul_inv]
    ring
  rw [meromorphicOrderAt_congr heq]

  have htg : MeromorphicAt (fun z => t * g z) (τ : ℂ) := hcm.mul hgm
  have htg0 : meromorphicOrderAt (fun z => t * g z) (τ : ℂ) = 0 := by
    have := meromorphicOrderAt_mul_of_ne_zero (f := g) (g := fun _ : ℂ => t) (x := (τ : ℂ))
      analyticAt_const ht
    rw [hg0] at this
    exact this
  rw [meromorphicOrderAt_mul hGm.neg htg.inv, ← meromorphicOrderAt_neg, h, meromorphicOrderAt_inv,
    htg0]
  simp

theorem valueMultiplicity_inv (F : ℍ → ℂ) {t : ℂ} (ht : t ≠ 0) (τ : ℍ) :
    valueMultiplicity (fun τ : ℍ => (F τ)⁻¹) t⁻¹ τ = valueMultiplicity F t τ := by

  have key : ∀ (F : ℍ → ℂ) (t : ℂ), t ≠ 0 → ∀ τ : ℍ, valueMultiplicity F t τ ≠ 0 →
      valueMultiplicity (fun τ : ℍ => (F τ)⁻¹) t⁻¹ τ = valueMultiplicity F t τ := by
    intro F t ht τ hm
    cases ho : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) using
      WithTop.recTopCoe with
    | top => exact absurd (valueMultiplicity_of_eq_top ho) hm
    | coe k =>
      have hk : 0 < k := by
        by_contra hk
        push Not at hk
        apply hm
        rw [valueMultiplicity_def, ho]
        simp [Int.toNat_eq_zero.2 hk]
      have hk' : ((k.toNat : ℤ) : WithTop ℤ) = (k : WithTop ℤ) := by
        rw [Int.toNat_of_nonneg hk.le]
      have h1 : valueMultiplicity F t τ = k.toNat := valueMultiplicity_of_eq_coe (by rw [hk', ho])
      have h2 := meromorphicOrderAt_inv_sub_inv (F := F) ht hk ho
      have h3 : valueMultiplicity (fun τ : ℍ => (F τ)⁻¹) t⁻¹ τ = k.toNat :=
        valueMultiplicity_of_eq_coe (by rw [hk', h2])
      rw [h1, h3]
  by_cases hm : valueMultiplicity F t τ = 0
  · by_cases hm' : valueMultiplicity (fun τ : ℍ => (F τ)⁻¹) t⁻¹ τ = 0
    · rw [hm, hm']
    ·
      have h : valueMultiplicity (fun τ : ℍ => ((F τ)⁻¹)⁻¹) t⁻¹⁻¹ τ =
          valueMultiplicity (fun τ : ℍ => (F τ)⁻¹) t⁻¹ τ :=
        key (fun τ : ℍ => (F τ)⁻¹) t⁻¹ (inv_ne_zero ht) τ hm'
      have h' : valueMultiplicity F t τ = valueMultiplicity (fun τ : ℍ => (F τ)⁻¹) t⁻¹ τ := by
        simpa only [inv_inv] using h
      rw [hm] at h'
      exact absurd h'.symm hm'
  · exact key F t ht τ hm

end AbelFibreInvOf

theorem solution (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) {t : ℂ} (ht : t ≠ 0) :
    ModularCurve.abelFibreSumOf Γ (fun τ : ℍ => (F τ)⁻¹) t⁻¹ =
      ModularCurve.abelFibreSumOf Γ F t := by
  simp only [ModularCurve.abelFibreSumOf_def, AbelFibreInvOf.valueMultiplicity_inv F ht]

end S_ModularCurve_abelFibreSumOf_inv
end P2MW
export P2MW.S_ModularCurve_abelFibreSumOf_inv (solution)
