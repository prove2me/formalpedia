-- Prove2me | solution 1 for HeckeCohomology.heckeH1_eq_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/274342e7-6b57-5163-89cd-9e4abbaf3aca

import Definitions.Def_GroupCohomology_TransferHecke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_heckeH1_eq_of_section

set_option autoImplicit false

namespace TWIndepAux

open groupCohomology HeckeCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁)
  (A : Rep k Γ) (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ)

theorem cocycle_apply_one (f : cocycles₁ A) : f (1 : Γ) = 0 := by
  have h := ((mem_cocycles₁_iff f).1 f.2) 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at h
  have h0 : f (1 : Γ) + 0 = f (1 : Γ) + f (1 : Γ) := by rw [add_zero]; exact h
  exact (add_left_cancel h0).symm

include hφ in

theorem twist_inv (f : cocycles₁ A) (s : S₂) :
    φ (f ((c s⁻¹ : S₁) : Γ)) = -(A.ρ ((s : Γ))⁻¹ (φ (f ((c s : S₁) : Γ)))) := by
  have h := transport_cocycle S₁ S₂ c A φ hφ f s⁻¹ s
  rw [inv_mul_cancel] at h
  rw [map_one] at h
  rw [OneMemClass.coe_one] at h
  rw [cocycle_apply_one] at h
  rw [map_zero] at h
  have h2 := eq_neg_of_add_eq_zero_right h.symm
  rw [h2, InvMemClass.coe_inv]

theorem cls_rep (q : Quotient (QuotientGroup.rightRel S₂)) : cls S₂ (rep S₂ q) = q := by
  simp [HeckeCohomology.rep, HeckeCohomology.cls]

theorem slip_coe (q : Quotient (QuotientGroup.rightRel S₂)) (γ : Γ) :
    ((slip S₂ q γ : S₂) : Γ) = rep S₂ q * γ * (rep S₂ (cls S₂ (rep S₂ q * γ)))⁻¹ := rfl

variable (r : Quotient (QuotientGroup.rightRel S₂) → Γ) (hr : ∀ q, cls S₂ (r q) = q)

include hr in

theorem shift_mem (q : Quotient (QuotientGroup.rightRel S₂)) : r q * (rep S₂ q)⁻¹ ∈ S₂ := by
  have h2 : cls S₂ (r q) = cls S₂ (rep S₂ q) := by rw [hr q, cls_rep]
  have h3 := Quotient.exact' h2
  rw [QuotientGroup.rightRel_apply] at h3
  simpa [mul_inv_rev, inv_inv] using inv_mem h3

noncomputable def sElt (q : Quotient (QuotientGroup.rightRel S₂)) : S₂ :=
  ⟨r q * (rep S₂ q)⁻¹, shift_mem S₂ r hr q⟩

theorem sElt_coe (q : Quotient (QuotientGroup.rightRel S₂)) :
    ((sElt S₂ r hr q : S₂) : Γ) = r q * (rep S₂ q)⁻¹ := rfl

theorem inv_r_mul_sElt (q : Quotient (QuotientGroup.rightRel S₂)) :
    (r q)⁻¹ * ((sElt S₂ r hr q : S₂) : Γ) = (rep S₂ q)⁻¹ := by
  rw [sElt_coe, inv_mul_cancel_left]

include hr in

theorem sigma_decomp (σ : Quotient (QuotientGroup.rightRel S₂) → Γ → S₂)
    (hσ : ∀ q γ, (σ q γ : Γ) = r q * γ * (r (cls S₂ (r q * γ)))⁻¹)
    (q : Quotient (QuotientGroup.rightRel S₂)) (γ : Γ) :
    σ q γ = sElt S₂ r hr q * slip S₂ q γ * (sElt S₂ r hr (cls S₂ (rep S₂ q * γ)))⁻¹ := by
  have hcls : cls S₂ (r q * γ) = cls S₂ (rep S₂ q * γ) := by
    have h := cls_rep_mul S₂ (r q) γ
    rw [hr q] at h
    exact h.symm
  apply Subtype.ext
  rw [hσ q γ, hcls, Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, sElt_coe, sElt_coe,
    slip_coe]
  simp [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left]

theorem cls_r_eq_of_slip (σ : Quotient (QuotientGroup.rightRel S₂) → Γ → S₂)
    (hσ : ∀ q γ, (σ q γ : Γ) = r q * γ * (r (cls S₂ (r q * γ)))⁻¹)
    (q : Quotient (QuotientGroup.rightRel S₂)) : cls S₂ (r q) = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    have hmem : x * (r (cls S₂ x))⁻¹ ∈ S₂ := by
      have h := (σ (cls S₂ x) ((r (cls S₂ x))⁻¹ * x)).2
      rw [hσ, mul_inv_cancel_left] at h
      exact h
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr hmem)

end TWIndepAux

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
open groupCohomology HeckeCohomology TWIndepAux in
theorem solution {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) (A : Rep k Γ) [S₂.FiniteIndex]
    (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ)
    (r : Quotient (QuotientGroup.rightRel S₂) → Γ)
    (σ : Quotient (QuotientGroup.rightRel S₂) → Γ → S₂)
    (hσ : ∀ q γ, (σ q γ : Γ) = r q * γ * (r (cls S₂ (r q * γ)))⁻¹)
    (f g : cocycles₁ A)
    (hg : ∀ γ : Γ, g γ = ∑ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ (r q)⁻¹ (φ (f (c (σ q γ) : Γ)))) :
    H1π A g = heckeH1 S₁ S₂ c A φ hφ (H1π A f) := by
  have hr : ∀ q, cls S₂ (r q) = q := cls_r_eq_of_slip S₂ r σ hσ
  have hcomp : ∀ (x y : Γ) (v : A), A.ρ x (A.ρ y v) = A.ρ (x * y) v := fun x y v => by
    rw [← Module.End.mul_apply, ← map_mul]
  set a₀ : A := ∑ q : Quotient (QuotientGroup.rightRel S₂),
    A.ρ (r q)⁻¹ (φ (f (c (sElt S₂ r hr q) : Γ))) with ha₀
  have hterm : ∀ (q : Quotient (QuotientGroup.rightRel S₂)) (γ : Γ),
      A.ρ (r q)⁻¹ (φ (f (c (σ q γ) : Γ))) =
        -(A.ρ (γ * (r (cls S₂ (rep S₂ q * γ)))⁻¹)
            (φ (f (c (sElt S₂ r hr (cls S₂ (rep S₂ q * γ))) : Γ)))) +
          (A.ρ (rep S₂ q)⁻¹ (φ (f (c (slip S₂ q γ) : Γ))) +
            A.ρ (r q)⁻¹ (φ (f (c (sElt S₂ r hr q) : Γ)))) := by
    intro q γ
    rw [sigma_decomp S₂ r hr σ hσ q γ, mul_assoc,
      transport_cocycle S₁ S₂ c A φ hφ f (sElt S₂ r hr q)
        (slip S₂ q γ * (sElt S₂ r hr (cls S₂ (rep S₂ q * γ)))⁻¹),
      transport_cocycle S₁ S₂ c A φ hφ f (slip S₂ q γ)
        ((sElt S₂ r hr (cls S₂ (rep S₂ q * γ)))⁻¹),
      twist_inv S₁ S₂ c A φ hφ f (sElt S₂ r hr (cls S₂ (rep S₂ q * γ)))]
    simp only [map_add, map_neg, hcomp]
    rw [inv_r_mul_sElt S₂ r hr q]
    have hT1 : (r q)⁻¹ * (((sElt S₂ r hr q : S₂) : Γ) *
        (((slip S₂ q γ : S₂) : Γ) *
          (((sElt S₂ r hr (cls S₂ (rep S₂ q * γ)) : S₂) : Γ))⁻¹)) =
        γ * (r (cls S₂ (rep S₂ q * γ)))⁻¹ := by
      rw [sElt_coe, sElt_coe, slip_coe, mul_inv_rev, inv_inv]
      simp [mul_assoc, inv_mul_cancel_left]
    rw [hT1, add_assoc]
  have hre : ∀ γ : Γ, (∑ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ γ (A.ρ (r (cls S₂ (rep S₂ q * γ)))⁻¹
        (φ (f (c (sElt S₂ r hr (cls S₂ (rep S₂ q * γ))) : Γ))))) =
      A.ρ γ a₀ := by
    intro γ
    rw [← map_sum, ha₀]
    refine congrArg _ (Fintype.sum_equiv (mulRight S₂ γ) _ _ fun q => ?_)
    rw [mulRight_apply]
  have hsum : ∀ γ : Γ, g γ =
      -(A.ρ γ a₀) + (heckeZ1 S₁ S₂ c A φ hφ f γ + a₀) := by
    intro γ
    rw [hg γ, Finset.sum_congr rfl fun q _ => hterm q γ, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun q _ =>
      (hcomp γ ((r (cls S₂ (rep S₂ q * γ)))⁻¹) _).symm]
    rw [hre γ, ← heckeZ1_apply S₁ S₂ c A φ hφ f γ, ← ha₀]
  have hπ : H1π A g = H1π A (heckeZ1 S₁ S₂ c A φ hφ f) := by
    rw [H1π_eq_iff]
    refine ⟨-a₀, funext fun γ => ?_⟩
    show A.ρ γ (-a₀) - (-a₀) = (⇑g - ⇑(heckeZ1 S₁ S₂ c A φ hφ f)) γ
    rw [Pi.sub_apply, hsum γ, map_neg, sub_neg_eq_add,
      add_comm (heckeZ1 S₁ S₂ c A φ hφ f γ) a₀, ← add_assoc, add_sub_cancel_right]
  rw [hπ]
  exact (heckeH1_H1π S₁ S₂ c A φ hφ f).symm

end S_HeckeCohomology_heckeH1_eq_of_section
end P2MW
export P2MW.S_HeckeCohomology_heckeH1_eq_of_section (solution)
