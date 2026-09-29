-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/948c23f4-0dbc-5cfd-9141-e1fcc3606f99

import Mathlib
import Theorems.Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center
import Theorems.Thm_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix MatrixGroups Subgroup MulAction

noncomputable section

namespace BassSerreCuspSL2

abbrev G23 (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))
abbrev Gp : Type := Monoid.CoprodI G23
abbrev PSL : Type := SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ)

def τ : Gp := Monoid.CoprodI.of (M := G23) (i := 0) (Multiplicative.ofAdd 1) *
  Monoid.CoprodI.of (M := G23) (i := 1) (Multiplicative.ofAdd 1)

def e : Gp ≃* PSL := ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose

theorem mem_center_iff_eq (A : SL(2, ℤ)) : A ∈ Subgroup.center SL(2, ℤ) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r * r = 1 := by rw [← pow_two]; simpa using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hA, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [← hA, map_neg, map_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩

theorem e_of_zero : e (Monoid.CoprodI.of (i := 0) (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.1

theorem e_of_one : e (Monoid.CoprodI.of (i := 1) (Multiplicative.ofAdd 1))
    = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.2

theorem e_τ : e τ = QuotientGroup.mk ModularGroup.T := by
  have hSS : ModularGroup.S * ModularGroup.S = -1 := by decide
  have h1 : (QuotientGroup.mk (-1 : SL(2, ℤ)) : PSL) = 1 :=
    (QuotientGroup.eq_one_iff (-1 : SL(2, ℤ))).mpr ((mem_center_iff_eq _).mpr (Or.inr rfl))
  rw [τ, map_mul, e_of_zero, e_of_one, ← QuotientGroup.mk_mul, ← mul_assoc, hSS, QuotientGroup.mk_mul,
    h1, one_mul]

def π : SL(2, ℤ) →* Gp := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

theorem π_apply (g : SL(2, ℤ)) : π g = e.symm (QuotientGroup.mk g) := rfl

theorem π_T : π ModularGroup.T = τ := by
  rw [π_apply, ← e_τ, MulEquiv.symm_apply_apply]

theorem π_surjective : Function.Surjective π :=
  e.symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem π_ker_le (Γ : Subgroup SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : π.ker ≤ Γ := by
  intro z hz
  rw [MonoidHom.mem_ker, π_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hz
  rcases (mem_center_iff_eq z).mp hz with rfl | rfl
  · exact one_mem Γ
  · exact hneg

section Main

variable (Γ : Subgroup SL(2, ℤ))

abbrev Hm : Subgroup Gp := Γ.map π

theorem comap_Hm (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : (Hm Γ).comap π = Γ := Subgroup.comap_map_eq_self (π_ker_le Γ hneg)

theorem mem_Γ_iff (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (g : SL(2, ℤ)) : g ∈ Γ ↔ π g ∈ Hm Γ := by
  conv_lhs => rw [← comap_Hm Γ hneg]
  rfl

theorem index_Hm (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : (Hm Γ).index = Γ.index := Subgroup.index_map_eq _ π_surjective (π_ker_le Γ hneg)

def θ : SL(2, ℤ) ⧸ Γ → Gp ⧸ Hm Γ :=
  Quotient.map' π fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem π h

@[scoped simp] theorem θ_mk (g : SL(2, ℤ)) : θ Γ (g : SL(2, ℤ) ⧸ Γ) = ((π g : Gp) : Gp ⧸ Hm Γ) := rfl

theorem θ_injective (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : Function.Injective (θ Γ) := by
  intro x y h
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [θ_mk, θ_mk, QuotientGroup.eq, ← map_inv, ← map_mul, ← mem_Γ_iff Γ hneg] at h
  exact QuotientGroup.eq.mpr h

theorem θ_smul (g : SL(2, ℤ)) (x : SL(2, ℤ) ⧸ Γ) : θ Γ (g • x) = π g • θ Γ x := by
  induction x using QuotientGroup.induction_on with | H a =>
  show θ Γ ((g * a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) = ((π g * π a : Gp) : Gp ⧸ Hm Γ)
  rw [θ_mk, map_mul]

theorem θ_T_zpow_smul (n : ℤ) (x : SL(2, ℤ) ⧸ Γ) :
    θ Γ (ModularGroup.T ^ n • x) = τ ^ n • θ Γ x := by
  rw [θ_smul, map_zpow, π_T]

theorem minimalPeriod_eq (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (x : SL(2, ℤ) ⧸ Γ) :
    Function.minimalPeriod (fun y => ModularGroup.T • y) x
      = Function.minimalPeriod (fun y => τ • y) (θ Γ x) := by
  apply Nat.dvd_antisymm
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd]
    apply θ_injective Γ hneg
    rw [← zpow_natCast, θ_T_zpow_smul Γ, zpow_natCast]
    exact (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, ← zpow_natCast, ← θ_T_zpow_smul Γ,
      zpow_natCast]
    congr 1
    exact (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl

theorem mem_orbit_iff_θ (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (x y : SL(2, ℤ) ⧸ Γ) :
    x ∈ orbit (zpowers ModularGroup.T) y ↔ θ Γ x ∈ orbit (zpowers τ) (θ Γ y) := by
  constructor
  · rintro ⟨⟨_, n, rfl⟩, rfl⟩
    exact ⟨⟨τ ^ n, n, rfl⟩, (θ_T_zpow_smul Γ n y).symm⟩
  · rintro ⟨⟨_, n, rfl⟩, h⟩
    refine ⟨⟨ModularGroup.T ^ n, n, rfl⟩, θ_injective Γ hneg ?_⟩
    rw [← h]
    exact θ_T_zpow_smul Γ n y

def Θ (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : orbitRel.Quotient (zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ)
    ≃ orbitRel.Quotient (zpowers τ) (Gp ⧸ Hm Γ) :=
  Quotient.congr (Equiv.ofBijective (θ Γ)
      ⟨θ_injective Γ hneg, fun y => by
        induction y using QuotientGroup.induction_on with | H k =>
        obtain ⟨g, rfl⟩ := π_surjective k
        exact ⟨(g : SL(2, ℤ) ⧸ Γ), rfl⟩⟩)
    (fun x y => mem_orbit_iff_θ Γ hneg x y)

theorem Θ_mk (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (x : SL(2, ℤ) ⧸ Γ) :
    Θ Γ hneg (Quotient.mk (orbitRel (zpowers ModularGroup.T) _) x)
      = Quotient.mk (orbitRel (zpowers τ) _) (θ Γ x) := rfl

end Main

end BassSerreCuspSL2
p2m_reactivate "P2MW.S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero.BassSerreCuspSL2"

open BassSerreCuspSL2 in
theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive Γ →+ R,
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (hg : g⁻¹ * ModularGroup.T ^ Function.minimalPeriod (fun x => ModularGroup.T • x)
                (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) * g ∈ Γ),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) _)
              (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ)) := by
  haveI : (Hm Γ).FiniteIndex := ⟨by rw [index_Hm Γ hneg]; exact Subgroup.FiniteIndex.index_ne_zero⟩

  set a' : MulAction.orbitRel.Quotient (Subgroup.zpowers τ) (Gp ⧸ Hm Γ) → R :=
    fun c => a ((Θ Γ hneg).symm c) with ha'def
  have ha' : ∑ᶠ c, a' c = 0 := by
    rw [← ha]
    exact finsum_eq_of_bijective (Θ Γ hneg).symm (Θ Γ hneg).symm.bijective fun c => rfl
  obtain ⟨φH, hφH⟩ :=
    Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero τ rfl (Hm Γ) R a' ha'
  refine ⟨φH.comp (MonoidHom.toAdditive (π.subgroupMap Γ)), fun g hg => ?_⟩
  have hk : (π g)⁻¹ * τ ^ Function.minimalPeriod (fun x => τ • x) ((π g : Gp) : Gp ⧸ Hm Γ) * π g
      ∈ Hm Γ := by
    rw [← θ_mk Γ, ← minimalPeriod_eq Γ hneg, ← π_T, ← map_pow, ← map_inv, ← map_mul,
      ← map_mul, ← mem_Γ_iff Γ hneg]
    exact hg
  have key := hφH (π g) hk
  rw [AddMonoidHom.comp_apply]
  have hmap : (MonoidHom.toAdditive (π.subgroupMap Γ)) (Additive.ofMul ⟨_, hg⟩)
      = Additive.ofMul ⟨_, hk⟩ := by
    show Additive.ofMul (π.subgroupMap Γ ⟨_, hg⟩) = _
    congr 1
    apply Subtype.ext
    show π (g⁻¹ * ModularGroup.T ^ _ * g) = _
    rw [map_mul, map_mul, map_inv, map_pow, π_T, minimalPeriod_eq Γ hneg, θ_mk]
  rw [hmap, key, ha'def]
  show a ((Θ Γ hneg).symm (Θ Γ hneg (Quotient.mk _ (g : SL(2, ℤ) ⧸ Γ)))) = _
  rw [Equiv.symm_apply_apply]

#print axioms solution

end
end S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero (solution)
