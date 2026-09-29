-- Prove2me | solution 1 for ModularCurve.Period.existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2c3bf78f-e9c1-5ebb-8b95-4b6bac3b5e01

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq

set_option autoImplicit false

open scoped MatrixGroups

namespace ParabolicPlusMinus

open ModularCurve.Period

variable (Γ : Subgroup SL(2, ℤ))

abbrev pm : Subgroup SL(2, ℤ) := Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

theorem neg_one_mem_pm : (-1 : SL(2, ℤ)) ∈ pm Γ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem mem_pm_of_mem {g : SL(2, ℤ)} (hg : g ∈ Γ) : g ∈ pm Γ := Subgroup.mem_sup_left hg

scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g ((-1 : SL(2, ℤ)) ^ k) := (Commute.neg_one_right g).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩

theorem exists_of_mem_pm {g : SL(2, ℤ)} (hg : g ∈ pm Γ) :
    ∃ γ : SL(2, ℤ), γ ∈ Γ ∧ (g = γ ∨ g = -γ) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨y, hy, ?_⟩
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    have : ((-1 : SL(2, ℤ)) ^ (2 : ℤ)) = 1 := by rw [zpow_two]; simp
    rw [← two_mul, zpow_mul, this, one_zpow, mul_one]
  · right
    have : ((-1 : SL(2, ℤ)) ^ (2 : ℤ)) = 1 := by rw [zpow_two]; simp
    rw [zpow_add, zpow_mul, this, one_zpow, one_mul, zpow_one, mul_neg_one]

theorem trace_neg_sq (γ : SL(2, ℤ)) :
    (((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, neg_sq]

theorem trace_neg_one_sq : (((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  rw [trace_neg_sq]; simp

variable {Γ}
variable {A : Type*} [AddCommGroup A] (ψ : Additive Γ →+ A) (hψ : IsParabolicHom Γ ψ)

include hψ in

theorem apply_neg_one (h : (-1 : SL(2, ℤ)) ∈ Γ) : ψ (Additive.ofMul ⟨-1, h⟩) = 0 :=
  hψ ⟨-1, h⟩ trace_neg_one_sq

include hψ in

theorem apply_eq_of_eq_or_eq_neg {γ δ : SL(2, ℤ)} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ)
    (h : γ = δ ∨ γ = -δ) : ψ (Additive.ofMul ⟨γ, hγ⟩) = ψ (Additive.ofMul ⟨δ, hδ⟩) := by
  rcases h with rfl | rfl
  · rfl
  · have hm : (-1 : SL(2, ℤ)) ∈ Γ := by
      have := Γ.mul_mem hγ (Γ.inv_mem hδ)
      simpa using this
    have hprod : (⟨-δ, hγ⟩ : Γ) = ⟨-1, hm⟩ * ⟨δ, hδ⟩ := Subtype.ext (by simp)
    rw [hprod, ofMul_mul, map_add, apply_neg_one ψ hψ hm, zero_add]

noncomputable def rep (g : pm Γ) : SL(2, ℤ) := (exists_of_mem_pm Γ g.2).choose

theorem rep_mem (g : pm Γ) : rep g ∈ Γ := (exists_of_mem_pm Γ g.2).choose_spec.1

theorem eq_or_eq_neg_rep (g : pm Γ) : (g : SL(2, ℤ)) = rep g ∨ (g : SL(2, ℤ)) = -rep g :=
  (exists_of_mem_pm Γ g.2).choose_spec.2

noncomputable def extFun (g : pm Γ) : A := ψ (Additive.ofMul ⟨rep g, rep_mem g⟩)

include hψ in

theorem extFun_eq (g : pm Γ) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ)
    (h : (g : SL(2, ℤ)) = γ ∨ (g : SL(2, ℤ)) = -γ) : extFun ψ g = ψ (Additive.ofMul ⟨γ, hγ⟩) := by
  unfold extFun
  apply apply_eq_of_eq_or_eq_neg ψ hψ
  rcases eq_or_eq_neg_rep g with h1 | h1 <;> rcases h with h2 | h2
  · exact Or.inl (h1.symm.trans h2)
  · exact Or.inr (h1.symm.trans h2)
  · exact Or.inr (by rw [← neg_eq_iff_eq_neg.mpr h1, h2])
  · exact Or.inl (by have := h1.symm.trans h2; exact neg_injective this)

private noncomputable def _root_.ParabolicPlusMinus.ext : Additive (pm Γ) →+ A where
  toFun g := extFun ψ (Additive.toMul g)
  map_zero' := by
    show extFun ψ (1 : pm Γ) = 0
    rw [extFun_eq ψ hψ (1 : pm Γ) Γ.one_mem (Or.inl rfl)]
    exact map_zero ψ
  map_add' x y := by
    show extFun ψ (Additive.toMul x * Additive.toMul y) = extFun ψ (Additive.toMul x) + extFun ψ (Additive.toMul y)
    set g := Additive.toMul x
    set g' := Additive.toMul y
    have hgg : ((g * g' : pm Γ) : SL(2, ℤ)) = rep g * rep g' ∨
        ((g * g' : pm Γ) : SL(2, ℤ)) = -(rep g * rep g') := by
      rw [Subgroup.coe_mul]
      rcases eq_or_eq_neg_rep g with h1 | h1 <;> rcases eq_or_eq_neg_rep g' with h2 | h2 <;>
        rw [h1, h2]
      · exact Or.inl rfl
      · exact Or.inr (by simp)
      · exact Or.inr (by simp)
      · exact Or.inl (by simp)
    rw [extFun_eq ψ hψ (g * g') (Γ.mul_mem (rep_mem g) (rep_mem g')) hgg]
    have : (⟨rep g * rep g', Γ.mul_mem (rep_mem g) (rep_mem g')⟩ : Γ) =
        ⟨rep g, rep_mem g⟩ * ⟨rep g', rep_mem g'⟩ := rfl
    rw [this, ofMul_mul, map_add]
    rfl

p2m_export "ParabolicPlusMinus" "ext"
theorem ext_apply_of_mem (γ : Γ) :
    ext ψ hψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), mem_pm_of_mem Γ γ.2⟩) = ψ (Additive.ofMul γ) :=
  extFun_eq ψ hψ _ γ.2 (Or.inl rfl)

theorem isParabolicHom_ext : IsParabolicHom (pm Γ) (ext ψ hψ) := by
  intro g hg
  show extFun ψ g = 0
  rw [extFun]
  apply hψ
  rcases eq_or_eq_neg_rep g with h | h
  · simpa [h] using hg
  · have : ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 =
        ((rep g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 := by
      rw [h, trace_neg_sq]
    rw [← this]; exact hg

theorem unique_ext (φ : Additive (pm Γ) →+ A) (hφ : IsParabolicHom (pm Γ) φ)
    (hφψ : ∀ γ : Γ, φ (Additive.ofMul ⟨(γ : SL(2, ℤ)), mem_pm_of_mem Γ γ.2⟩) = ψ (Additive.ofMul γ)) :
    φ = ext ψ hψ := by
  ext x
  set g := Additive.toMul x
  show φ (Additive.ofMul g) = ext ψ hψ (Additive.ofMul g)
  have hm1 : φ (Additive.ofMul ⟨-1, neg_one_mem_pm Γ⟩) = 0 := hφ ⟨-1, neg_one_mem_pm Γ⟩ trace_neg_one_sq
  rcases eq_or_eq_neg_rep g with h | h
  · have hg : g = ⟨rep g, mem_pm_of_mem Γ (rep_mem g)⟩ := Subtype.ext h
    rw [hg, hφψ ⟨rep g, rep_mem g⟩]
    exact (extFun_eq ψ hψ (⟨rep g, mem_pm_of_mem Γ (rep_mem g)⟩ : pm Γ) (rep_mem g) (Or.inl rfl)).symm
  · have hg : g = ⟨-1, neg_one_mem_pm Γ⟩ * ⟨rep g, mem_pm_of_mem Γ (rep_mem g)⟩ :=
      Subtype.ext (by rw [h]; simp)
    rw [hg, ofMul_mul, map_add, map_add, hm1, zero_add, hφψ ⟨rep g, rep_mem g⟩]
    have e1 : ext ψ hψ (Additive.ofMul (⟨rep g, mem_pm_of_mem Γ (rep_mem g)⟩ : pm Γ)) =
        ψ (Additive.ofMul ⟨rep g, rep_mem g⟩) :=
      extFun_eq ψ hψ (⟨rep g, mem_pm_of_mem Γ (rep_mem g)⟩ : pm Γ) (rep_mem g) (Or.inl rfl)
    have e2 : ext ψ hψ (Additive.ofMul (⟨-1, neg_one_mem_pm Γ⟩ : pm Γ)) = ψ (Additive.ofMul ⟨1, Γ.one_mem⟩) :=
      extFun_eq ψ hψ (⟨-1, neg_one_mem_pm Γ⟩ : pm Γ) Γ.one_mem (Or.inr (by simp))
    rw [e1, e2]
    have : (⟨1, Γ.one_mem⟩ : Γ) = 1 := rfl
    rw [this, ofMul_one, map_zero, zero_add]

end ParabolicPlusMinus
p2m_reactivate "P2MW.S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq.ParabolicPlusMinus"

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A]
    (ψ : Additive Γ →+ A) (hψ : ModularCurve.Period.IsParabolicHom Γ ψ) :
    ∃! φ : Additive ↥(Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) →+ A,
      ModularCurve.Period.IsParabolicHom (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) φ ∧
        ∀ γ : Γ, φ (Additive.ofMul ⟨(γ : SL(2, ℤ)), Subgroup.mem_sup_left γ.2⟩) = ψ (Additive.ofMul γ) := by
  refine ⟨ParabolicPlusMinus.ext ψ hψ, ⟨ParabolicPlusMinus.isParabolicHom_ext ψ hψ,
    ParabolicPlusMinus.ext_apply_of_mem ψ hψ⟩, ?_⟩
  rintro φ ⟨hφ, hφψ⟩
  exact ParabolicPlusMinus.unique_ext ψ hψ φ hφ hφψ

end S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq
end P2MW
export P2MW.S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq (solution)
