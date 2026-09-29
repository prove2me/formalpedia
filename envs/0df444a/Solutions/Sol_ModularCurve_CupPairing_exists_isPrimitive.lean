-- Prove2me | solution 1 for ModularCurve.CupPairing.exists_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/548e38f9-45e2-519f-bd79-f834fcd7f05a

import Mathlib
import Definitions.Def_ModularCurve_CupPairing
import Theorems.Thm_ModularCurve_PDPairing_isFreeGroup_Gamma_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CupPairing_exists_isPrimitive

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "CupPairing.IsPrimitive PDPairing.hPrim PDPairing.isFreeGroup_inf PDPairing.isFreeGroup_Gamma_four"
namespace CupPairing
p2m_export "ModularCurve.CupPairing" "IsPrimitive"
namespace PrimExist
p2m_open "ModularCurve.CupPairing ModularCurve"

open ModularCurve.PDPairing

section Abstract

variable {G : Type*} [Group G] (H : Subgroup G)

theorem transferElt_mem (g : G) (q : G ⧸ H) : (g • q).out⁻¹ * g * q.out ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← MulAction.Quotient.coe_smul_out,
    smul_eq_mul]

noncomputable def c (g : G) (q : G ⧸ H) : H := ⟨(g • q).out⁻¹ * g * q.out, transferElt_mem H g q⟩

@[scoped simp] theorem coe_c (g : G) (q : G ⧸ H) : (c H g q : G) = (g • q).out⁻¹ * g * q.out := rfl

theorem c_mul (g g' : G) (q : G ⧸ H) : c H (g * g') q = c H g (g' • q) * c H g' q := by
  apply Subtype.ext
  simp only [coe_c, Subgroup.coe_mul, mul_smul]
  group

def res (φ : Additive G →+ ℚ) : Additive H →+ ℚ := φ.comp (MonoidHom.toAdditive H.subtype)

@[scoped simp] theorem res_apply (φ : Additive G →+ ℚ) (k : H) :
    res H φ (Additive.ofMul k) = φ (Additive.ofMul (k : G)) := rfl

noncomputable def av (φ : Additive G →+ ℚ) (q : G ⧸ H) : ℚ := φ (Additive.ofMul q.out)

theorem apply_c (φ : Additive G →+ ℚ) (g : G) (q : G ⧸ H) :
    φ (Additive.ofMul (c H g q : G)) = φ (Additive.ofMul g) + av H φ q - av H φ (g • q) := by
  simp only [coe_c, ofMul_mul, ofMul_inv, map_add, map_neg, av]
  ring

variable [H.FiniteIndex]

noncomputable scoped instance fintypeQuot : Fintype (G ⧸ H) := Fintype.ofFinite _

theorem sum_smul_eq {M : Type*} [AddCommMonoid M] (g : G) (F : G ⧸ H → M) :
    ∑ q : G ⧸ H, F (g • q) = ∑ q : G ⧸ H, F q :=
  Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)

variable (φ ψ : Additive G →+ ℚ) (hH : H → ℚ)

noncomputable def A (g : G) : ℚ := ∑ q : G ⧸ H, hH (c H g q)

noncomputable def K (g : G) : ℚ := ∑ q : G ⧸ H, (av H φ (g • q) * av H ψ q - av H φ q * av H ψ (g • q))

noncomputable def hG (g : G) : ℚ := (A H hH g - K H φ ψ g) / (Fintype.card (G ⧸ H) : ℚ)

variable {H φ ψ hH}

theorem A_mul (hprim : IsPrimitive (res H φ) (res H ψ) hH) (g g' : G) :
    A H hH (g * g') = A H hH g + A H hH g' -
      ∑ q : G ⧸ H, omega (res H φ) (res H ψ) (c H g (g' • q)) (c H g' q) := by
  unfold A
  have h1 : ∑ q : G ⧸ H, hH (c H (g * g') q) =
      ∑ q : G ⧸ H, (hH (c H g (g' • q)) + hH (c H g' q) -
        omega (res H φ) (res H ψ) (c H g (g' • q)) (c H g' q)) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [c_mul, hprim]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_smul_eq H g' (fun q => hH (c H g q))]

theorem sum_omega_c (g g' : G) :
    ∑ q : G ⧸ H, omega (res H φ) (res H ψ) (c H g (g' • q)) (c H g' q) =
      (Fintype.card (G ⧸ H) : ℚ) * omega φ ψ g g' + K H φ ψ g + K H φ ψ g' - K H φ ψ (g * g') := by

  set a : G ⧸ H → ℚ := av H φ with ha
  set b : G ⧸ H → ℚ := av H ψ with hb

  have hpt : ∀ q : G ⧸ H, omega (res H φ) (res H ψ) (c H g (g' • q)) (c H g' q) =
      omega φ ψ g g' +
      ((a (g' • q) * b q - a q * b (g' • q)) +
        (a (g • g' • q) * b (g' • q) - a (g' • q) * b (g • g' • q)) -
        (a (g • g' • q) * b q - a q * b (g • g' • q))) +
      (φ (Additive.ofMul g) * (b q - b (g' • q)) +
        ψ (Additive.ofMul g') * (a (g' • q) - a (g • g' • q)) -
        ψ (Additive.ofMul g) * (a q - a (g' • q)) -
        φ (Additive.ofMul g') * (b (g' • q) - b (g • g' • q))) := by
    intro q
    simp only [omega, res_apply, apply_c, ha, hb]
    ring
  rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

  have hKg : K H φ ψ g = ∑ q : G ⧸ H, (a (g • g' • q) * b (g' • q) - a (g' • q) * b (g • g' • q)) := by
    unfold K
    rw [← sum_smul_eq H g' (fun q => a (g • q) * b q - a q * b (g • q))]
  have hKgg' : K H φ ψ (g * g') = ∑ q : G ⧸ H, (a (g • g' • q) * b q - a q * b (g • g' • q)) := by
    unfold K
    simp only [mul_smul, ha, hb]
  have hKg' : K H φ ψ g' = ∑ q : G ⧸ H, (a (g' • q) * b q - a q * b (g' • q)) := rfl
  have hquad : ∑ q : G ⧸ H, ((a (g' • q) * b q - a q * b (g' • q)) +
        (a (g • g' • q) * b (g' • q) - a (g' • q) * b (g • g' • q)) -
        (a (g • g' • q) * b q - a q * b (g • g' • q))) =
      K H φ ψ g + K H φ ψ g' - K H φ ψ (g * g') := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hKg, hKgg', hKg']
    ring

  have hb1 : ∑ q : G ⧸ H, b (g' • q) = ∑ q : G ⧸ H, b q := sum_smul_eq H g' b
  have ha1 : ∑ q : G ⧸ H, a (g' • q) = ∑ q : G ⧸ H, a q := sum_smul_eq H g' a
  have ha2 : ∑ q : G ⧸ H, a (g • g' • q) = ∑ q : G ⧸ H, a q := by
    rw [← sum_smul_eq H g a, ← sum_smul_eq H g' (fun q => a (g • q))]
  have hb2 : ∑ q : G ⧸ H, b (g • g' • q) = ∑ q : G ⧸ H, b q := by
    rw [← sum_smul_eq H g b, ← sum_smul_eq H g' (fun q => b (g • q))]
  have hlin : ∑ q : G ⧸ H, (φ (Additive.ofMul g) * (b q - b (g' • q)) +
        ψ (Additive.ofMul g') * (a (g' • q) - a (g • g' • q)) -
        ψ (Additive.ofMul g) * (a q - a (g' • q)) -
        φ (Additive.ofMul g') * (b (g' • q) - b (g • g' • q))) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hb1, ha1, ha2, hb2]
    ring
  rw [hquad, hlin]
  ring

theorem isPrimitive_hG (hprim : IsPrimitive (res H φ) (res H ψ) hH) :
    IsPrimitive φ ψ (hG H φ ψ hH) := by
  intro g g'
  have hn : (Fintype.card (G ⧸ H) : ℚ) ≠ 0 := by
    have : 0 < Fintype.card (G ⧸ H) := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold hG
  rw [A_mul hprim, sum_omega_c]
  field_simp
  ring

theorem exists_isPrimitive_of_subgroup (hex : ∃ hH : H → ℚ, IsPrimitive (res H φ) (res H ψ) hH) :
    ∃ h : G → ℚ, IsPrimitive φ ψ h := by
  obtain ⟨hH, hprim⟩ := hex
  exact ⟨hG H φ ψ hH, isPrimitive_hG hprim⟩

end Abstract

section SL2

open CongruenceSubgroup

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

abbrev freePart : Subgroup Γ := (Γ ⊓ Gamma 4).subgroupOf Γ

scoped instance freePart_finiteIndex : (freePart Γ).FiniteIndex := by
  unfold freePart
  infer_instance

@[reducible] noncomputable def isFreeGroup_freePart : IsFreeGroup ↥(freePart Γ) := by
  haveI : IsFreeGroup ↥(Gamma 4) := ModularCurve.PDPairing.isFreeGroup_Gamma_four
  haveI : IsFreeGroup ↥(Γ ⊓ Gamma 4) := ModularCurve.PDPairing.isFreeGroup_inf (Gamma 4) Γ
  exact IsFreeGroup.ofMulEquiv
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : Γ ⊓ Gamma 4 ≤ Γ)).symm

theorem main (φ ψ : Additive Γ →+ ℚ) : ∃ h : Γ → ℚ, IsPrimitive φ ψ h := by
  haveI : IsFreeGroup ↥(freePart Γ) := isFreeGroup_freePart Γ
  refine exists_isPrimitive_of_subgroup (H := freePart Γ) ⟨hPrim (res (freePart Γ) φ)
    (res (freePart Γ) ψ), fun g g' => hPrim_mul _ _ g g'⟩

end SL2

end ModularCurve.CupPairing.PrimExist
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_exists_isPrimitive.ModularCurve P2MW.S_ModularCurve_CupPairing_exists_isPrimitive.ModularCurve.CupPairing P2MW.S_ModularCurve_CupPairing_exists_isPrimitive.ModularCurve.CupPairing.PrimExist"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_exists_isPrimitive.ModularCurve P2MW.S_ModularCurve_CupPairing_exists_isPrimitive.ModularCurve.CupPairing"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_exists_isPrimitive.ModularCurve"

theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (φ ψ : Additive Γ →+ ℚ) :
    ∃ h : Γ → ℚ, ModularCurve.CupPairing.IsPrimitive φ ψ h :=
  ModularCurve.CupPairing.PrimExist.main Γ φ ψ

end S_ModularCurve_CupPairing_exists_isPrimitive
end P2MW
export P2MW.S_ModularCurve_CupPairing_exists_isPrimitive (solution)
