-- Prove2me | solution 1 for ModularCurve.CupPairing.mult_mul_pair_coresAdd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8d2f82b9-6656-5787-b093-93f5cd2563be

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_CupPairing
import Theorems.Thm_ModularCurve_CupPairing_exists_isPrimitive
import Theorems.Thm_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive
import Theorems.Thm_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "CupPairing.mult CupPairing.pair Period.IsParabolicHom CupPairing.exists_isPrimitive CupPairing.pair_eq_cuspSum_div_of_isPrimitive CupPairing.cuspSum_eq_sum_finsum_of_le"
namespace CupPairing
p2m_export "ModularCurve.CupPairing" "IsPrimitive mult pair mult_ne_zero exists_isPrimitive pair_eq_cuspSum_div_of_isPrimitive cuspSum_eq_sum_finsum_of_le"
namespace Proj
p2m_open "ModularCurve.CupPairing ModularCurve"

open ModularCurve.PDPairing ModularCurve.Period MulAction Function

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

theorem coresAdd_apply (y : Additive H →+ ℚ) (g : G) :
    CohCarrier.coresAdd H y (Additive.ofMul g) = ∑ q : G ⧸ H, y (Additive.ofMul (c H g q)) := by
  have hα : ∀ r : G ⧸ H, ((default : H.LeftTransversal).2.leftQuotientEquiv r : G) = r.out :=
    fun r => Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq' r
  change Multiplicative.toAdd ((AddMonoidHom.toMultiplicativeRight y).transfer g) = _
  rw [MonoidHom.transfer_def _ (default : H.LeftTransversal) g]
  simp only [Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  refine (Fintype.sum_equiv (MulAction.toPerm g) (fun q => y (Additive.ofMul (c H g q))) _
    (fun q => ?_)).symm
  congr 2
  apply Subtype.ext
  simp only [coe_c, MulAction.toPerm_apply]
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, inv_smul_smul, hα, hα, smul_eq_mul, mul_assoc]

end Abstract

section ClassFn

variable {G : Type*} [Group G] {φ ψ : Additive G →+ ℚ} {h : G → ℚ}

theorem isPrimitive_one (hh : IsPrimitive φ ψ h) : h 1 = 0 := by
  have e := hh 1 1
  rw [one_mul, omega_one_left, sub_zero] at e
  linear_combination -e

theorem isPrimitive_conj (hh : IsPrimitive φ ψ h) (p δ : G) (hφ : φ (Additive.ofMul p) = 0)
    (hψ : ψ (Additive.ofMul p) = 0) : h (δ * p * δ⁻¹) = h p := by
  have e1 := hh (δ * p) δ⁻¹
  have e2 := hh δ p
  have e3 := hh δ δ⁻¹
  rw [mul_inv_cancel, isPrimitive_one hh] at e3
  simp only [omega, ofMul_mul, ofMul_inv, map_add, map_neg, hφ, hψ] at e1 e2 e3
  linear_combination e1 + e2 - e3

theorem isPrimitive_conj' (hh : IsPrimitive φ ψ h) (p δ : G) (hφ : φ (Additive.ofMul p) = 0)
    (hψ : ψ (Additive.ofMul p) = 0) : h (δ⁻¹ * p * δ) = h p := by
  have := isPrimitive_conj hh p δ⁻¹ hφ hψ
  rwa [inv_inv] at this

end ClassFn

section Twisted

variable {Γ : Type*} [Group Γ] (K' : Subgroup Γ) [K'.FiniteIndex]
variable (x : Additive Γ →+ ℚ) (yK : Additive K' →+ ℚ) (hK : K' → ℚ)

noncomputable def A (g : Γ) : ℚ := ∑ q : Γ ⧸ K', hK (c K' g q)

noncomputable def L (g : Γ) : ℚ :=
  ∑ q : Γ ⧸ K', (av K' x q + av K' x (g • q)) * yK (Additive.ofMul (c K' g q))

noncomputable def Htw (g : Γ) : ℚ := A K' hK g - L K' x yK g

variable {K' x yK hK}

theorem isPrimitive_Htw (hprim : IsPrimitive (res K' x) yK hK) :
    IsPrimitive x (CohCarrier.coresAdd K' yK) (Htw K' x yK hK) := by
  intro g g'
  set a : Γ ⧸ K' → ℚ := av K' x with ha
  set Y : Γ → Γ ⧸ K' → ℚ := fun g q => yK (Additive.ofMul (c K' g q)) with hY

  have hA : A K' hK (g * g') = A K' hK g + A K' hK g' -
      ∑ q : Γ ⧸ K', omega (res K' x) yK (c K' g (g' • q)) (c K' g' q) := by
    unfold A
    have h1 : ∑ q : Γ ⧸ K', hK (c K' (g * g') q) = ∑ q : Γ ⧸ K', (hK (c K' g (g' • q)) +
        hK (c K' g' q) - omega (res K' x) yK (c K' g (g' • q)) (c K' g' q)) := by
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [c_mul, hprim]
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_smul_eq K' g' (fun q => hK (c K' g q))]

  have hcor : ∀ g₀ : Γ, CohCarrier.coresAdd K' yK (Additive.ofMul g₀) = ∑ q : Γ ⧸ K', Y g₀ q :=
    fun g₀ => coresAdd_apply K' yK g₀
  have hYsucc : ∀ q, Y (g * g') q = Y g (g' • q) + Y g' q := by
    intro q
    simp only [hY, c_mul, ofMul_mul, map_add]
  have hΩ : ∑ q : Γ ⧸ K', omega (res K' x) yK (c K' g (g' • q)) (c K' g' q) =
      omega x (CohCarrier.coresAdd K' yK) g g' +
        (∑ q : Γ ⧸ K', (a (g' • q) - a (g • g' • q)) * Y g' q -
          ∑ q : Γ ⧸ K', (a q - a (g' • q)) * Y g (g' • q)) := by
    have hpt : ∀ q : Γ ⧸ K', omega (res K' x) yK (c K' g (g' • q)) (c K' g' q) =
        (x (Additive.ofMul g) * Y g' q - x (Additive.ofMul g') * Y g (g' • q)) +
        ((a (g' • q) - a (g • g' • q)) * Y g' q - (a q - a (g' • q)) * Y g (g' • q)) := by
      intro q
      simp only [omega, res_apply, apply_c, ha, hY]
      ring
    rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_smul_eq K' g' (fun q => Y g q), omega, hcor g, hcor g']
    ring

  have hL : L K' x yK g + L K' x yK g' - L K' x yK (g * g') =
      ∑ q : Γ ⧸ K', (a (g' • q) - a (g • g' • q)) * Y g' q -
        ∑ q : Γ ⧸ K', (a q - a (g' • q)) * Y g (g' • q) := by
    have hLg : L K' x yK g = ∑ q : Γ ⧸ K', (a (g' • q) + a (g • g' • q)) * Y g (g' • q) := by
      unfold L
      rw [← sum_smul_eq K' g' (fun q => (a q + a (g • q)) * Y g q)]
    have hLg' : L K' x yK g' = ∑ q : Γ ⧸ K', (a q + a (g' • q)) * Y g' q := rfl
    have hLgg' : L K' x yK (g * g') = ∑ q : Γ ⧸ K', (a q + a (g • g' • q)) * (Y g (g' • q) + Y g' q) := by
      unfold L
      refine Finset.sum_congr rfl (fun q _ => ?_)
      change (a q + a ((g * g') • q)) * Y (g * g') q = _
      rw [hYsucc, mul_smul]
    rw [hLg, hLg', hLgg', ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  unfold Htw
  rw [hA, hΩ]
  linear_combination hL

end Twisted

section Telescope

variable {Γ : Type*} [Group Γ] (K' : Subgroup Γ) [K'.FiniteIndex]
variable (x : Additive Γ →+ ℚ) (yK : Additive K' →+ ℚ) (hK : K' → ℚ)

omit [K'.FiniteIndex] in

theorem P_mem (u : Γ) (q₀ : Γ ⧸ K') (j : ℕ) : (u ^ j • q₀).out⁻¹ * u ^ j * q₀.out ∈ K' := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← MulAction.Quotient.coe_smul_out,
    smul_eq_mul]

noncomputable def P (u : Γ) (q₀ : Γ ⧸ K') (j : ℕ) : K' :=
  ⟨(u ^ j • q₀).out⁻¹ * u ^ j * q₀.out, P_mem K' u q₀ j⟩

@[scoped simp] theorem coe_P (u : Γ) (q₀ : Γ ⧸ K') (j : ℕ) :
    (P K' u q₀ j : Γ) = (u ^ j • q₀).out⁻¹ * u ^ j * q₀.out := rfl

theorem P_zero (u : Γ) (q₀ : Γ ⧸ K') : P K' u q₀ 0 = 1 := by
  apply Subtype.ext
  simp only [coe_P, pow_zero, one_smul, mul_one, inv_mul_cancel, Subgroup.coe_one]

theorem P_succ (u : Γ) (q₀ : Γ ⧸ K') (j : ℕ) :
    P K' u q₀ (j + 1) = c K' u (u ^ j • q₀) * P K' u q₀ j := by
  apply Subtype.ext
  simp only [coe_P, coe_c, Subgroup.coe_mul, pow_succ', mul_smul]
  group

variable {K' x yK hK}

theorem sum_range_term (hprim : IsPrimitive (res K' x) yK hK) (u : Γ) (hxu : x (Additive.ofMul u) = 0)
    (hxpow : ∀ j : ℕ, x (Additive.ofMul (u ^ j)) = 0) (q₀ : Γ ⧸ K') (n : ℕ) :
    ∑ j ∈ Finset.range n, (hK (c K' u (u ^ j • q₀)) -
        (av K' x (u ^ j • q₀) + av K' x (u ^ (j + 1) • q₀)) * yK (Additive.ofMul (c K' u (u ^ j • q₀)))) =
      (hK (P K' u q₀ n) - (av K' x q₀ + av K' x (u ^ n • q₀)) * yK (Additive.ofMul (P K' u q₀ n))) -
      (hK (P K' u q₀ 0) - (av K' x q₀ + av K' x (u ^ 0 • q₀)) * yK (Additive.ofMul (P K' u q₀ 0))) := by
  rw [← Finset.sum_range_sub (fun j => hK (P K' u q₀ j) -
    (av K' x q₀ + av K' x (u ^ j • q₀)) * yK (Additive.ofMul (P K' u q₀ j))) n]
  refine Finset.sum_congr rfl (fun j _ => ?_)

  have e1 := hprim (c K' u (u ^ j • q₀)) (P K' u q₀ j)
  rw [← P_succ] at e1

  have hxc : x (Additive.ofMul (c K' u (u ^ j • q₀) : Γ)) =
      av K' x (u ^ j • q₀) - av K' x (u ^ (j + 1) • q₀) := by
    rw [apply_c, hxu, zero_add, ← mul_smul, ← pow_succ']
  have hxP : x (Additive.ofMul (P K' u q₀ j : Γ)) = av K' x q₀ - av K' x (u ^ j • q₀) := by
    simp only [coe_P, ofMul_mul, ofMul_inv, map_add, map_neg, hxpow j, av]
    ring

  have hyP : yK (Additive.ofMul (P K' u q₀ (j + 1))) =
      yK (Additive.ofMul (c K' u (u ^ j • q₀))) + yK (Additive.ofMul (P K' u q₀ j)) := by
    rw [P_succ, ofMul_mul, map_add]
  simp only [omega, res_apply, hxc, hxP] at e1
  rw [e1, hyP]
  ring

end Telescope

theorem sum_zmod_cast (n : ℕ) [NeZero n] (f : ℤ → ℚ) :
    ∑ k : ZMod n, f (ZMod.cast k) = ∑ j ∈ Finset.range n, f j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [← Fin.sum_univ_eq_sum_range (fun j => f j)]
  rfl

section Core

variable (Γ' Γ : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] [Γ.FiniteIndex] (hle : Γ' ≤ Γ)

abbrev K' : Subgroup Γ := Γ'.subgroupOf Γ

noncomputable def ι : K' Γ' Γ ≃* Γ' := Subgroup.subgroupOfEquivOfLe hle

omit [Γ'.FiniteIndex] [Γ.FiniteIndex] in
@[scoped simp] theorem coe_ι (k : K' Γ' Γ) : ((ι Γ' Γ hle k : Γ') : SL(2, ℤ)) = ((k : Γ) : SL(2, ℤ)) := rfl

variable (x : Additive Γ →+ ℚ) (y' : Additive Γ' →+ ℚ)

def xres : Additive Γ' →+ ℚ := x.comp (MonoidHom.toAdditive (Subgroup.inclusion hle))

omit [Γ'.FiniteIndex] [Γ.FiniteIndex] in
@[scoped simp] theorem xres_apply (γ : Γ') :
    xres Γ' Γ hle x (Additive.ofMul γ) = x (Additive.ofMul (Subgroup.inclusion hle γ)) := rfl

noncomputable def yK : Additive (K' Γ' Γ) →+ ℚ :=
  y'.comp (MonoidHom.toAdditive (ι Γ' Γ hle).toMonoidHom)

omit [Γ'.FiniteIndex] [Γ.FiniteIndex] in
@[scoped simp] theorem yK_apply (k : K' Γ' Γ) :
    yK Γ' Γ hle y' (Additive.ofMul k) = y' (Additive.ofMul (ι Γ' Γ hle k)) := rfl

theorem trace_conj_T_zpow (z : SL(2, ℤ)) (n : ℤ) :
    ((z⁻¹ * ModularGroup.T ^ n * z : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul,
    ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
  ring

omit [Γ.FiniteIndex] in

theorem coe_cuspGen_pow (Q : Cusp Γ) (m : ℕ) :
    ((cuspGen Γ Q ^ m : Γ) : SL(2, ℤ)) = Q.out.out⁻¹ *
      ModularGroup.T ^ ((minimalPeriod (ModularGroup.T • ·) Q.out : ℤ) * m) * Q.out.out := by
  rw [Subgroup.coe_pow]
  have h := conj_pow (a := Q.out.out⁻¹)
    (b := ModularGroup.T ^ (minimalPeriod (ModularGroup.T • ·) Q.out)) (i := m)
  rw [inv_inv] at h
  change (Q.out.out⁻¹ * ModularGroup.T ^ minimalPeriod (ModularGroup.T • ·) Q.out * Q.out.out) ^ m = _
  rw [h, ← zpow_natCast, ← zpow_natCast, ← zpow_mul]

theorem trace_cuspGen_pow_conj (Q : Cusp Γ) (m : ℕ) (γ : Γ) :
    (((γ⁻¹ * cuspGen Γ Q ^ m * γ : Γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_cuspGen_pow]
  have : ((γ : SL(2, ℤ)))⁻¹ * (Q.out.out⁻¹ * ModularGroup.T ^
      ((minimalPeriod (ModularGroup.T • ·) Q.out : ℤ) * m) * Q.out.out) * γ =
      (Q.out.out * γ)⁻¹ * ModularGroup.T ^ ((minimalPeriod (ModularGroup.T • ·) Q.out : ℤ) * m) *
        (Q.out.out * γ) := by group
  rw [this, trace_conj_T_zpow]
  norm_num

theorem trace_cuspGen_pow (Q : Cusp Γ) (m : ℕ) :
    (((cuspGen Γ Q ^ m : Γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  have := trace_cuspGen_pow_conj Γ Q m 1
  simpa using this

variable {Γ' Γ hle x y'}
variable (hx : IsParabolicHom Γ x) (hy' : IsParabolicHom Γ' y')

omit [Γ'.FiniteIndex] [Γ.FiniteIndex] in

theorem isPrimitive_hK {H' : Γ' → ℚ} (hH' : IsPrimitive (xres Γ' Γ hle x) y' H') :
    IsPrimitive (res (K' Γ' Γ) x) (yK Γ' Γ hle y') (fun k => H' (ι Γ' Γ hle k)) := by
  intro k k'
  dsimp only
  rw [map_mul, hH']
  simp only [omega, xres_apply, yK_apply, res_apply]
  have h1 : Subgroup.inclusion hle (ι Γ' Γ hle k) = (k : Γ) := Subtype.ext rfl
  have h2 : Subgroup.inclusion hle (ι Γ' Γ hle k') = (k' : Γ) := Subtype.ext rfl
  rw [h1, h2]

noncomputable def Fext (H' : Γ' → ℚ) (s : SL(2, ℤ)) : ℚ := by
  classical
  exact if h : s ∈ Γ' then H' ⟨s, h⟩ else 0

omit [Γ'.FiniteIndex] in
theorem Fext_apply {H' : Γ' → ℚ} (γ : Γ') : Fext (Γ' := Γ') H' (γ : SL(2, ℤ)) = H' γ := by
  unfold Fext
  rw [dif_pos γ.2]

omit [Γ'.FiniteIndex] in
theorem Fext_apply' (H' : Γ' → ℚ) (s : SL(2, ℤ)) (hs : s ∈ Γ') :
    Fext (Γ' := Γ') H' s = H' ⟨s, hs⟩ := by
  unfold Fext
  rw [dif_pos hs]

include hx hy' in

theorem Fext_conj {H' : Γ' → ℚ} (hH' : IsPrimitive (xres Γ' Γ hle x) y' H') :
    ∀ p ∈ Γ', ∀ δ ∈ Γ', (p : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
      Fext (Γ' := Γ') H' (δ * p * δ⁻¹) = Fext (Γ' := Γ') H' p := by
  intro p hp δ hδ htr
  have hmem : δ * p * δ⁻¹ ∈ Γ' := Γ'.mul_mem (Γ'.mul_mem hδ hp) (Γ'.inv_mem hδ)
  rw [Fext_apply' H' _ hmem, Fext_apply' H' p hp]
  have helt : (⟨δ * p * δ⁻¹, hmem⟩ : Γ') = ⟨δ, hδ⟩ * ⟨p, hp⟩ * ⟨δ, hδ⟩⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, InvMemClass.coe_inv])
  rw [helt]
  refine isPrimitive_conj hH' ⟨p, hp⟩ ⟨δ, hδ⟩ ?_ ?_
  · rw [xres_apply]
    exact hx _ htr
  · exact hy' _ htr

include hx hy' hle in

theorem orbit_sum {H' : Γ' → ℚ} (hH' : IsPrimitive (xres Γ' Γ hle x) y' H') (Q : Cusp Γ)
    (q₀ : Γ ⧸ K' Γ' Γ) :
    ∑ j ∈ Finset.range (minimalPeriod (cuspGen Γ Q • ·) q₀),
        (H' (ι Γ' Γ hle (c (K' Γ' Γ) (cuspGen Γ Q) (cuspGen Γ Q ^ j • q₀))) -
          (av (K' Γ' Γ) x (cuspGen Γ Q ^ j • q₀) + av (K' Γ' Γ) x (cuspGen Γ Q ^ (j + 1) • q₀)) *
            yK Γ' Γ hle y' (Additive.ofMul (c (K' Γ' Γ) (cuspGen Γ Q) (cuspGen Γ Q ^ j • q₀)))) =
      Fext (Γ' := Γ') H' ((q₀.out⁻¹ * cuspGen Γ Q ^ minimalPeriod (cuspGen Γ Q • ·) q₀ *
        q₀.out : Γ) : SL(2, ℤ)) := by
  have hprim := isPrimitive_hK hH'
  have hxpow : ∀ j : ℕ, x (Additive.ofMul (cuspGen Γ Q ^ j)) = 0 :=
    fun j => hx _ (trace_cuspGen_pow Γ Q j)
  have hxu : x (Additive.ofMul (cuspGen Γ Q)) = 0 := by simpa using hxpow 1
  rw [sum_range_term hprim (cuspGen Γ Q) hxu hxpow q₀]

  have hPℓ : (P (K' Γ' Γ) (cuspGen Γ Q) q₀ (minimalPeriod (cuspGen Γ Q • ·) q₀) : Γ) =
      q₀.out⁻¹ * cuspGen Γ Q ^ minimalPeriod (cuspGen Γ Q • ·) q₀ * q₀.out := by
    rw [coe_P, (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr (dvd_refl _)]
  have hyπ : yK Γ' Γ hle y' (Additive.ofMul (P (K' Γ' Γ) (cuspGen Γ Q) q₀
      (minimalPeriod (cuspGen Γ Q • ·) q₀))) = 0 := by
    rw [yK_apply]
    apply hy'
    rw [coe_ι, hPℓ]
    exact trace_cuspGen_pow_conj Γ Q _ q₀.out
  have hK1 : H' (ι Γ' Γ hle 1) = 0 := isPrimitive_one (h := fun k => H' (ι Γ' Γ hle k)) hprim
  rw [P_zero, hK1, hyπ, ofMul_one, map_zero]
  simp only [mul_zero, sub_zero]

  have hmem : ((q₀.out⁻¹ * cuspGen Γ Q ^ minimalPeriod (cuspGen Γ Q • ·) q₀ * q₀.out : Γ) :
      SL(2, ℤ)) ∈ Γ' := by
    rw [← hPℓ]
    exact Subgroup.mem_subgroupOf.mp (P (K' Γ' Γ) (cuspGen Γ Q) q₀ _).2
  rw [Fext_apply' H' _ hmem]
  congr 1
  exact Subtype.ext (by rw [coe_ι, hPℓ])

include hx hy' hle in

theorem Htw_cuspGen {H' : Γ' → ℚ} (hH' : IsPrimitive (xres Γ' Γ hle x) y' H') (Q : Cusp Γ) :
    Htw (K' Γ' Γ) x (yK Γ' Γ hle y') (fun k => H' (ι Γ' Γ hle k)) (cuspGen Γ Q) =
      ∑ᶠ O : orbitRel.Quotient (Subgroup.zpowers (cuspGen Γ Q)) (Γ ⧸ K' Γ' Γ),
        Fext (Γ' := Γ') H' ((O.out.out⁻¹ * cuspGen Γ Q ^
          minimalPeriod (cuspGen Γ Q • ·) O.out * O.out.out : Γ) : SL(2, ℤ)) := by
  classical
  haveI : Fintype (orbitRel.Quotient (Subgroup.zpowers (cuspGen Γ Q)) (Γ ⧸ K' Γ' Γ)) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  unfold Htw A L
  rw [← Finset.sum_sub_distrib,
    ← (Subgroup.quotientEquivSigmaZMod (K' Γ' Γ) (cuspGen Γ Q)).symm.sum_comp, Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ (fun O => ?_)
  simp only [Subgroup.quotientEquivSigmaZMod_symm_apply]
  rw [sum_zmod_cast (minimalPeriod (cuspGen Γ Q • ·) O.out)
    (fun k => H' (ι Γ' Γ hle (c (K' Γ' Γ) (cuspGen Γ Q) (cuspGen Γ Q ^ k • O.out))) -
      (av (K' Γ' Γ) x (cuspGen Γ Q ^ k • O.out) + av (K' Γ' Γ) x (cuspGen Γ Q • cuspGen Γ Q ^ k • O.out)) *
        yK Γ' Γ hle y' (Additive.ofMul (c (K' Γ' Γ) (cuspGen Γ Q) (cuspGen Γ Q ^ k • O.out))))]
  have hstep : ∀ j : ℕ, cuspGen Γ Q • cuspGen Γ Q ^ j • O.out = cuspGen Γ Q ^ (j + 1) • O.out :=
    fun j => by rw [← mul_smul, ← pow_succ']
  simp only [zpow_natCast, hstep]
  exact orbit_sum hx hy' hH' Q O.out

include hx hy' hle in

theorem cuspSum_Htw {H' : Γ' → ℚ} (hH' : IsPrimitive (xres Γ' Γ hle x) y' H') :
    cuspSum Γ (Htw (K' Γ' Γ) x (yK Γ' Γ hle y') (fun k => H' (ι Γ' Γ hle k))) = cuspSum Γ' H' := by
  have h1 : cuspSum Γ' H' = cuspSum Γ' (fun γ => Fext (Γ' := Γ') H' γ) := by
    unfold cuspSum
    exact Finset.sum_congr rfl (fun Q' _ => (Fext_apply _).symm)
  rw [h1, ModularCurve.CupPairing.cuspSum_eq_sum_finsum_of_le Γ' Γ hle _ (Fext_conj hx hy' hH')]
  unfold cuspSum
  exact Finset.sum_congr rfl (fun Q _ => Htw_cuspGen hx hy' hH' Q)

include hx hy' hle in

theorem core :
    mult Γ * pair Γ x (CohCarrier.coresAdd (K' Γ' Γ) (yK Γ' Γ hle y')) =
      mult Γ' * pair Γ' (xres Γ' Γ hle x) y' := by
  obtain ⟨H', hH'⟩ := ModularCurve.CupPairing.exists_isPrimitive Γ' (xres Γ' Γ hle x) y'
  have hprim := isPrimitive_hK hH'
  rw [ModularCurve.CupPairing.pair_eq_cuspSum_div_of_isPrimitive Γ x _ _ (isPrimitive_Htw hprim),
    ModularCurve.CupPairing.pair_eq_cuspSum_div_of_isPrimitive Γ' _ y' H' hH',
    cuspSum_Htw hx hy' hH']
  have h1 := mult_ne_zero Γ
  have h2 := mult_ne_zero Γ'
  field_simp

end Core

section CardShape

theorem coresAdd_congr {Γ : Type*} [Group Γ] {K₁ K₂ : Subgroup Γ} [K₁.FiniteIndex] [K₂.FiniteIndex]
    (h : K₁ = K₂) (y₁ : Additive K₁ →+ ℚ) (y₂ : Additive K₂ →+ ℚ)
    (hy : ∀ (k : Γ) (h₁ : k ∈ K₁) (h₂ : k ∈ K₂),
      y₁ (Additive.ofMul ⟨k, h₁⟩) = y₂ (Additive.ofMul ⟨k, h₂⟩)) :
    CohCarrier.coresAdd K₁ y₁ = CohCarrier.coresAdd K₂ y₂ := by
  subst h
  have : y₁ = y₂ := by
    ext a
    exact hy (Additive.toMul a).1 (Additive.toMul a).2 (Additive.toMul a).2
  subst this
  rfl

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (K : Subgroup Γ) [K.FiniteIndex]

scoped instance finiteIndex_map_subtype : (K.map Γ.subtype).FiniteIndex := by
  constructor
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

omit [Γ.FiniteIndex] [K.FiniteIndex] in
theorem subgroupOf_map_subtype_eq : K' (K.map Γ.subtype) Γ = K :=
  Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective K

theorem main
    (x : Additive Γ →+ ℚ) (xK y' : Additive (K.map Γ.subtype) →+ ℚ) (yK₀ : Additive K →+ ℚ)
    (hx : IsParabolicHom Γ x) (hy' : IsParabolicHom (K.map Γ.subtype) y')
    (hxK : ∀ k : K, xK (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩) =
      x (Additive.ofMul (k : Γ)))
    (hyK : ∀ k : K, yK₀ (Additive.ofMul k) =
      y' (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩)) :
    mult Γ * pair Γ x (CohCarrier.coresAdd K yK₀) =
      mult (K.map Γ.subtype) * pair (K.map Γ.subtype) xK y' := by
  have hle : K.map Γ.subtype ≤ Γ := Subgroup.map_subtype_le K

  have hxres : xK = xres (K.map Γ.subtype) Γ hle x := by
    ext a
    obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp (Additive.toMul a).2
    have ha : Additive.toMul a = ⟨((⟨g, hg⟩ : K) : Γ), Subgroup.mem_map_of_mem Γ.subtype hg⟩ :=
      Subtype.ext hgeq.symm
    have hincl : Subgroup.inclusion hle (Additive.toMul a) = g := Subtype.ext hgeq.symm
    change xK (Additive.ofMul (Additive.toMul a)) =
      x (Additive.ofMul (Subgroup.inclusion hle (Additive.toMul a)))
    rw [hincl, ha]
    exact hxK ⟨g, hg⟩

  have hcor : CohCarrier.coresAdd K yK₀ =
      CohCarrier.coresAdd (K' (K.map Γ.subtype) Γ) (yK (K.map Γ.subtype) Γ hle y') := by
    refine (coresAdd_congr (subgroupOf_map_subtype_eq Γ K) (yK (K.map Γ.subtype) Γ hle y') yK₀
      ?_).symm
    intro k h₁ h₂
    rw [yK_apply, hyK ⟨k, h₂⟩]
    congr 2
  rw [hcor, hxres]
  exact core hx hy'

end CardShape

end ModularCurve.CupPairing.Proj
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.ModularCurve P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.ModularCurve.CupPairing P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.ModularCurve.CupPairing.Proj"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.ModularCurve P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.ModularCurve.CupPairing"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.ModularCurve"

theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (K : Subgroup Γ) [K.FiniteIndex]
    (x : Additive Γ →+ ℚ) (xK y' : Additive (K.map Γ.subtype) →+ ℚ) (yK : Additive K →+ ℚ)
    (hx : ModularCurve.Period.IsParabolicHom Γ x)
    (hy' : ModularCurve.Period.IsParabolicHom (K.map Γ.subtype) y')
    (hxK : ∀ k : K, xK (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩) =
      x (Additive.ofMul (k : Γ)))
    (hyK : ∀ k : K, yK (Additive.ofMul k) =
      y' (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩)) :
    ModularCurve.CupPairing.mult Γ * ModularCurve.CupPairing.pair Γ x (CohCarrier.coresAdd K yK) =
      ModularCurve.CupPairing.mult (K.map Γ.subtype) *
        ModularCurve.CupPairing.pair (K.map Γ.subtype) xK y' :=
  ModularCurve.CupPairing.Proj.main Γ K x xK y' yK hx hy' hxK hyK

end S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq
end P2MW
export P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq (solution)
