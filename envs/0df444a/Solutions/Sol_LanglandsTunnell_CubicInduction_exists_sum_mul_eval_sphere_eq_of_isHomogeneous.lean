-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_sum_mul_eval_sphere_eq_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8aa87c38-f3e5-58c5-bfc5-28d066687ee0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous

set_option autoImplicit false

namespace WsC
namespace ZS

open MvPolynomial

noncomputable section

abbrev R3 := MvPolynomial (Fin 3) ℂ

def cpt (x : Fin 3 → ℝ) : Fin 3 → ℂ := fun a => ((x a : ℝ) : ℂ)

theorem eval_smul_of_isHomogeneous {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) (r : ℂ)
    (u : Fin 3 → ℂ) : eval (r • u) p = r ^ ℓ * eval u p := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdeg : ∑ i, d i = ℓ := by
    have h1 : Finsupp.weight (1 : Fin 3 → ℕ) d = ℓ := hp (mem_support_iff.mp hd)
    rw [← Finsupp.degree_eq_sum]
    rw [Finsupp.degree_eq_weight_one]
    exact h1
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem eval_real_eq_zero {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ)
    (h : ∀ u : Fin 3 → ℝ, ∑ a : Fin 3, u a ^ 2 = 1 → eval (cpt u) p = 0)
    (x : Fin 3 → ℝ) : eval (cpt x) p = 0 := by

  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    have hc : p = C (p.coeff 0) := by
      rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
      exact hp
    have hu : ∑ a : Fin 3, (![1, 0, 0] : Fin 3 → ℝ) a ^ 2 = 1 := by
      simp [Fin.sum_univ_three]
    have := h _ hu
    rw [hc, eval_C] at this
    rw [hc, eval_C, this]
  · set s : ℝ := ∑ a : Fin 3, x a ^ 2 with hs
    by_cases hs0 : s = 0
    ·
      have hx : ∀ a, x a = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (x a))).mp (hs ▸ hs0)
        intro a
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (this a (Finset.mem_univ a))
      have hx0 : cpt x = 0 := by
        funext a; simp [cpt, hx a]
      rw [hx0, show eval (0 : Fin 3 → ℂ) p = constantCoeff p from by rw [eval_zero],
        constantCoeff_eq, hp.coeff_eq_zero]
      simp only [map_zero]
      omega
    · have hspos : 0 < s := lt_of_le_of_ne (Finset.sum_nonneg (fun a _ => sq_nonneg (x a)))
        (Ne.symm hs0)
      set r : ℝ := Real.sqrt s with hr
      have hrpos : 0 < r := Real.sqrt_pos.mpr hspos
      have hr2 : r ^ 2 = s := Real.sq_sqrt hspos.le
      set u : Fin 3 → ℝ := fun a => x a / r with hu
      have hu1 : ∑ a : Fin 3, u a ^ 2 = 1 := by
        simp only [hu, div_pow, ← Finset.sum_div]
        rw [hr2]
        exact div_self hs0
      have hxu : cpt x = (r : ℂ) • cpt u := by
        funext a
        simp only [cpt, hu, Pi.smul_apply, smul_eq_mul, Complex.ofReal_div]
        field_simp [Complex.ofReal_ne_zero.mpr hrpos.ne']
      rw [hxu, eval_smul_of_isHomogeneous hp, h u hu1, mul_zero]

theorem eq_zero_of_eval_sphere {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ)
    (h : ∀ u : Fin 3 → ℝ, ∑ a : Fin 3, u a ^ 2 = 1 → eval (cpt u) p = 0) : p = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset p
    (fun i => (Finset.range (p.degreeOf i + 1)).image (fun k : ℕ => (k : ℂ))) ?_ ?_
  · intro i
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    omega
  · intro z hz
    have hreal : ∀ i, ∃ k : ℕ, z i = (k : ℂ) := by
      intro i
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hz i)
      exact ⟨k, hk.symm⟩
    choose k hk using hreal
    have hz' : z = cpt (fun i => (k i : ℝ)) := by
      funext i; simp [cpt, hk i]
    rw [hz']
    exact eval_real_eq_zero hp h _

abbrev V (ℓ : ℕ) : Submodule ℂ R3 := homogeneousSubmodule (Fin 3) ℂ ℓ

scoped instance V_fd (ℓ : ℕ) : FiniteDimensional ℂ (V ℓ) :=
  Submodule.finiteDimensional_of_le (S₂ := restrictTotalDegree (Fin 3) ℂ ℓ)
    (fun p hp => (mem_restrictTotalDegree _ _ _).mpr (IsHomogeneous.totalDegree_le hp))

def evL (pt : Fin 3 → ℂ) : R3 →ₗ[ℂ] ℂ where
  toFun p := eval pt p
  map_add' p q := map_add _ _ _
  map_smul' c p := by simp only [smul_eval, smul_eq_mul, RingHom.id_apply]

theorem evL_apply (pt : Fin 3 → ℂ) (p : R3) : evL pt p = eval pt p := rfl

def F (ℓ : ℕ) (u : Fin 3 → ℝ) : Module.Dual ℂ (V ℓ) := (evL (cpt u)).comp (V ℓ).subtype

theorem F_apply (ℓ : ℕ) (u : Fin 3 → ℝ) (v : V ℓ) : F ℓ u v = eval (cpt u) (v : R3) := rfl

def sphere : Set (Fin 3 → ℝ) := {u | ∑ a : Fin 3, u a ^ 2 = 1}

theorem span_F_eq_top (ℓ : ℕ) : Submodule.span ℂ (F ℓ '' sphere) = ⊤ := by
  set W : Submodule ℂ (Module.Dual ℂ (V ℓ)) := Submodule.span ℂ (F ℓ '' sphere) with hW
  have hco : W.dualCoannihilator = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    have hv0 : (v : R3) = 0 := by
      refine eq_zero_of_eval_sphere v.2 (fun u hu => ?_)
      rw [← F_apply]
      exact hv _ (Submodule.subset_span ⟨u, hu, rfl⟩)
    exact Subtype.ext hv0
  have := (Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)).symm
  rw [hco, Submodule.dualAnnihilator_bot] at this
  exact this

theorem main (ℓ : ℕ) (Λ : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] ℂ) :
    ∃ (N : ℕ) (u : Fin N → Fin 3 → ℝ) (c : Fin N → ℂ),
      (∀ n : Fin N, ∑ a : Fin 3, u n a ^ 2 = 1) ∧
      ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
        Λ p = ∑ n : Fin N, c n * MvPolynomial.eval (fun a : Fin 3 => ((u n a : ℝ) : ℂ)) p := by
  have hmem : Λ.comp (V ℓ).subtype ∈ Submodule.span ℂ (F ℓ '' sphere) := by
    rw [span_F_eq_top]; trivial
  obtain ⟨N, f, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  have hg : ∀ n : Fin N, ∃ u : Fin 3 → ℝ, u ∈ sphere ∧ F ℓ u = (g n : Module.Dual ℂ (V ℓ)) :=
    fun n => (g n).2
  choose u hu using hg
  refine ⟨N, u, f, fun n => (hu n).1, fun p hp => ?_⟩
  have := congrArg (fun φ : Module.Dual ℂ (V ℓ) => φ ⟨p, hp⟩) hsum
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
  rw [← this, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [LinearMap.smul_apply, ← (hu n).2, F_apply, smul_eq_mul]
  rfl

end

end WsC.ZS
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous.WsC P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous.WsC.ZS"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous.WsC"

theorem solution
    (ℓ : ℕ) (Λ : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] ℂ) :
    ∃ (N : ℕ) (u : Fin N → Fin 3 → ℝ) (c : Fin N → ℂ),
      (∀ n : Fin N, ∑ a : Fin 3, u n a ^ 2 = 1) ∧
      ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
        Λ p = ∑ n : Fin N, c n * MvPolynomial.eval (fun a : Fin 3 => ((u n a : ℝ) : ℂ)) p := by
  exact WsC.ZS.main ℓ Λ

end S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous (solution)
