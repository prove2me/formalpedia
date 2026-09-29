-- Prove2me | solution 1 for ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/eb6d2849-e731-5976-beae-1526a6f37f51

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_span_frickeRational_E4_pow_E6_pow_eq_top
import Theorems.Thm_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup
open scoped Real MatrixGroups ModularForm

namespace GammaOneCyclotomicEvenMF

def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp at h1 h2
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 τ.im_pos.ne'
    subst hs
    simp at h2
    exact ⟨rfl, h2⟩

theorem tauPair_spec (τ : ℍ) : (tauPair τ).ω₁ = (τ : ℂ) ∧ (tauPair τ).ω₂ = 1 := ⟨rfl, rfl⟩

variable (N : ℕ)

def WW (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

def fricke (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ

def jf (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

theorem WW_spec (v : Fin 2 → ZMod N) (τ : ℍ) : WW N v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)) := rfl

theorem fricke_spec (v : Fin 2 → ZMod N) (τ : ℍ) : fricke N v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ := rfl

theorem jf_spec (τ : ℍ) : jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := rfl

def kN : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}

theorem kN_eq : kN N = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := rfl

theorem Gamma_le_Gamma1 : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem exists_abm {k : ℤ} (hk : Even k) :
    ∃ a b m : ℕ, k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ) := by
  obtain ⟨r, rfl⟩ := hk
  rcases le_or_gt 0 r with hr | hr
  · refine ⟨r.toNat, r.toNat, r.toNat, ?_⟩
    rw [Int.toNat_of_nonneg hr]; ring
  · refine ⟨2 * (-r).toNat, (-r).toNat, (-r).toNat, ?_⟩
    have h : ((-r).toNat : ℤ) = -r := Int.toNat_of_nonneg (by omega)
    push_cast
    rw [h]; ring

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem main (N : ℕ) [NeZero N] (k : ℤ) (hk : Even k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (ModularForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ kN N := by
  classical
  obtain ⟨a, b, m, habm⟩ := exists_abm hk

  set S : Set (ModularForm (Γ₁ℝ N) k) := {f : ModularForm (Γ₁ℝ N) k |
      ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        (∀ mo, P.coeff mo ∈ kN N) ∧ (∀ mo, Q.coeff mo ∈ kN N) ∧
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke N v.1) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke N v.1) Q τ =
          ModularForm.discriminant τ ^ m *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke N v.1) P τ} with hS
  have hspan : Submodule.span ℂ S = ⊤ :=
    ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top N tauPair tauPair_spec (WW N) (WW_spec N)
      (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) (Gamma1 N) (Gamma_le_Gamma1 N) k a b m habm

  have hcoef : ∀ f ∈ S, ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ kN N := by
    rintro f ⟨P, Q, hP, hQ, hQ0, hid⟩ n
    exact ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational N tauPair tauPair_spec (WW N) (WW_spec N)
      (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) k a b m f P Q hP hQ
      hQ0 hid n

  haveI : FiniteDimensional ℂ (ModularForm (Γ₁ℝ N) k) := ModularForm.finiteDimensional_of_isArithmetic _ k
  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent ℂ S
  have ht_fin : t.Finite := LinearIndependent.set_finite_of_isNoetherian ht_ind
  letI : Fintype t := ht_fin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → ModularForm (Γ₁ℝ N) k)) := by
    rw [Subtype.range_coe, ht_span, hspan]
  let B : Module.Basis t ℂ (ModularForm (Γ₁ℝ N) k) := Module.Basis.mk ht_ind htop
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, B.reindex e, fun i n => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact hcoef _ (ht_sub (e.symm i).2) n

end GammaOneCyclotomicEvenMF

end

theorem solution (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} :=
  GammaOneCyclotomicEvenMF.main N k hk

end S_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even
end P2MW
export P2MW.S_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even (solution)
