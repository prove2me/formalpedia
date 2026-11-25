-- Prove2me | solution 1 for GlobalTheory.SW.WeilAct.exists_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:58.503724+00:00
-- url     : https://prove2.me/submissions/907cbf3f-0b95-4f3c-845a-31e52c608dfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Theorems.Thm_GlobalTheory_SW_WeilAct_thH_smul
import Theorems.Thm_GlobalTheory_SW_WeilAct_ip_ofQ
import Theorems.Thm_GlobalTheory_SW_WeilAct_ip_smul
import Theorems.Thm_GlobalTheory_SW_TransComp_key
import Theorems.Thm_GlobalTheory_SW_thH_eq_thS_dictionary
import Theorems.Thm_GlobalTheory_T_exists_rational_symplectic_of_unitary_cmField
import Theorems.Thm_GlobalTheory_T_rationalSchwartzBruhat_algebra_integral_linear
import Theorems.Thm_P2M_GlobalTheory_T_exists_weil_of_symplectic__5d7707bdca5b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.WeilAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.WeilAct
theorem _root_.solution (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N) :
    ∃ W : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ, ∀ φ, IsSB φ →
      IsSB (W φ) ∧ TransH Ψ γ φ (W φ) ∧ ∀ φ', IsSB φ' → ip (W φ) (W φ') = ip φ φ' := by
  obtain ⟨hb, hS, -, hth, hsb⟩ := thH_eq_thS_dictionary E Ψ hΨ n N
  obtain ⟨σ, hσ, c, hc, hdict⟩ := GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField E Ψ hΨ n N γ hγ
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weil_of_symplectic' (Fin n) (QI E N) σ (by simpa using hn) hσ
  obtain ⟨d, hd, hip⟩ := ip_ofQ E n N
  let e := Equiv.ofBijective _ hb
  let V : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ := fun φ x =>
    ω (fun m => φ (ofQ m)) (e.symm x)
  have hV : ∀ φ, (fun m => V φ (ofQ m)) = ω fun m => φ (ofQ m) := fun φ => by
    funext m
    exact congrArg _ (e.symm_apply_apply m)
  have hVsb : ∀ φ, IsSB φ → IsSB (V φ) := fun φ hφ => by
    rw [hsb, hV]
    exact (hω _ ((hsb φ).1 hφ)).1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨fun φ => (c ^ (n / 2))⁻¹ • V φ, fun φ hφ => ⟨?_, ?_, fun φ' hφ' => ?_⟩⟩
  · exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hVsb φ hφ) (hVsb φ hφ)).2.1 _
  · intro Z hZ z z'
    obtain ⟨h1, h2, h3⟩ := hdict Z hZ
    obtain ⟨h3, h4⟩ := h3 z z'
    have key := (hω _ ((hsb φ).1 hφ)).2.1 _ (hS Z hZ) (zetaOf Ψ z z')
    rw [thH_smul, hth, hth, hV, ← h1, h3, key, h2, Finset.sum_congr rfl fun k _ => h4 k,
      Fintype.card_fin, mul_pow, ← Finset.prod_pow, hFac, Finset.prod_mul_distrib,
      ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    have hp : ∀ τ : Ψ, ((hDen Ψ γ Z τ).det ^ 2) ^ (n / 2) = (hDen Ψ γ Z τ).det ^ n := fun τ => by
      rw [← pow_mul, Nat.mul_div_cancel' hn.two_dvd]
    simp only [hp]
    have := pow_ne_zero (n / 2) hc0
    rw [← mul_assoc (π * I : ℂ) 2, show (π * I * 2 : ℂ) = 2 * π * I by ring]
    field_simp
  · rw [ip_smul (by simp [hc])]
    refine mul_left_cancel₀ hd ?_
    rw [← hip _ _ (hVsb φ hφ) (hVsb φ' hφ'), ← hip _ _ hφ hφ', hV, hV]
    exact (hω _ ((hsb φ).1 hφ)).2.2 _ ((hsb φ').1 hφ')
end GlobalTheory.SW.WeilAct
