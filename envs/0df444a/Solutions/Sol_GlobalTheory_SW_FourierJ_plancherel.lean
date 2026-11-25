-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.plancherel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:04.936132+00:00
-- url     : https://prove2.me/submissions/dddd27ac-284b-4098-a847-e2c62ae8533f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_sum_ech_rep
import Theorems.Thm_GlobalTheory_SW_FourierJ_pr_sub_left
import Theorems.Thm_GlobalTheory_SW_FourierJ_ft_eq
import Theorems.Thm_GlobalTheory_SW_FourierJ_ft_level
import Theorems.Thm_GlobalTheory_SW_FourierJ_level_mul_conj
import Theorems.Thm_GlobalTheory_SW_FourierJ_intM_rep
import Theorems.Thm_GlobalTheory_SW_FourierJ_conj_ech
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_add
import Theorems.Thm_GlobalTheory_T_schwartzBruhatIntegral_eq_sum_residueRepresentatives


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution {R : ℕ} (hR : 0 < R) {φ ψ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ)
    (h' : HasLevel R ψ) (c : ℂ) (hc : c * conj c = 1) :
    ip (fun y => c * ft φ y) (fun y => c * ft ψ y) = ip φ ψ := by
  classical
  unfold ip
  rw [GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives κ ι R _ hR (level_mul_conj (ft_level hR h c) (ft_level hR h' c)),
    GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives κ ι R _ hR (level_mul_conj h h')]
  congr 1
  set V : ℂ := (R : ℂ) ^ (Fintype.card κ * Fintype.card ι) with hV
  have hV0 : V ≠ 0 := pow_ne_zero _ (by exact_mod_cast hR.ne')
  have hVc : conj V = V := by simp [hV]
  have key : ∀ n : κ → ι → Fin (R * R), c * ft φ (rep R n) * conj (c * ft ψ (rep R n)) =
      ∑ a : κ → ι → Fin (R * R), ∑ b : κ → ι → Fin (R * R),
        (V ^ 2)⁻¹ * (φ (rep R a) * conj (ψ (rep R b))) *
          ech (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) := by
    intro n
    rw [ft_eq hR h (intM_rep hR n), ft_eq hR h' (intM_rep hR n), ← hV, map_mul, map_mul, map_inv₀,
      hVc, map_sum]
    have e : ∀ A B : ℂ, c * (V⁻¹ * A) * (conj c * (V⁻¹ * B)) = (V ^ 2)⁻¹ * (A * B) := by
      intro A B
      calc _ = (c * conj c) * ((V ^ 2)⁻¹ * (A * B)) := by rw [sq, mul_inv]; ring
        _ = _ := by rw [hc, one_mul]
    rw [e, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) =
        pr (rep R a) (rep R n) + -pr (rep R b) (rep R n) := by
      rw [← sub_eq_add_neg, ← pr_sub_left]; rfl
    rw [this, ech_add, map_mul, conj_ech]; ring
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_ech_rep κ ι R hR, ← hV, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  field_simp
end GlobalTheory.SW.FourierJ
