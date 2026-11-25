-- Prove2me | solution 1 for GlobalTheory.FlagMahler.comp_le_Qy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:17.517692+00:00
-- url     : https://prove2.me/submissions/3cb979e6-2ed6-4e4a-abfa-fc3b7b9416ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_c_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlagMahler
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open Complex
open NumberField Module
open Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
open Complex
namespace GlobalTheory.FlagMahler
namespace _root_.GlobalTheory.FlagMahler
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ)
    (p : Fin r → E) (b : Fin r) :
    X.c τ * ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) b‖ ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y p := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy
  calc X.c τ * ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) b‖ ^ 2
      ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun a => ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) a‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_univ b)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ).le
    _ ≤ ∑ σ, X.c σ * ∑ a, ‖((y σ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb σ.1 p) a‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun σ => X.c σ * ∑ a, ‖((y σ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb σ.1 p) a‖ ^ 2)
          (fun σ _ => mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X σ).le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
          (Finset.mem_univ τ)
end _root_.GlobalTheory.FlagMahler
end GlobalTheory.FlagMahler
