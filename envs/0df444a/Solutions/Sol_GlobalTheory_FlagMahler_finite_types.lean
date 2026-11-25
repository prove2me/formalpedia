-- Prove2me | solution 1 for GlobalTheory.FlagMahler.finite_types
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:59.504431+00:00
-- url     : https://prove2.me/submissions/edcfb4d7-73f0-4556-a724-df62ce7446d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Theorems.Thm_GlobalTheory_FlagMahler_norm_herm_le
import Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
import Theorems.Thm_GlobalTheory_FlagMahler_finite_bounded
import Theorems.Thm_GlobalTheory_FlagMahler_finite_int_sq

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
namespace GlobalTheory.FlagMahler
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (C D : ℝ) (hD : 0 ≤ D) :
    (HermitianLatticeMaps.ty X '' {f : Basis ι ℤ X.Λ | ∃ y, IntegralBasisReduction.IsNormal X y ∧
      (∀ i, QuadraticLatticeForms.Qy X y (f i) ≤ C) ∧
      ∀ (v : X.Λ) (i : ι), ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ D * QuadraticLatticeForms.Qy X y v}).Finite := by
  have h1 := finite_bounded X fun τ => r * (C / X.c τ)
  have h2 := fun k : Free.ChooseBasisIndex ℤ (𝓞 E) =>
    finite_int_sq (D * ((∑ σ : X.Ψ, ‖σ.1 (RingOfIntegers.basis E k : E)‖ ^ 2) * C))
  have h3 := Set.Finite.pi' (fun _ : ι => Set.Finite.pi' fun _ : ι => h1)
  have h4 := Set.Finite.pi' (fun k => Set.Finite.pi' fun _ : ι => Set.Finite.pi' fun _ : ι => h2 k)
  refine (h3.prod h4).subset ?_
  rintro _ ⟨f, ⟨y, hy, hf, hr⟩, rfl⟩
  refine ⟨fun i j => ⟨X.Λ_int _ (f i).2 _ (f j).2, norm_herm_le X hy (hf i) (hf j)⟩,
    fun k i j => ?_⟩
  refine (hr _ j).trans (mul_le_mul_of_nonneg_left ?_ hD)
  rw [HermitianLatticeMaps.smul_coe]
  exact (Qy_smul_le X y _ _).trans (mul_le_mul_of_nonneg_left (hf i)
    (Finset.sum_nonneg fun _ _ => by positivity))
end GlobalTheory.FlagMahler
