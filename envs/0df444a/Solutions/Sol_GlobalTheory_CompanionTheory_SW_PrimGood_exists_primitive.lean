-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:24:32.438416+00:00
-- url     : https://prove2.me/submissions/63d1f24c-7f90-4e42-b80d-db107118493d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_core
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_exists_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_change_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_eventually_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_valued_algebraMap
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E), (a : Fv F v ⊗[F] E) • y ∈ latV b v ∧ z ∈ latV b v ∧ z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 := by
  intro F E _ _ _ _ _ σ hcm d b M
  obtain ⟨b₂, Δ, hΔ0, h0, h1⟩ := exists_basis hcm
  filter_upwards [change_basis b₂ b, GoodInt.eventually_eq_one Δ hΔ0,
    GoodInt.eventually_eq_one (2 : F) two_ne_zero] with v hch hΔ h2 y hy
  obtain ⟨z, hz⟩ := hy
  have hB0 : (Algebra.TensorProduct.basis (Fv F v) b₂) 0 = 1 := by
    rw [Algebra.TensorProduct.basis_apply, h0]; rfl
  have hB1 : (Algebra.TensorProduct.basis (Fv F v) b₂) 1 *
      (Algebra.TensorProduct.basis (Fv F v) b₂) 1 =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) Δ) := by
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, h1, mul_one]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E Δ = algebraMap F (Fv F v) Δ ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have h2' : Valued.v (2 : Fv F v) = 1 := by
    have := GoodInt.valued_algebraMap v (2 : F)
    rw [map_ofNat] at this
    rw [this, h2]
  have hΔ' : Valued.v (algebraMap F (Fv F v) Δ) = 1 := by
    rw [GoodInt.valued_algebraMap, hΔ]
  have hsq : ∀ x : Fv F v, Valued.v (x - 1) < 1 → IsSquare x := fun x hx =>
    GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v x (by
      rw [show (4 : Fv F v) = 2 * 2 by norm_num, map_mul, h2', one_mul]
      exact hx)
  obtain ⟨u, z', c1, c2, c3⟩ := core Valued.v hB0 hB1 hsq h2' hΔ' (y 0) z hz
  refine ⟨u, fun _ => z', ?_, ?_, ?_⟩
  · intro a i k
    obtain rfl := Subsingleton.elim a 0
    refine hch _ (fun l => ?_) k
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact c1 i l
  · intro a i k
    refine hch _ (fun l => ?_) k
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact c2 i l
  · simpa [dotProduct] using c3
end GlobalTheory.CompanionTheory.SW.PrimGood
