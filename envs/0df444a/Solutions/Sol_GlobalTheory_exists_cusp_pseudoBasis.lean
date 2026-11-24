-- Prove2me | solution 1 for GlobalTheory.exists_cusp_pseudoBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:12.158672+00:00
-- url     : https://prove2.me/submissions/afab0f9d-bb3e-4735-a275-91ec17e93532

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCuspPseudoBasisAdaptedLattice
import Theorems.Thm_GlobalTheory_herm_comb_eq_zero_of_iso
import Theorems.Thm_Formalism_L2_Pj_FJ_exists_crdMap
import Theorems.Thm_Formalism_L2_Pj_FJ_exists_smul_mem
import Theorems.Thm_GlobalTheory_exists_pseudoBasis_adapted
import Theorems.Thm_UpperTheory_Reformulated_B_LocalSituation_exists_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu₀ : FJ.CuspFD X ρ), ∃ (cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), IsUnit P.det ∧ (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) ∧ (∀ b, cc' b ≠ 0) ∧ (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) := by
  intro E _ _ _ r ρ X cu₀
  classical
  let T : (Fin ρ → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E cu₀.e
  have hT : ∀ v, T v = ∑ i, v i • cu₀.e i := fun v => Fintype.linearCombination_apply E cu₀.e v
  obtain ⟨Ψ, hΨ⟩ := FJ.exists_crdMap cu₀
  have hinj : Function.Injective T := by
    refine Function.LeftInverse.injective (g := Ψ) fun v => ?_
    rw [hT, hΨ]
  let L : Submodule (𝓞 E) (Fin ρ → E) := X.Λ.comap (T.restrictScalars (𝓞 E))
  have hL : ∀ v, v ∈ L ↔ T v ∈ X.Λ := fun v => Iff.rfl
  have hfg : L.FG := by
    refine Submodule.FG.of_le (X.Λ_fg.map (Ψ.restrictScalars (𝓞 E))) fun v hv => ?_
    refine ⟨T v, (hL v).1 hv, ?_⟩
    show Ψ (T v) = v
    rw [hT, hΨ]
  have hsp : Submodule.span E (L : Set (Fin ρ → E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨c, hc, hcw⟩ := FJ.exists_smul_mem X (T w)
    have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h =>
      hc (IsFractionRing.injective (𝓞 E) E (by rw [map_zero]; exact h))
    have hm : algebraMap (𝓞 E) E c • w ∈ L := by
      rw [hL, map_smul, algebraMap_smul]
      exact hcw
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin ρ → E))) (algebraMap (𝓞 E) E c)⁻¹
      (Submodule.subset_span hm)
    rwa [smul_smul, inv_mul_cancel₀ hcE, one_smul] at this
  obtain ⟨s, e, c, hc, hmem, -⟩ := exists_pseudoBasis_adapted E ρ L ⊤ hfg hsp
  have hsum : ∀ a : Fin ρ → E, ∑ b, a b • T (e b) = T (∑ b, a b • e b) := by
    intro a
    simp only [map_sum, map_smul]
  refine ⟨⟨fun b => T (e b), e.linearIndependent.map' T (LinearMap.ker_eq_bot.2 hinj), ?_⟩,
    (e.toMatrix (Pi.basisFun E (Fin ρ)))ᵀ, c, ?_, ?_, hc, ?_⟩
  · intro a b
    simp only [hT]
    exact herm_comb_eq_zero_of_iso _ _ cu₀.iso _ _
  · rw [Matrix.det_transpose]
    exact e.isUnit_det _
  · intro a
    show cu₀.e a = ∑ b, e.repr (Pi.basisFun E (Fin ρ) a) b • T (e b)
    rw [hsum, e.sum_repr, hT]
    simp [Pi.single_apply]
  · intro a
    show ∑ b, a b • T (e b) ∈ X.Λ ↔ _
    rw [hsum, ← hL, hmem]
    simp only [e.repr_sum_self]
end GlobalTheory
