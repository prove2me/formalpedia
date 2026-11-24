-- Prove2me | solution 1 for GlobalTheory.CMNormIdentity.exists_eigen_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:00.810074+00:00
-- url     : https://prove2.me/submissions/c304c3bb-6fb2-4b71-86e3-c78c1cd7923f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingSmul
import Theorems.Thm_GlobalTheory_EigenNorm_eq_zero_of_sum_embedding_mul
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CMNormIdentity
namespace GlobalTheory.CMNormIdentity
theorem _root_.solution {E : Type} [Field E] [NumberField E] {L V : Type} [AddCommGroup L] [Module (𝓞 E) L]
    [AddCommGroup V] [Module ℂ V] (X : L →+ V) :
    ∃ x : (E →+* ℂ) → L →+ V, ∀ (s : 𝓞 E) a, X (s • a) = ∑ τ : E →+* ℂ, τ (s : E) • x τ a := by
  classical
  let b := RingOfIntegers.basis E
  have hli : LinearIndependent ℂ (fun (τ : E →+* ℂ) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) => τ (b i : E)) := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    refine EigenNorm.eq_zero_of_sum_embedding_mul f fun s => ?_
    have hb : ∀ i, ∑ τ : E →+* ℂ, τ (b i : E) * f τ = 0 := fun i => by
      simpa [mul_comm] using congrFun hf i
    rw [← b.sum_repr s]
    simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, map_zsmul, Finset.sum_mul, smul_mul_assoc] at hb ⊢
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, hb, smul_zero, Finset.sum_const_zero]
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Embeddings.card, Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank])
  have hc : ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 E), ∃ c : (E →+* ℂ) → ℂ,
      ∑ τ, c τ • (fun j => τ (b j : E)) = Pi.single i 1 := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsp ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨fun τ => AddMonoidHom.mk' (fun a => ∑ i, c i τ • X (b i • a)) fun a a' => by
    simp [smul_add, Finset.sum_add_distrib], fun s a => ?_⟩
  have hb : ∀ j, X (b j • a) = ∑ τ : E →+* ℂ, τ (b j : E) • ∑ i, c i τ • X (b i • a) := fun j => by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ τ : E →+* ℂ, τ (b j : E) * c i τ = (Pi.single i 1 : _ → ℂ) j := fun i => by
      rw [← hc i]
      simp [mul_comm]
    simp only [← Finset.sum_smul, this]
    simp [Pi.single_apply]
  simp only [AddMonoidHom.mk'_apply]
  conv_lhs => rw [← b.sum_repr s]
  conv_rhs => rw [← b.sum_repr s]
  simp only [Finset.sum_smul, smul_assoc, map_sum, map_zsmul, RingOfIntegers.coe_eq_algebraMap] at hb ⊢
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.smul_sum, ← hb]
end GlobalTheory.CMNormIdentity
