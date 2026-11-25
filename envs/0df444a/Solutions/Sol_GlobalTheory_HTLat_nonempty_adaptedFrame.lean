-- Prove2me | solution 1 for GlobalTheory.HTLat.nonempty_adaptedFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:48:35.94129+00:00
-- url     : https://prove2.me/submissions/5107cce3-41ba-4c7b-b6d1-943be21835fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_HTLat_map_step
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
namespace GlobalTheory.HTLat
theorem _root_.solution {W U₁ : Submodule C U} (h : W ≤ U₁) [FiniteDimensional C U₁] :
    Nonempty (AdaptedFrame W U₁ (Module.finrank C U₁) (Module.finrank C W)) := by
  have : FiniteDimensional C W := Submodule.finiteDimensional_of_le h
  obtain ⟨Q, hQ⟩ := (W.comap U₁.subtype).exists_isCompl
  have hj : Module.finrank C (W.comap U₁.subtype) = Module.finrank C W :=
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq
  have hN : Module.finrank C W + Module.finrank C Q = Module.finrank C U₁ := by
    rw [← hj]; exact Submodule.finrank_add_eq_of_isCompl hQ
  let b₁ := Module.finBasisOfFinrankEq C _ hj
  let b₂ := Module.finBasis C Q
  let b := ((b₁.prod b₂).map (Submodule.prodEquivOfIsCompl _ _ hQ)).reindex
    (finSumFinEquiv.trans (finCongr hN))
  have hb : ∀ k, (U₁.subtype ∘ b) ((finSumFinEquiv.trans (finCongr hN)) (Sum.inl k)) =
      (U₁.subtype ∘ₗ (W.comap U₁.subtype).subtype) (b₁ k) := fun k => by simp [b]
  refine ⟨⟨U₁.subtype ∘ b, b.linearIndependent.map' _ U₁.ker_subtype, by omega, ?_, ?_⟩⟩
  · have h1 : (U₁.subtype ∘ b) '' {k | (k : ℕ) < Module.finrank C W} =
        (U₁.subtype ∘ₗ (W.comap U₁.subtype).subtype) '' Set.range b₁ := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨_, ⟨⟨k, hk⟩, rfl⟩, ?_⟩
        exact (hb ⟨k, hk⟩).symm.trans (congrArg (U₁.subtype ∘ b) (Fin.ext rfl))
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨(finSumFinEquiv.trans (finCongr hN)) (Sum.inl k), k.2, hb k⟩
    rw [step, h1, ← Submodule.map_span, b₁.span_eq, Submodule.map_comp, Submodule.map_subtype_top,
      Submodule.map_comap_subtype, inf_eq_right.2 h]
  · have : {k : Fin (Module.finrank C U₁) | (k : ℕ) < Module.finrank C U₁} = Set.univ :=
      Set.eq_univ_of_forall fun k => k.2
    rw [← map_step, step, this, Set.image_univ, b.span_eq, Submodule.map_subtype_top]
end GlobalTheory.HTLat
