-- Prove2me | solution 1 for GlobalTheory.HolPeriods.Uniformises.comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:01.481877+00:00
-- url     : https://prove2.me/submissions/3478aa94-2ecc-4485-9553-f5caa7de4695

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsHolToPointAndExp
import Theorems.Thm_GlobalTheory_HolPeriods_isDerivAt0_comp_equiv
import Theorems.Thm_GlobalTheory_HolPeriods_isHolTo_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolPeriods
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
namespace GlobalTheory.HolPeriods
namespace Uniformises
theorem _root_.solution {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {D' : Datum H}
    {t : D.La →ₗ[𝓞 E] D'.La} {P P' : D'.La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.X}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)} (h : Uniformises Xo σ ty D' t P' y e) (hP : IsPeriod D' ty P)
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ a, P' a = k (P a))
    (hlin : ∀ (a : 𝓞 E) z, k (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * k z i) :
    Uniformises Xo σ ty D' t P y (fun z => e (k z)) := by
  obtain ⟨h1, -, ⟨h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12⟩ := h
  refine ⟨h1, hP, ⟨fun z w => by simp only [map_add, h3], h4.comp k.surjective, ?_, fun w => ?_, fun v hv => ?_⟩,
    fun z => ?_, fun a z => by simp only [hlin, h9], fun n a a₂ c hn hc => ?_, fun a ha => ?_, fun a => ?_⟩
  · have hd : DifferentiableOn ℂ (fun z => k z) Set.univ :=
      k.toContinuousLinearEquiv.differentiable.differentiableOn
    have := isHolTo_comp h5 isOpen_univ hd (Set.mapsTo_univ _ _)
    exact this
  · simp only [isDerivAt0_comp_equiv (fun z => (e z).left) k]
    exact h6 _
  · simp only [isDerivAt0_comp_equiv (fun z => (e z).left) k]
    obtain ⟨w, hw, hu⟩ := h7 v (by simpa only [map_zero] using hv)
    refine ⟨k.symm w, by simpa only [LinearEquiv.apply_symm_apply] using hw, fun w' hw' => ?_⟩
    rw [← hu _ hw', LinearEquiv.symm_apply_apply]
  · rw [h8]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, k.injective (by rw [← hk, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hk a⟩
  · simp only [map_smul, ← hk]
    exact h10 n a a₂ c hn hc
  · simp only [map_smul, ← hk]
    exact h11 a ha
  · simp only [map_smul, ← hk]
    exact h12 a
end Uniformises
end GlobalTheory.HolPeriods
