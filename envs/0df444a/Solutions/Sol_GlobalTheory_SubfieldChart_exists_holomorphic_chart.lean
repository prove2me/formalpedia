-- Prove2me | solution 1 for GlobalTheory.SubfieldChart.exists_holomorphic_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:30.108088+00:00
-- url     : https://prove2.me/submissions/7f04586f-2444-42b3-9cda-34d7523546e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicChart
import Theorems.Thm_GlobalTheory_SubfieldChart_exists_chart_algebra
import Theorems.Thm_GlobalTheory_AffinePointValues_appLE_specMap_fromSpec
import Theorems.Thm_GlobalTheory_AffinePointValues_fromSpec_comp
import Theorems.Thm_GlobalTheory_AffinePointValues_specMap_appLE_fromSpec
import Theorems.Thm_GlobalTheory_HolChart_hol_of_affine
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


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
noncomputable section
open GlobalTheory GlobalTheory.SubfieldChart
namespace GlobalTheory.SubfieldChart
theorem _root_.solution :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B := by
  intro k _ σ X s d y₀ hX hy₀
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (y₀ (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (y₀ (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (y₀ (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : k →+* Γ(X, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hc : c.IsStandardSmoothOfRelativeDimension d :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hsm
  let _ : Algebra k ℂ := σ.toAlgebra
  let _ : Algebra k Γ(X, U) := c.toAlgebra
  have _ : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, U) := hc
  let pt : (Γ(X, U) →+* ℂ) → (Sp ℂ ⟶ X) := fun e =>
    Spec.map (CommRingCat.ofHom e : Γ(X, U) ⟶ CommRingCat.of ℂ) ≫ hU.fromSpec
  have hptU : ∀ e, ⊤ ≤ pt e ⁻¹ᵁ U := fun e p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hptv : ∀ e f, valAt' (pt e) U f = e f := fun e f => by
    rw [valAt', dif_pos (hptU e)]
    exact congrArg (fun ψ => ψ.hom f)
      (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom e) (hptU e))
  have hpts : ∀ e, pt e ≫ s = spMap (e.comp c) := fun e => by
    simp only [pt]
    rw [Category.assoc, AffinePointValues.fromSpec_comp hU s hle, ← Spec.map_comp]
    rfl
  have hsurj : ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U →
      ∃ e : Γ(X, U) →ₐ[k] ℂ, pt e.toRingHom = x := by
    intro x hxs hx
    let e : Γ(X, U) →+* ℂ := (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
    have he : pt e = x := AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x hx
    have h1 : spMap (e.comp c) = spMap σ := by rw [← hpts, he, hxs]
    have h2 : e.comp c = σ := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    exact ⟨{ e with commutes' := fun a => RingHom.congr_fun h2 a }, he⟩
  have hyU : ⊤ ≤ y₀ ⁻¹ᵁ U := ((valAt'_rules X y₀).1 U).2 hp
  obtain ⟨e, rfl⟩ := hsurj y₀ hy₀ hyU
  obtain ⟨W, p, n, r, ε, hW, hW0, hp0, hε, hpd, hpi, hps⟩ := exists_chart_algebra d e
  refine ⟨W, fun w => pt (p w).toRingHom, U, fun _ => 0, n, r, hW, hW0, by simp only [hp0],
    fun b _ => ?_, fun V f => ?_, fun w hw w' hw' h => hpi hw hw' ?_, hyU, ε, hε,
    fun x hxs hx hxe => ?_⟩
  · rw [hpts]
    congr 2
    exact RingHom.ext fun a => (p b).commutes a
  · exact HolChart.hol_of_affine valAt'_rules hU hW (fun w => pt (p w).toRingHom)
      (fun w _ => hptU _) (fun a => (hpd a).congr fun w _ => hptv _ a) V f
  · refine AlgHom.ext fun a => ?_
    have h1 := hptv (p w).toRingHom a
    have h' : pt (p w).toRingHom = pt (p w').toRingHom := h
    rw [h', hptv] at h1
    exact h1.symm
  · obtain ⟨e', rfl⟩ := hsurj x hxs hx
    obtain ⟨w, hw, h⟩ := hps e' fun i => by
      have := hxe i
      rw [hptv, hptv] at this
      exact this
    exact ⟨w, hw, by rw [h]⟩
end GlobalTheory.SubfieldChart
