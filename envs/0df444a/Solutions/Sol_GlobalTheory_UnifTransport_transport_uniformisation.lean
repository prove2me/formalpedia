-- Prove2me | solution 1 for GlobalTheory.UnifTransport.transport_uniformisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:43.156795+00:00
-- url     : https://prove2.me/submissions/53294ddd-349c-40d2-b511-272431d72048

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolUnifReparam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TransportThetaLevelUniformisationCoordinates
import Theorems.Thm_GlobalTheory_UnifTransport_hermForm_eq_of_im

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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.UnifTransport
namespace GlobalTheory.UnifTransport
theorem _root_.solution :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (La' : Type) [AddCommGroup La'] (EF' : LinearMap.BilinForm ℤ La') (lam' : Fin (2 * g) → La') (ac' : J → La' → La') (Q' : La' →+ (Fin g → ℂ)) (Hm' : Matrix (Fin g) (Fin g) ℂ) (e : La ≃+ La') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (Function.Injective Q' ∧ DiscreteTopology (Q').range ∧ Submodule.span ℝ (Set.range Q') = ⊤ ∧ (Hm').IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧ ∀ x y, (hermForm Hm' (Q' x) (Q' y)).im = EF' x y) → (∀ x, Q' (e x) = h (Q x)) → (∀ x y, EF' (e x) (e y) = EF x y) → (∀ j x, e (ac j x) = ac' j (e x)) → (∀ i, ∃ y, e (lam i) = lam' i + k • y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF' x (ac' w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac' j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro o _ g k J b em w w' t La _ EF lam ac Q Hm La' _ EF' lam' ac' Q' Hm' e h hA hA' hQ hE hac hlam hU
  obtain ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩ := hU

  have hsym : ∀ x, h.symm (Q' x) = Q (e.symm x) := by
    intro x
    have hx := hQ (e.symm x)
    rw [e.apply_symm_apply] at hx
    rw [hx, LinearEquiv.symm_apply_apply]

  have him : ∀ x ∈ Set.range Q, ∀ y ∈ Set.range Q,
      (hermForm Hm' ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) x)
        ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) y)).im = (hermForm Hm x y).im := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [← hQ, ← hQ, hA'.2.2.2.2.2, hA.2.2.2.2.2, hE]
  have hH : ∀ a c, a ⬝ᵥ Hm'.mulVec (star c) = (h.symm a) ⬝ᵥ Hm.mulVec (star (h.symm c)) := by
    intro a c
    have hac' := hermForm_eq_of_im Hm Hm' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Set.range Q) hA.2.2.1 him
      (h.symm a) (h.symm c)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hac'
    exact hac'

  have hper : ∀ a v, v ∈ u.Λ → u.ex (a - v) = u.ex a := by
    intro a v hv
    have hsplit := u.ex_add (a - v) v
    rw [sub_add_cancel, (u.ker v).2 hv, _root_.mul_one] at hsplit
    exact hsplit.symm
  refine ⟨holUnifReparam u h.symm (fun _ => 1) (differentiable_const 1) (fun _ => one_ne_zero),
    fun l => χ' ⟨h.symm l, l.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold HolUnif.IsAH
    refine ⟨hA'.2.2.2.1, hA'.2.2.2.2.1, fun l => hAH.2.2.1 _, ?_⟩
    intro l i z hz
    simp only [holUnifReparam, div_one, map_add]
    rw [hH z l, hH l l]
    exact hAH.2.2.2 ⟨h.symm l, l.2⟩ i (h.symm z) hz
  · intro z
    show h.symm z ∈ u.Λ ↔ z ∈ Q'.range
    rw [hΛ]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      rw [hQ, ha, LinearEquiv.apply_symm_apply]
    · rintro ⟨c, rfl⟩
      exact ⟨e.symm c, (hsym c).symm⟩
  · intro x l hl
    have hpos : h.symm (l : Fin g → ℂ) = Q (e.symm x) := by rw [hl, hsym]
    have hform := hE (e.symm x) (ac w (e.symm x))
    rw [hac, e.apply_symm_apply] at hform
    rw [hform]
    exact hχ (e.symm x) ⟨h.symm l, l.2⟩ hpos
  · intro i
    obtain ⟨y, hy⟩ := hlam i
    have hl : lam' i = e (lam i) - k • y := eq_sub_of_add_eq hy.symm
    have hmem : (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) ∈ u.Λ := by
      by_cases hk : ((k : ℕ) : ℂ) = 0
      · rw [hk, mul_zero, zero_smul]
        exact zero_mem _
      · rw [inv_mul_cancel₀ hk, one_smul]
        exact (hΛ _).2 ⟨e.symm y, rfl⟩
    have hpt' : h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i))
        = ((k : ℕ) : ℂ)⁻¹ • Q (lam i) - (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) := by
      rw [hl, map_sub, map_nsmul, map_smul, map_sub, map_nsmul, hsym, hsym, e.symm_apply_apply, smul_sub,
        mul_smul, Nat.cast_smul_eq_nsmul]
    show (t.pt i).left = (u.ex (h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i)))).left
    rw [hpt', hper _ _ hmem, hpt]
  · intro j
    obtain ⟨F, hF1, hF2⟩ := hact j
    refine ⟨(h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ∘ₗ F ∘ₗ (h.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), ?_, ?_⟩
    · intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hsym, hF1, ← hQ, hac, e.apply_symm_apply]
    · intro z
      show u.ex (h.symm (h (F (h.symm z)))) = u.ex (h.symm z) ≫ t.act j
      rw [LinearEquiv.symm_apply_apply, hF2]
end GlobalTheory.UnifTransport
