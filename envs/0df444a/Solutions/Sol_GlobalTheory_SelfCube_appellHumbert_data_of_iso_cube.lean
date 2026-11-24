-- Prove2me | solution 1 for GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:39.55745+00:00
-- url     : https://prove2.me/submissions/987c36f3-df9b-4950-94e6-5cdbb85a48db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Theorems.Thm_GlobalTheory_SelfCube_form_eq_zero_of_unit
import Theorems.Thm_GlobalTheory_SelfCube_herm_add_left
import Theorems.Thm_GlobalTheory_SelfCube_herm_add_right
import Theorems.Thm_GlobalTheory_SelfCube_herm_smul_left
import Theorems.Thm_GlobalTheory_SelfCube_herm_zero_left
import Theorems.Thm_GlobalTheory_SelfCube_herm_conj
import Theorems.Thm_GlobalTheory_SelfCube_herm_continuous
import Theorems.Thm_GlobalTheory_SelfCube_prod_finset_fin_two
import Theorems.Thm_GlobalTheory_SelfCube_exists_unit_of_iso
import Theorems.Thm_GlobalTheory_SelfCube_semicharacter_rule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
open GlobalTheory.CubeValues
namespace GlobalTheory.SelfCube
theorem _root_.solution :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (P : Out.PolAV (Sp ℂ)) [IsCommMonObj P.A] (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (f : P.A ⟶ P.A) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u.Λ), (∀ z, u.ex (F z) = u.ex z ≫ f) → LBIso P.L (cubeLB P.A ![𝟙 P.A, f] P.L) → (∀ z w, hermForm Hm z w = hermForm Hm z (F w) + hermForm Hm (F z) w) ∧ ∀ l : u.Λ, χ l = (-1) ^ Ef l ⟨F l, hF l l.2⟩) := by
  classical
  intro hv hh P _ u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ f F hF hexF hiso
  have hv' : ValueRules := hv
  clear hv hh
  have : DiscreteTopology u.Λ := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hfr' : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z =
      (χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)) * u.fr i (z + l) := hfr
  have hχne : ∀ l, χ l ≠ 0 := fun l h => by
    have h1 := hχ l
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hχ0 : χ 0 = 1 := by
    have h := semicharacter_rule hv' P.isLB u hH χ hfr' 0 0 0 (by simp [herm_zero_left])
    simp only [add_zero, zpow_zero, _root_.mul_one] at h
    exact mul_right_cancel₀ (hχne 0) (h.symm.trans (_root_.one_mul _).symm)
  obtain ⟨a, ha_def⟩ : ∃ a : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, a = fun l z =>
      if h : l ∈ u.Λ then χ ⟨l, h⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) else 1 :=
    ⟨_, rfl⟩
  have ha_mem : ∀ l (hl : l ∈ u.Λ) z,
      a l z = χ ⟨l, hl⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) := fun l hl z => by
    simp only [ha_def, dif_pos hl]
  have ha : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = a l z * u.fr i (z + l) :=
    fun l hl i z hz => by rw [ha_mem l hl]; exact hfr' ⟨l, hl⟩ i z hz
  obtain ⟨ψ, hψd, hψ0, hψp⟩ := exists_unit_of_iso hv' P.isLB u ![𝟙 P.A, f] ![LinearMap.id, F]
    (by intro k; fin_cases k
        · simp
        · simpa using hF)
    (by intro k z; fin_cases k
        · simp
        · simp [hexF])
    a ha hiso
  have hprod : ∀ z l, l ∈ u.Λ → ψ (z + l) * a l z =
      a 0 0 * (a l z)⁻¹ * (a (F l) (F z))⁻¹ * a (l + F l) (z + F z) * ψ z := by
    intro z l hl
    rw [hψp z l hl, prod_finset_fin_two (fun J => a (∑ k ∈ J, (![LinearMap.id, F] k) l)
      (∑ k ∈ J, (![LinearMap.id, F] k) z) ^ ((-1 : ℤ) ^ (2 - J.card)))]
    simp
  obtain ⟨D, hD⟩ : ∃ D : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, D = fun z w =>
      hermForm Hm z (F w) + hermForm Hm (F z) w - hermForm Hm z w := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : u.Λ → ℂ, ρ = fun l => χ (l + ⟨F l, hF l l.2⟩) * (χ l)⁻¹ * (χ l)⁻¹ *
      (χ ⟨F l, hF l l.2⟩)⁻¹ := ⟨_, rfl⟩
  have hFc : Continuous F := F.continuous_of_finiteDimensional
  have hc : Continuous fun z => D z z := by
    simp only [hD]
    exact ((herm_continuous Hm continuous_id hFc).add (herm_continuous Hm hFc continuous_id)).sub
      (herm_continuous Hm continuous_id continuous_id)
  have hadd : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [hD, herm_add_left, map_add]; ring
  have hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w := fun t z w => by
    simp only [hD, herm_smul_left, map_smul]; ring
  have hst : ∀ z w, D w z = starRingEnd ℂ (D z w) := fun z w => by
    simp only [hD, map_sub, map_add, ← herm_conj Hm hH]; ring
  have hρ : ∀ l, ‖ρ l‖ = 1 := fun l => by
    simp [hρdef, hχ]
  have hper : ∀ z (l : u.Λ), ψ (z + l) = ρ l * cexp (π * D z l + π / 2 * D l l) * ψ z := by
    intro z l
    have hl := l.2
    have hFl := hF l l.2
    have hlF : (l : Fin P.g → ℂ) + F l ∈ u.Λ := Submodule.add_mem _ hl hFl
    have key := hprod z l hl
    rw [ha_mem 0 (Submodule.zero_mem _), ha_mem l hl, ha_mem (F l) hFl, ha_mem _ hlF] at key
    have h0' : (⟨0, Submodule.zero_mem _⟩ : u.Λ) = 0 := rfl
    have hlF' : (⟨(l : Fin P.g → ℂ) + F l, hlF⟩ : u.Λ) = l + ⟨F l, hFl⟩ := rfl
    rw [h0', hχ0, hlF'] at key
    simp only [herm_zero_left, mul_zero, zero_add, Complex.exp_zero, _root_.mul_one,
      _root_.one_mul] at key
    have hX : cexp (π * D z l + π / 2 * D l l) =
        cexp (π * hermForm Hm (z + F z) (l + F l) + π / 2 * hermForm Hm (l + F l) (l + F l)) *
        (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ *
        (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ *
        (cexp (π * hermForm Hm (F z) (F l) + π / 2 * hermForm Hm (F l) (F l)))⁻¹ := by
      simp only [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      simp only [hD, herm_add_left, herm_add_right]
      ring
    rw [hX, hρdef]
    have e1 := Complex.exp_ne_zero (π * hermForm Hm z l + π / 2 * hermForm Hm l l)
    have e2 := Complex.exp_ne_zero (π * hermForm Hm (F z) (F l) + π / 2 * hermForm Hm (F l) (F l))
    have c1 := hχne l
    have c2 := hχne ⟨F l, hFl⟩
    have hmul := mul_ne_zero c1 e1
    rw [← mul_inv_cancel_right₀ hmul (ψ (z + l)), key]
    field_simp
  obtain ⟨hD0, hρ1⟩ := form_eq_zero_of_unit u.Λ ψ hψd hψ0 D hc hadd hsm hst ρ hρ hper
  refine ⟨fun z w => ?_, fun l => ?_⟩
  · have h1 := hD0 z w
    simp only [hD] at h1
    linear_combination -h1
  · have h1 := hρ1 l
    simp only [hρdef] at h1
    have h2 := semicharacter_rule hv' P.isLB u hH χ hfr' l ⟨F l, hF l l.2⟩ (Ef l ⟨F l, hF l l.2⟩)
      (hE _ _)
    rw [h2] at h1
    have c1 := hχne l
    have c2 := hχne ⟨F l, hF l l.2⟩
    field_simp at h1
    exact h1.symm
end GlobalTheory.SelfCube
