-- Prove2me | solution 1 for GlobalTheory.sections_pow_theta_functions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:35.76626+00:00
-- url     : https://prove2.me/submissions/a789f393-8236-4ff2-8689-d78ec9f49381

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Theorems.Thm_GlobalTheory_SectionTheta_ex_add_lattice
import Theorems.Thm_GlobalTheory_SectionTheta_quot_eq
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open SectionTheta
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') := by
  intro hval hext hred P u Hm χ Ef hAH n
  obtain ⟨-, -, -, hlaw⟩ := hAH
  have hcov : ∀ z, ∃ j : (lbPow P.L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j := by
    intro z
    have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
      rw [P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    refine ⟨fun _ => i, ?_⟩
    rw [Cartier.lbPow_U]
    exact ((hval _ (u.ex z).left).1 _).2 hi
  have hU : ∀ z (j : (lbPow P.L n).ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j PUnit.unit) := fun z j hj => Cartier.lbPow_U P.L n j ▸ hj
  refine ⟨fun s => ?_, fun θ s s' hs hs' => ?_⟩
  · choose c hc using hcov
    let θ : (Fin P.g → ℂ) → ℂ := fun z =>
      valAt' (u.ex z).left ((lbPow P.L n).U (c z)) (s.f (c z)) / u.fr (c z PUnit.unit) z ^ n
    have hθ : ∀ (j : (lbPow P.L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j →
        θ z = valAt' (u.ex z).left ((lbPow P.L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n :=
      fun j z hj => quot_eq u z (hval _ _).2.1 (hval _ _).2.2.1 n s _ _ (hc z) hj
    have hfn : u.IsFnPow n s θ := by
      intro j z hj
      rw [hθ j z hj, div_mul_cancel₀ _ (pow_ne_zero n (u.fr_ne _ z (hU z j hj)))]
    refine ⟨θ, ⟨⟨fun z => ?_, fun l z => ?_⟩, hfn⟩, fun θ' hθ' => ?_⟩
    · obtain ⟨ho, hd⟩ := u.hol _ (s.f (c z))
      have hn := ho.mem_nhds (hc z)
      have hd2 : DifferentiableOn ℂ (u.fr (c z PUnit.unit))
          {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow P.L n).U (c z)} :=
        (u.fr_hol _).mono fun w hw => hU w _ hw
      have hq := (hd.differentiableAt hn).mul (((hd2.differentiableAt hn).pow n).inv
        (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))))
      refine hq.congr_of_eventuallyEq ?_
      filter_upwards [hn] with w hw
      exact (hθ _ w hw).trans (div_eq_mul_inv _ _)
    · have h1 := hfn (c z) z (hc z)
      have hc' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ (lbPow P.L n).U (c z) := by
        rw [ex_add_lattice]; exact hc z
      have h2 := hfn (c z) (z + l) hc'
      rw [ex_add_lattice, h1, hlaw l _ z (hU z _ (hc z)), mul_pow, ← _root_.mul_assoc] at h2
      have h3 := mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ _ (hU _ _ hc'))) h2
      rw [← h3, _root_.mul_comm]
      rfl
    · funext z
      have h1 := hfn (c z) z (hc z)
      rw [hθ'.2 (c z) z (hc z)] at h1
      exact mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))) h1
  · have hsm : Smooth P.A.hom := by
      have := P.smoothDim
      exact SmoothOfRelativeDimension.smooth P.g P.A.hom
    have hf : s.f = s'.f := by
      funext j
      refine hext P.A (hred _ _ hsm) inferInstance _ _ _ fun x hx => ?_
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [hs j z hx, hs' j z hx]
    cases s
    cases s'
    cases hf
    rfl
end GlobalTheory
