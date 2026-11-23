-- Prove2me | solution 1 for GlobalTheory.HolChart.exists_holomorphic_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:07.878265+00:00
-- url     : https://prove2.me/submissions/5ce4d7a7-5d35-4ac4-ac7a-fe5e55db083e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Theorems.Thm_GlobalTheory_HolChart_exists_etale_coords_vanishing
import Theorems.Thm_GlobalTheory_HolChart_derivation_eq_zero
import Theorems.Thm_GlobalTheory_HolChart_hol_of_affine

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
open GlobalTheory GlobalTheory.HolChart
namespace GlobalTheory.HolChart
theorem _root_.solution :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) → (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) := by
  intro hval haff hring X g hX e
  let e' : Sp ℂ ⟶ X.left := e.left
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (e' (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : X.hom (e' (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = X.hom (e' (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : ℂ →+* Γ(X.left, U) :=
    (X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn X.hom U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension g :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (X.hom.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hsm
  have hpts : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U →
      ∃ ev : Γ(X.left, U) →+* ℂ, (∀ f, valAt' x.left U f = ev f) ∧ ∀ a, ev (c a) = a := by
    intro x hx
    obtain ⟨ev, hev⟩ := (hval X.left x.left).2.1 U hx
    refine ⟨ev, hev, fun a => ?_⟩
    rw [← hev, ← hcc]
    exact (hval X.left x.left).2.2.2.2.2 X.hom (Over.w x) U a hx
  have heU : ⊤ ≤ e.left ⁻¹ᵁ U := ((hval X.left e').1 U).2 hp
  obtain ⟨ev, hev, hevc⟩ := hpts e heU
  obtain ⟨φ, hφc, hφ, hφ0⟩ := exists_etale_coords_vanishing c hc ev hevc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(X.left, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) Γ(X.left, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := hφ
  let eA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ := hring g Γ(X.left, U) eA hφ0
  have hex : ∀ x : Γ(X.left, U) →ₐ[ℂ] ℂ, ∃! y : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ U ∧ ∀ f, valAt' y.left U f = x f := fun x =>
    haff X U hU x.toRingHom (fun a => x.commutes a)
  choose pt hpt hptu using hex
  let W' : Set (Fin g → ℂ) := W ∩ ⋂ k, (W ∩ (fun w => σ w (f k)) ⁻¹' Metric.ball (eA (f k)) ε)
  have hW' : IsOpen W' := hW.inter (isOpen_iInter_of_finite fun k =>
    (hσd (f k)).continuousOn.isOpen_inter_preimage hW Metric.isOpen_ball)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ W ∧ ∀ k, ‖σ w (f k) - eA (f k)‖ < ε := by
    intro w
    simp only [W', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    exact ⟨fun h => ⟨h.1, fun k => (h.2 k).2⟩, fun h => ⟨h.1, fun k => ⟨h.1, h.2 k⟩⟩⟩
  refine ⟨W', fun w => pt (σ w), U, fun i => φ (MvPolynomial.X i), hW', ?_, ?_, hU, ?_, ?_, ?_, ?_⟩
  · exact (hmem 0).2 ⟨hW0, fun k => by rw [hσ0, sub_self, norm_zero]; exact hε⟩
  · show pt (σ 0) = e
    rw [hσ0]
    exact (hptu eA e ⟨heU, hev⟩).symm
  · intro V a
    refine hol_of_affine hval hU hW' (fun w => (pt (σ w)).left) (fun w _ => (hpt (σ w)).1)
      (fun b => ?_) V a
    exact ((hσd b).mono Set.inter_subset_left).congr fun w _ => (hpt (σ w)).2 b
  · intro w hw
    exact ⟨(hpt (σ w)).1, fun i => ((hpt (σ w)).2 _).trans (hσt w hw.1 i)⟩
  · have himg : (fun w => pt (σ w)) '' W' =
        {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U 0 ∈ (Set.univ : Set ℂ)} ∩
          ⋂ k, {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧
            valAt' x.left U (f k) ∈ Metric.ball (eA (f k)) ε} := by
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_univ,
        and_true, Metric.mem_ball, dist_eq_norm]
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(hpt (σ w)).1, fun k => ⟨(hpt (σ w)).1, ?_⟩⟩
        rw [(hpt (σ w)).2]
        exact ((hmem w).1 hw).2 k
      · rintro ⟨hx, hk⟩
        obtain ⟨ex, hex, hexc⟩ := hpts x hx
        let xA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ex with commutes' := hexc }
        have hk' : ∀ k, ‖xA (f k) - eA (f k)‖ < ε := fun k => by
          have := (hk k).2
          rw [hex] at this
          exact this
        obtain ⟨w, hw, hxw⟩ := hσs xA hk'
        refine ⟨w, (hmem w).2 ⟨hw, hxw ▸ hk'⟩, ?_⟩
        rw [← hxw]
        exact (hptu xA x ⟨hx, hex⟩).symm
    rw [himg]
    let _ := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) |
      ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧
        S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun k => ?_)
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, 0, Set.univ, isOpen_univ, rfl⟩
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f k, _, Metric.isOpen_ball, rfl⟩
  · intro D h0 hm hX
    refine derivation_eq_zero φ hφ ev D (fun a => ?_) (fun a b => ?_) hX
    · rw [hφc', ← hcc]; exact h0 a
    · rw [← hev, ← hev]; exact hm a b
end GlobalTheory.HolChart
