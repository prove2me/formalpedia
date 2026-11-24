-- Prove2me | solution 1 for GlobalTheory.thetaUnifAV_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:56.229855+00:00
-- url     : https://prove2.me/submissions/384e57ae-1f26-41c3-96e5-1e098168bd5d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaUnifAVOfParts

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ P : Out.PolAV (Sp ℂ), ∃ u : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, (∃ (U : P.A.left.Opens) (t : Fin P.g → Γ(P.A.left,
        U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(P.A.left, U) →+ ℂ, (∀ a, D (constFn
        P.A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex
        0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex
        w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin P.g → ℂ)) 0) ∧ (∀ (n : ℕ) (a : (Fin n →
        ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), (∀ (U : (P.A).left.Opens) (f : Γ((P.A).left, U)), IsOpen {w
        | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ
        : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin P.g →
        ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G w) = a w)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∃ (U : A.left.Opens) (t
        : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left,
        U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex
        0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t
        i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t
        i)) (ContinuousLinearMap.id ℂ (Fin g →
        ℂ)) 0) → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (A
        : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∀ (n : ℕ) (a : (Fin
        n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : (A).left.Opens) (f : Γ((A).left, U)), IsOpen {w
        | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ
        : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin g →
        ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G
        w) = a w) → ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F
        z) = u.ex z ≫ f) → (∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec
        P.A))), rig.IsGen → ∀ u₀ : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), u.ex = u₀.ex ∧ u.IsRig rig ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef
        l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c
        : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) /
        k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b
        : Fin P.g → ℂ))) (unitOn c)) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm
        : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z +
        l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P
        : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ → (Hm.IsHermitian ∧
        (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m
        : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l *
        cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ)
        ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → ∀ (n
        : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z +
        l)) → Function.Bijective Ef → u.IsAH Hm χ) → ThetaUnifAV := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 P rig hrig
  obtain ⟨u₀, hco, hlift⟩ := h1 P
  obtain ⟨u, Hm, χ, Ef, hex, hr, hd⟩ := h4 P rig hrig u₀
  rw [← hex] at hco hlift
  have hb := h6 P u Hm χ Ef hd
  have hAH := h9 P u Hm χ Ef hd hb
  have ht := h2 P.A P.L P.g u hco
  refine ⟨u, Hm, χ, Ef, hAH, hr, ht.1, ht.2, h3 P.A P.L P.g u hlift, fun n => ⟨(h7 P u Hm χ Ef hd n).1, fun θ hθ => ?_⟩,
    hd.2.2.1, hb, h5 P u Hm χ Ef hd⟩
  obtain ⟨s, hs⟩ := h8 P u Hm χ Ef hAH hd hb n θ hθ
  exact ⟨s, hs, fun s' hs' => (h7 P u Hm χ Ef hd n).2 θ s' s hs' hs⟩
end GlobalTheory
