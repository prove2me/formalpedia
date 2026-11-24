-- Prove2me | solution 1 for GlobalTheory.ThetaOnto.theta_from_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:43:33.686536+00:00
-- url     : https://prove2.me/submissions/d970fc12-d4a4-4878-89b0-9e0386e2d133

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanOfCardLe
import Theorems.Thm_GlobalTheory_ThetaOnto_constFn_zero
import Theorems.Thm_GlobalTheory_ThetaOnto_mem_span_of_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaOnto
namespace GlobalTheory.ThetaOnto
theorem _root_.solution :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f k z) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ → (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ) := by
  intro hval hdim hsec hfun P u Hm χ Ef hAH hfr hEf n θ hθ
  have hpt : ∀ z, (u.ex z).left ≫ P.A.hom = 𝟙 _ := fun z => Over.w (u.ex z)
  have hconst : ∀ z (U : P.A.left.Opens) (a : ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      valAt' (u.ex z).left U (constFn P.A.hom U a) = a :=
    fun z U a hU => (hval _ _).2.2.2.2.2 P.A.hom (hpt z) U a hU
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hper : ∀ (l : u.Λ) z, θ (z + l) = θ z := fun l z => by
      rw [hθ.2 l z, pow_zero, _root_.one_mul]
    have := u.discrete
    have : IsZLattice ℝ u.Λ := ⟨u.full⟩
    let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
    have hb : Bornology.IsBounded (Set.range θ) := by
      have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
        Metric.isCompact_of_isClosed_isBounded isClosed_closure
          (ZSpan.fundamentalDomain_isBounded b).closure
      refine (hK.image hθ.1.continuous).isBounded.subset ?_
      rintro _ ⟨z, rfl⟩
      refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
      have hfl : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ u.Λ := by
        have h : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ Submodule.span ℤ (Set.range b) :=
          (ZSpan.floor b z).2
        exact ((Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis_span ℝ).le h
      rw [← hper ⟨_, hfl⟩ (ZSpan.fract b z), ZSpan.fract_apply, sub_add_cancel]
    have hc : ∀ z, θ z = θ 0 := fun z => hθ.1.apply_eq_apply_of_bounded hb z 0
    refine ⟨secConst P.A.hom P.L (θ 0), ?_⟩
    intro j z hz
    show valAt' _ _ (constFn P.A.hom _ (θ 0)) = _
    rw [hconst z _ _ hz, pow_zero, _root_.mul_one, hc z]
  ·
    obtain ⟨s, hs⟩ := hsec P n hn
    have hex : ∀ i, ∃ T, u.IsThetaFn Hm χ n T ∧ u.IsFnPow n (s i) T :=
      fun i => ((hfun P u Hm χ Ef hfr n).1 (s i)).exists
    choose T hT using hex
    have hcomb : ∀ a : Fin (n ^ P.g) → ℂ,
        u.IsFnPow n (secComb P.A.hom a s) (fun z => ∑ i, a i * T i z) := by
      intro a j z hz
      obtain ⟨e, he⟩ := (hval _ (u.ex z).left).2.1 _ hz
      have hca : ∀ i, e (constFn P.A.hom ((lbPow P.L n).U j) (a i)) = a i := fun i => by
        rw [← he]; exact hconst z _ (a i) hz
      have hsi : ∀ i, e ((s i).f j) = T i z * u.fr (j PUnit.unit) z ^ n := fun i => by
        rw [← he]; exact (hT i).2 j z hz
      rw [he]
      show e (∑ i, constFn P.A.hom _ (a i) * (s i).f j) = _
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hca, hsi, _root_.mul_assoc]
    have hli : LinearIndependent ℂ T := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hz : ∀ z, ∑ i, a i * T i z = 0 := fun z => by
        simpa [Finset.sum_apply] using congrFun ha z
      have h0 : u.IsFnPow n (secComb P.A.hom (0 : Fin (n ^ P.g) → ℂ) s)
          (fun z => ∑ i, a i * T i z) := by
        intro j z hz'
        rw [hcomb 0 j z hz']
        simp [hz]
      have heq := (hfun P u Hm χ Ef hfr n).2 _ _ _ (hcomb a) h0
      have ha0 : a = 0 := by
        apply hs a
        intro j
        have hj := congrArg (fun t => LB.Sec.f t j) heq
        simp only [secComb] at hj
        rw [hj]
        simp [constFn_zero]
      intro i
      rw [ha0]
      rfl
    obtain ⟨a, ha⟩ := mem_span_of_card_le (u.IsThetaFn Hm χ n)
      (fun M f hf hlin => hdim P.g u.Λ u.discrete u.full Hm χ Ef hfr.1 hAH.2.1 hfr.2.1 hfr.2.2.1 hEf
        n hn M f (fun k => ⟨(hf k).1, fun l z => (hf k).2 l z⟩) hlin)
      T (fun i => (hT i).1) hli hθ
    refine ⟨secComb P.A.hom a s, ?_⟩
    intro j z hz
    rw [hcomb a j z hz, ← ha]
    simp [Finset.sum_apply]
end GlobalTheory.ThetaOnto
