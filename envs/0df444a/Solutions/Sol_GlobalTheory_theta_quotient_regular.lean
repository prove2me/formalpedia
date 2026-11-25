-- Prove2me | solution 1 for GlobalTheory.theta_quotient_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:06:18.635797+00:00
-- url     : https://prove2.me/submissions/baddbd4d-31c1-430c-95ca-9835608ac18c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous
import Theorems.Thm_GlobalTheory_ThetaQuotient_eval_div_of_isHomogeneous
import Theorems.Thm_P2M_GlobalTheory_ThetaQuotient_valAt__eval__b3ed41ed5a49
import Theorems.Thm_GlobalTheory_ThetaQuotient_exists_glue_of_values
import Theorems.Thm_GlobalTheory_ThetaQuotient_exists_div_basicOpen
import Theorems.Thm_GlobalTheory_top_le_preimage_basicOpen_iff
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_top_le_preimage_of_valAt__ne_zero_a6acb076de42


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
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open ThetaQuotient
namespace GlobalTheory
theorem _root_.solution : (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z))) := by
  intro hext g τ _ N _ hpoly X ex D ⟨hint, hprop, hsurj, _, _, hD, hcov⟩ d p q hp hq
  have hext' := hext X inferInstance inferInstance
  obtain ⟨P, hP, hPv⟩ := hpoly d p hp
  obtain ⟨Q, hQ, hQv⟩ := hpoly d q hq
  generalize hθ : (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) = θ
  have hθ' : ∀ c z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) = θ c z :=
    fun c z => congrFun (congrFun hθ c) z
  simp only [hθ'] at hD hPv hQv
  have hmem : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ θ c z ≠ 0 := fun c => (hD c).2.2.1
  choose r hr using fun c => (hD c).2.2.2
  have hφ : ∀ (F : MvPolynomial (Fin g → Fin N) ℂ), F.IsHomogeneous d → ∀ c, ∃ φ : Γ(X.left, D c), ∀ z, θ c z ≠ 0 →
      valAt' (ex z).left (D c) φ = MvPolynomial.eval (fun c' => θ c' z) F / θ c z ^ d := by
    intro F hF c
    refine ⟨_, fun z hz => (valAt'_eval₂ (ex z) ((hmem c z).2 hz) (r c) F).trans ?_⟩
    rw [← eval_div_of_isHomogeneous hF]
    congr 2
    funext c'
    exact (hr c).1 c' z hz
  choose φp hφp using hφ P hP
  choose φq hφq using hφ Q hQ
  simp only [← hPv, ← hQv] at hφp hφq
  choose s hs using fun c => exists_div_basicOpen (φp c) (φq c)
  have hV : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) ↔ θ c z ≠ 0 ∧ q z ≠ 0 := by
    intro c z
    rw [top_le_preimage_basicOpen_iff]
    constructor
    · intro h
      have h1 := (hmem c z).1 (top_le_preimage_of_valAt'_ne_zero _ h)
      rw [hφq c z h1] at h
      exact ⟨h1, fun h0 => h (by rw [h0, zero_div])⟩
    · rintro ⟨h1, h2⟩
      rw [hφq c z h1]
      exact div_ne_zero h2 (pow_ne_zero _ h1)
  have hsv : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) →
      valAt' (ex z).left _ (s c) = p z / q z := by
    intro c z h
    obtain ⟨h1, _⟩ := (hV c z).1 h
    rw [hs c _ h, hφp c z h1, hφq c z h1, div_div_div_cancel_right₀ (pow_ne_zero _ h1)]
  choose σ hσ using hsurj
  obtain ⟨φ, hφ⟩ := exists_glue_of_values hext' (fun c => X.left.basicOpen (φq c)) s (fun x => p (σ x) / q (σ x))
    (fun c x hx => by
      have := hsv c (σ x) (by rw [hσ]; exact hx)
      rwa [hσ] at this)
  have hU : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (⨆ c, X.left.basicOpen (φq c)) ↔
      ∃ c, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) := by
    intro z
    refine (top_le_preimage_iff_mem _ _).trans (TopologicalSpace.Opens.mem_iSup.trans (exists_congr fun c => ?_))
    exact (top_le_preimage_iff_mem _ _).symm
  have hU' : ∀ z, q z ≠ 0 → ∃ c, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) := by
    intro z hz
    have : (ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ c, D c := by rw [hcov]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨c, (hV c z).2 ⟨(hmem c z).1 ((top_le_preimage_iff_mem _ _).2 hc), hz⟩⟩
  refine ⟨_, φ, fun z => ⟨⟨fun h => ?_, fun h => (hU z).2 (hU' z h)⟩, fun h => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (hU z).1 h
    exact ((hV c z).1 hc).2
  · obtain ⟨c, hc⟩ := hU' z h
    rw [hφ _ ((hU z).2 ⟨c, hc⟩), ← hsv c z hc]
    have := hsv c (σ (ex z)) (by rw [hσ]; exact hc)
    rw [hσ] at this
    exact this.symm
end GlobalTheory
