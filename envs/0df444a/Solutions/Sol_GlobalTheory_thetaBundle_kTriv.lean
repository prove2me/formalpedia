-- Prove2me | solution 1 for GlobalTheory.thetaBundle_kTriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:25.354721+00:00
-- url     : https://prove2.me/submissions/26cb21c9-6ce3-49fa-aee6-917aab081dbf

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
import Theorems.Thm_GlobalTheory_autFactor_eq_zero_mul_exp
import Theorems.Thm_P2M_GlobalTheory_autFactor_ne_zero__b91261d44755
import Theorems.Thm_GlobalTheory_mem_periodLattice_of_exp_thetaLinForm
import Theorems.Thm_GlobalTheory_eq_zero_of_thetaLinForm
import Theorems.Thm_GlobalTheory_fderiv_eq_mul_of_ratio

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
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice
        τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g →
        ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ
        : Fin g → ℂ) (gam : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
        : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = gam * f z) → ξ = 0) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c
        i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) /
        2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
        : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g →
        ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)))) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u
        : HolUnif A L g), SmoothOfRelativeDimension g A.hom → (∀ w : Fin g → ℂ, (∀ (U
        : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex
        0).left ⁻¹ᵁ U → fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) → w = 0) → ∃ (U
        : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex
        0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f *
        f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t
        i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t
        i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L
        : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ R], ∀ (x
        : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L
        x), c.IsGen) → x = 1) → Out.KTriv A L) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L
        : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ
        R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing
        R] [Algebra ℂ R], ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing
        R] [Algebra ℂ R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing
        R] [Algebra ℂ R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → ∀ (g : ℕ) (u
        : HolUnif A L g) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∃ (U : A.left.Opens) (t
        : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left,
        U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex
        0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t
        i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t
        i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ l, a l ≠ 0) → (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l)) → (∀ (w
        : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ), (∀ l : u.Λ, cexp (B l w) = cexp (lam
        l)) → w ∈ u.Λ) → (∀ (w : Fin g → ℂ) (lam : (Fin g →
        ℂ) →ₗ[ℂ] ℂ), (∀ l : u.Λ, B l w = lam l) → w = 0) → (∀ (R : Type) [CommRing R] [Algebra ℂ
        R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) → (∀ (g : ℕ) (τ
        : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex
        : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral
        X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
        (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
        U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
        : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D
        c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i
        : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D
        c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ)
        • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin
        N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
        (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z
        +
        w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L
        : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ)
        ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n +
        ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n'
        : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n'
        : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N
        : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠
        0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → Out.KTriv X L) := by
  intro hLat hSep hInd hSpan hCoord hKT hFT hLoc hUni g τ hτ N hN X ex D hX _ _ _ _ a₀ b₀ _ _ L u hL hu
    hAb hSm
  obtain ⟨hex, hΛ, hfr, -⟩ := hu
  subst hex
  obtain ⟨-, -, -, -, -, hD, hcov⟩ := hX

  have huniq : ∀ n n' m m' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = τ *ᵥ ofIntVec m + ofIntVec m' →
      n = m ∧ n' = m' := by
    intro n n' m m' h
    have h0 := (hLat g τ hτ).2.2 (n - m) (n' - m') (by
      rw [sub_eq_add_neg, sub_eq_add_neg, ofIntVec_add, ofIntVec_add, ofIntVec_neg, ofIntVec_neg,
        mulVec_add, mulVec_neg]
      rw [← sub_eq_zero] at h
      rw [← h]
      abel)
    exact ⟨sub_eq_zero.mp h0.1, sub_eq_zero.mp h0.2⟩
  have hmem : ∀ l : u.Λ, ∃ p : (Fin g → ℤ) × (Fin g → ℤ),
      (l : Fin g → ℂ) = τ *ᵥ ofIntVec p.1 + ofIntVec p.2 := by
    intro l
    obtain ⟨n, n', hn⟩ := (hΛ l).1 l.2
    exact ⟨(n, n'), hn⟩
  choose p hp using hmem
  have hpn : ∀ n n' : Fin g → ℤ, ∀ hl : τ *ᵥ ofIntVec n + ofIntVec n' ∈ u.Λ, (p ⟨_, hl⟩).1 = n := by
    intro n n' hl
    exact ((huniq _ _ _ _ (hp ⟨_, hl⟩)).1).symm
  have hlat : ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' ∈ u.Λ := fun n n' => (hΛ _).2 ⟨n, n', rfl⟩

  let θ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)

  have hsub : ∀ y y' : PrimeSpectrum ℂ, y = y' := fun y y' => Subsingleton.elim y y'
  obtain ⟨c, hc⟩ : ∃ c, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ D c := by
    let x₀ : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
    have hx : (u.ex 0).left.base x₀ ∈ (⨆ c, D c) := by
      rw [hcov]
      trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨c, fun y _ => ?_⟩
    rw [hsub y x₀]
    exact hc

  have hsep : ∀ w : Fin g → ℂ, (∀ (U : X.left.Opens) (f : Γ(X.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) → w = 0 := by
    intro w hw
    have hθc : θ c 0 ≠ 0 := ((hD c).2.2.1 0).mp hc
    obtain ⟨r, hr, -⟩ := (hD c).2.2.2
    have hdiff := (hInd g τ hτ N (by omega)).1
    refine hSep g τ hτ N hN 0 w (fderiv ℂ (θ c) 0 w / θ c 0) fun f hf => ?_
    exact fderiv_eq_mul_of_ratio θ (fun c' => (hdiff c').1) c 0 w hθc
      (fun c' y => valAt' (u.ex y).left (D c) (r c')) (fun c' y hy => hr c' y hy)
      (fun c' => hw (D c) (r c') hc) f (hSpan g τ hτ N (by omega) f hf)
  have hcoord := hCoord X L g u hSm hsep
  have hane : ∀ l : u.Λ, autFactor a₀ b₀ τ (p l).1 (p l).2 0 ≠ 0 := fun l => autFactor_ne_zero' _ _ _ _ _ _
  have hrel : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = autFactor a₀ b₀ τ (p l).1 (p l).2 0 * cexp (thetaLinForm (p l).1 z) * u.fr i (z + l) := by
    intro l i z hz
    rw [← autFactor_eq_zero_mul_exp, hp l, ← add_assoc]
    exact hfr _ _ i z hz
  have hunimod : ∀ (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ),
      (∀ l : u.Λ, cexp (thetaLinForm (p l).1 w) = cexp (lam l)) → w ∈ u.Λ := by
    intro w lam hl
    rw [hΛ]
    refine mem_periodLattice_of_exp_thetaLinForm hτ.1 w lam fun n n' => ?_
    have h1 := hl ⟨_, hlat n n'⟩
    rwa [hpn n n' (hlat n n')] at h1
  have hnondeg : ∀ (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ),
      (∀ l : u.Λ, thetaLinForm (p l).1 w = lam l) → w = 0 := by
    intro w lam hl
    refine eq_zero_of_thetaLinForm (τ := τ) w lam fun n n' => ?_
    have h1 := hl ⟨_, hlat n n'⟩
    rwa [hpn n n' (hlat n n')] at h1
  exact hKT X L hAb hL (hFT X L hAb hL (hLoc X L hAb hL
    (hUni X L hAb hL g u (fun l => autFactor a₀ b₀ τ (p l).1 (p l).2 0) (fun l => thetaLinForm (p l).1)
      hcoord hane hrel hunimod hnondeg)))
end GlobalTheory
