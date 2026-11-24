-- Prove2me | solution 1 for GlobalTheory.exists_isMonHom_of_map_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:13.644189+00:00
-- url     : https://prove2.me/submissions/67e1d792-de44-438d-b861-9d6948d960b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTopLePreimageOfISupEqTop
import Theorems.Thm_GlobalTheory_TorusEnd_top_le_preimage_finset_inf
import Theorems.Thm_GlobalTheory_TorusEnd_exists_top_le_preimage_of_iSup_eq_top
import Theorems.Thm_P2M_GlobalTheory_TorusEnd_valAt__eval__5db942836e7d
import Theorems.Thm_GlobalTheory_TorusEnd_hom_ext_of_points
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c


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
open TorusEnd
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f'
        : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶
        X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y
        : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶
        Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D
        : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶
        Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left,
        U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F
        y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) → (∀ (X Y : Over (Sp
        ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X
        ⊗ Y).left) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (N : ℕ) (F
        : (Fin g → ℂ) →ₗ[ℂ] (Fin g →
        ℂ)), (∀ l ∈ periodLattice τ, F l ∈ periodLattice τ) → ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g →
        ℂ) → ℂ, G z₀ ≠ 0 ∧ ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z
        + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 +
        ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ (fun z => f (F z) * G z) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => f (F z) * G z) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d
        : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => f (F
        z) * G z) z)) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c
        i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) /
        2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
        : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
        ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
        N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
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
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → ∀ [GrpObj X], (∀ z w, ex (z +
        w) = ex z * ex w) → ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g →
        ℂ), (∀ l ∈ periodLattice τ, F l ∈ periodLattice τ) → ∃ f : X ⟶ X, IsMonHom f ∧ ∀ z, ex (F
        z) = ex z ≫ f) := by
  intro _ Hm Hred HG Hθ g τ hτ N hN X ex D ⟨hint, hprop, hsurj, hex, _, hD, hcov⟩ hreg _ hadd F hF
  have hXr : IsReduced X.left := inferInstance
  have hXf : LocallyOfFiniteType X.hom := inferInstance
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ X) → (𝟙_ (Over (Sp ℂ)) ⟶ X) := fun y => ex (F (Function.surjInv hsurj y))
  have hΦ : ∀ z, Φ (ex z) = ex (F z) := fun z => by
    refine (hex _ _).2 ?_
    rw [← map_sub]
    exact hF _ ((hex _ _).1 (Function.surjInv_eq hsurj _))
  obtain ⟨d, hd⟩ := HG g τ hτ N F hF
  have hθ := (Hθ g τ hτ N (by omega)).1
  obtain ⟨f, hf, -⟩ := Hm X X hXr hXf Φ fun y => by
    obtain ⟨z₀, rfl⟩ := hsurj y
    obtain ⟨c, hc⟩ := exists_top_le_preimage_of_iSup_eq_top (ex (F z₀)).left D hcov
    obtain ⟨haff, -, hmem, r, hr, hgen⟩ := hD c
    obtain ⟨G, hG0, hG⟩ := hd z₀
    choose U φ hU using fun c' => hreg d _ _ (hG _ (hθ c')) (hG _ (hθ c))
    have hle : ∀ c', Finset.univ.inf U ≤ U c' := fun c' => Finset.inf_le (Finset.mem_univ c')
    refine ⟨Finset.univ.inf U, D c, ?_, haff, fun y' hy' => ?_, fun ψ => ?_⟩
    · exact (top_le_preimage_finset_inf _ _ _).2 fun c' _ =>
        (hU c' z₀).1.2 (mul_ne_zero ((hmem _).1 hc) hG0)
    · obtain ⟨z, rfl⟩ := hsurj y'
      rw [hΦ]
      exact (hmem _).2 (left_ne_zero_of_mul ((hU c z).1.1 (top_le_preimage_mono _ (hle c) hy')))
    · obtain ⟨P, rfl⟩ := hgen ψ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (fun c' => resG X.left (hle c') (φ c')) P, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := hsurj y'
      have hq := (hU c z).1.1 (top_le_preimage_mono _ (hle c) hy')
      have h1 := left_ne_zero_of_mul hq
      have h2 := right_ne_zero_of_mul hq
      rw [hΦ, valAt'_eval₂ _ _ hy', valAt'_eval₂ _ _ ((hmem _).2 h1)]
      congr 2
      funext c'
      rw [valAt'_res _ _ _ hy', (hU c' z).2 hq, hr c' _ h1, mul_div_mul_right _ _ h2]
  have hfe : ∀ z, ex (F z) = ex z ≫ f := fun z => by rw [hf, hΦ]
  have h0 : ex 0 = η[X] := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h1 : ex 0 = 1 := by simpa using h
    rw [h1, Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨f, ⟨?_, ?_⟩, hfe⟩
  · rw [← h0, ← hfe, map_zero]
  · have hft : LocallyOfFiniteType (X ⊗ X).hom := by
      change LocallyOfFiniteType (pullback.fst X.hom X.hom ≫ X.hom)
      infer_instance
    refine hom_ext_of_points (Hm X (X ⊗ X) (Hred X X hXr hXr hXf hXf) hft) fun y => ?_
    obtain ⟨z, hz⟩ := hsurj (y ≫ fst X X)
    obtain ⟨w, hw⟩ := hsurj (y ≫ snd X X)
    have hy : y = lift (ex z) (ex w) := by
      ext1 <;> simp [hz, hw]
    rw [hy, ← Category.assoc, ← Hom.mul_def, ← hadd, ← hfe, map_add, hadd, Hom.mul_def, ← Category.assoc, lift_map,
      ← hfe, ← hfe]
end GlobalTheory
