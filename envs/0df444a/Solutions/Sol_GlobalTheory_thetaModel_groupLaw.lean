-- Prove2me | solution 1 for GlobalTheory.thetaModel_groupLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:36:36.203226+00:00
-- url     : https://prove2.me/submissions/a95e472c-027d-4f0e-82a5-32adc5c93d19

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_ThetaModelGroup_grpObj_of_points
import Theorems.Thm_GlobalTheory_ThetaModelGroup_RegAt_mul
import Theorems.Thm_GlobalTheory_ThetaModelGroup_RegAt_sum
import Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_chart
import Theorems.Thm_GlobalTheory_ThetaModelGroup_hom_ext_points
import Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_hom_of_coords
import Theorems.Thm_GlobalTheory_ThetaModelGroup_IsLevel_neg
import Theorems.Thm_GlobalTheory_ThetaModelGroup_IsLevel_sq
import Theorems.Thm_GlobalTheory_ThetaModelGroup_locallyOfFiniteType_tensor

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
open ThetaModelGroup
namespace GlobalTheory
theorem _root_.solution : (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X
    Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U
    : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a
    w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b
    w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w
    | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w))
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w))
    w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (X : Over (Sp
    ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left,
    U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶
    X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y : Over (Sp
    ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp
    ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D
    : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶
    Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left,
    U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F
    y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) → (∀ (X Y : Over (Sp
    ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X
    ⊗ Y).left) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 1 ≤ N → ∀ f f' : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
    : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ f' ∧ ∀ (n n'
    : Fin g → ℤ) z, f' (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f' z) → ∃ (n : ℕ) (h k : Fin n → (Fin g →
    ℂ) → ℂ), (∀ i, (Differentiable ℂ (h i) ∧ ∀ (n n' : Fin g → ℤ) z, (h i) (z + τ *ᵥ ofIntVec n +
    ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * (h i) z) ∧ (Differentiable ℂ (k i) ∧ ∀ (n n' : Fin g → ℤ) z, (k i) (z + τ *ᵥ ofIntVec n +
    ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * (k i) z)) ∧ ∀ z w, f (z + w) * f' (z - w) = ∑ i, h i z * k i w) → (∀ (g : ℕ) (τ
    : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
    : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z
    + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 +
    ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
    τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
    g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n
    n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c
    : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
    : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
    : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
    g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice
    τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g →
    ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g
    : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
    ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
    N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
    (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
    U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
    : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left,
    D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) •
    z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r
    c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c
    i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin
    g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
    (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
    ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
    0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → ∃ (_
    : GrpObj X), IsCommMonObj X ∧ ∀ z w, ex (z + w) = ex z * ex w) := by
  intro _ _ H Hred Hadd Hth _ Hne _ g τ hτ N hN X ex D ⟨hint, hprop, hs, hker, _, hc, hD⟩ hreg
  have hX : IsReduced X.left := inferInstance
  have hXf : LocallyOfFiniteType X.hom := inferInstance
  have hXXf : LocallyOfFiniteType (X ⊗ X).hom := locallyOfFiniteType_tensor
  have hXX : IsReduced (X ⊗ X).left := Hred X X hX hX hXf hXf
  have hXXXf : LocallyOfFiniteType ((X ⊗ X) ⊗ X).hom := locallyOfFiniteType_tensor
  have hXXX : IsReduced ((X ⊗ X) ⊗ X).left := Hred _ X hXX hX hXXf hXf
  have hlev := (Hth g τ hτ N (by omega)).1
  generalize hθ : (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) = θ
  have hθ' : ∀ c z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) = θ c z :=
    fun c z => by rw [← hθ]
  simp only [hθ'] at hc hlev
  replace hlev : ∀ c, IsLevel τ N (θ c) := hlev
  have hc' := fun c => And.intro (hc c).1 (hc c).2.2
  choose s hs' using hs
  have hch : ∀ x, ∃ a, θ a (s x) ≠ 0 := fun x => by
    obtain ⟨a, ha⟩ := exists_chart hD (ex (s x))
    exact ⟨a, ((hc a).2.2.1 _).1 ha⟩
  have hq : ∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), IsLevel τ (N * d) p → IsLevel τ (N * d) q → ∀ x, q (s x) ≠ 0 →
      RegAt x (fun x' => p (s x') / q (s x')) := fun d p q hp hq x hx => by
    obtain ⟨U, φ, hU⟩ := hreg d p q hp hq
    refine ⟨U, by simpa only [hs'] using (hU (s x)).1.2 hx, φ, fun x' hx' => ?_⟩
    have := hU (s x')
    rw [hs'] at this
    exact this.2 (this.1.1 hx')
  have hsub : ∀ z, s (ex z) - z ∈ periodLattice τ := fun z => (hker _ _).1 (hs' _)
  obtain ⟨m, hm⟩ := exists_hom_of_coords H hXX hXXf hD ex θ hc'
    (fun y => s (y ≫ fst X X) + s (y ≫ snd X X)) (fun y => by
      obtain ⟨a, ha⟩ := hch (y ≫ fst X X)
      obtain ⟨b, hb⟩ := hch (y ≫ snd X X)
      obtain ⟨f', hf', hf0⟩ := Hne g τ hτ N (by omega) (s (y ≫ fst X X) - s (y ≫ snd X X))
      refine ⟨fun y' => f' (s (y' ≫ fst X X) - s (y' ≫ snd X X)) /
        (θ a (s (y' ≫ fst X X)) ^ 2 * θ b (s (y' ≫ snd X X)) ^ 2),
        div_ne_zero hf0 (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)), fun c => ?_⟩
      obtain ⟨n, h, k, hhk, hsum⟩ := Hadd g τ hτ N (by omega) (θ c) f' (hlev c) hf'
      have := RegAt.sum (y := y) fun i : Fin n =>
        ((hq 2 (h i) _ (by rw [mul_comm]; exact (hhk i).1) (hlev a).sq _ (pow_ne_zero _ ha)).comp (fst X X)).mul
        ((hq 2 (k i) _ (by rw [mul_comm]; exact (hhk i).2) (hlev b).sq _ (pow_ne_zero _ hb)).comp (snd X X))
      convert this using 2 with y'
      rw [div_mul_eq_mul_div, mul_comm (f' _), hsum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [div_mul_div_comm])
  obtain ⟨i, hi⟩ := exists_hom_of_coords H hX hXf hD ex θ hc' (fun y => - s y) (fun y => by
      obtain ⟨a, ha⟩ := hch y
      refine ⟨fun y' => (θ a (s y'))⁻¹, inv_ne_zero ha, fun c => ?_⟩
      have := hq 1 _ _ (by rw [Nat.mul_one]; exact (hlev c).neg) (by rw [Nat.mul_one]; exact hlev a) y ha
      convert this using 2 with y'
      rw [div_eq_inv_mul])
  have ha : ∀ c, IsAffineOpen (D c) := fun c => (hc c).1
  refine grpObj_of_points X ex (fun x => ⟨s x, hs' x⟩) m i (fun z w => ?_) (fun z => ?_)
    (hom_ext_points H hX hXf hD ha) (hom_ext_points H hXX hXXf hD ha) (hom_ext_points H hXXX hXXXf hD ha)
  · rw [hm, lift_fst, lift_snd, hker, add_sub_add_comm]
    exact add_mem (hsub z) (hsub w)
  · rw [hi, hker, neg_sub_neg, ← neg_sub]
    exact neg_mem (hsub z)
end GlobalTheory
