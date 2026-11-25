-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSec.sections_pow_eq_thetaLevelChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:25.655809+00:00
-- url     : https://prove2.me/submissions/59dff129-1301-482a-9c3f-a3e1949a2e9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Theorems.Thm_GlobalTheory_ThetaBundleSec_fr_pow_compat
import Theorems.Thm_GlobalTheory_ThetaBundleSec_exists_fn
import Theorems.Thm_GlobalTheory_ThetaBundleSec_sec_unique
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_pow
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_level
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_mul
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_pow
import Theorems.Thm_GlobalTheory_ThetaBundleSym_autFactor_eq
import Theorems.Thm_GlobalTheory_ThetaBundleSym_eC_nat_mul
import Theorems.Thm_GlobalTheory_ThetaBundleSym_exists_sec
import Theorems.Thm_GlobalTheory_eC_nat_mul
import Theorems.Thm_GlobalTheory_existsUnique_point_of_ringHom
import Theorems.Thm_GlobalTheory_mem_thetaLevelChar_iff_autFactor
import Theorems.Thm_P2M_GlobalTheory_eq_of_valAt__eq_229a7b1c0d79
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


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
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSec
open ThetaBundleSym
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.ThetaBundleSec
theorem _root_.solution :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → (∀ n : ℕ, (∀ s, ∃! θ, θ ∈ thetaLevelChar a b n τ ∧ u.IsFnPow n s θ) ∧ ∀ θ ∈ thetaLevelChar a b n τ, ∃! s, u.IsFnPow n s θ) := by
  intro g τ hτ N hN X ex D hX hrat hNe _ hadd a b ha hb L u hL hu _ _ n
  obtain ⟨hint, hprop, hex, hlat, -⟩ := hX
  obtain ⟨rfl, -, hlaw, hfr⟩ := hu
  have hext' := eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom X inferInstance inferInstance
  refine ⟨fun s => ?_, fun θ hθ => ?_⟩
  · obtain ⟨θ, hd, hfn, huniq, haut⟩ := exists_fn u hL n s
    refine ⟨θ, ⟨mem_thetaLevelChar_iff_autFactor.2 ⟨hd, fun m m' z => ?_⟩, hfn⟩, fun θ' h => huniq θ' h.2⟩
    refine haut z _ _ ((hlat _ _).2 ?_) fun i hi => hlaw m m' i z hi
    exact ⟨m, m', by abel⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  choose h F hh hF hF' hU using hfr
  have fh : ∀ i, HasFactor τ a b 0 (M + 1) (h i) := fun i => ⟨(hh i).1, fun n n' z => by
    rw [(hh i).2, ThetaBundleSym.eC_nat_mul, pow_zero, _root_.one_mul]; rfl⟩
  have fF : ∀ i, HasFactor τ a b 1 (M + 2) (F i) := fun i => ⟨hF i, fun n n' z => by
    rw [hF' i, ThetaBundleSym.eC_nat_mul, autFactor_eq]
    change _ * basicFactor τ n z ^ (M + 1) * _ = _
    ring⟩
  have fθ : HasFactor τ a b n n θ := ⟨hθ.1, fun m m' z => by
    rw [(mem_thetaLevelChar_iff_autFactor.1 hθ).2, autFactor_eq, mul_pow]⟩
  have hev : Even (n * (M + 1)) := hNe.mul_left n
  obtain ⟨s, hs⟩ := exists_sec hex hext' (lbPow L n) (fun j z => θ z * u.fr (j PUnit.unit) z ^ n)
    (fun j => by
      obtain ⟨W, ψ, hψ⟩ := hrat (n * (M + 2)) _ _
        (((fθ.mul ((fh (j PUnit.unit)).pow n)).mul ((fF (j PUnit.unit)).pow (n * M))).level ha hb
          (by convert hev using 1; ring) _ (by ring))
        (((fF (j PUnit.unit)).pow (n * (M + 1))).level ha hb (by convert hev using 1; ring) _ (by ring))
      refine ⟨W, ψ, fun z hz => ?_⟩
      have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := Cartier.lbPow_U L n j ▸ hz
      obtain ⟨a0, b0⟩ := (hU _ z).1.1 hz'
      have hq : F (j PUnit.unit) z ^ (n * (M + 1)) ≠ 0 := pow_ne_zero _ b0
      refine ⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩
      rw [(hU _ z).2, div_pow]
      field_simp
      ring)
    (fun j j' z hj hj' => by
      rw [fr_pow_compat u z n j j' hj hj']
      ring)
  exact ⟨s, hs, fun s' hs' => sec_unique u n hs' hs⟩
end GlobalTheory.ThetaBundleSec
