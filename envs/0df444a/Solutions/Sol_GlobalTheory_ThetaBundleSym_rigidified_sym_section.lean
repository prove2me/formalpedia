-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSym.rigidified_sym_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:50:49.842662+00:00
-- url     : https://prove2.me/submissions/379fc006-f10e-485c-88d5-f3ca3b627cf0

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Theorems.Thm_GlobalTheory_ThetaBundleSym_exists_sec
import Theorems.Thm_GlobalTheory_ThetaBundleSym_exists_gen
import Theorems.Thm_GlobalTheory_ThetaBundleSym_eC_nat_mul
import Theorems.Thm_GlobalTheory_ThetaBundleSym_autFactor_eq
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_mul
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_pow
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_neg
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_level
import Theorems.Thm_GlobalTheory_ThetaBundleSym_hasFactor_theta
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_gen_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen


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
open GlobalTheory GlobalTheory.ThetaBundleSym
namespace GlobalTheory.ThetaBundleSym
theorem _root_.solution :
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → SiegelSubDomainStatement → ThetaHoloStatement → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) → Out.Rigidified X L ∧ Out.Sym X L ∧ ∃ th : L.Sec, u.IsFn th (fun z => theta a b z τ)) := by
  intro hext hS hH g τ hτ N hN X ex D hX hrat hNe _ hadd a b ha hb L u hL hu
  obtain ⟨hint, hprop, hex, -⟩ := hX
  obtain ⟨rfl, -, -, hfr⟩ := hu
  have hext' := hext X inferInstance inferInstance
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  choose h F hh hF hF' hU using hfr
  have fh : ∀ i, HasFactor τ a b 0 (M + 1) (h i) := fun i => ⟨(hh i).1, fun n n' z => by
    rw [(hh i).2, eC_nat_mul, pow_zero, _root_.one_mul]; rfl⟩
  have fF : ∀ i, HasFactor τ a b 1 (M + 2) (F i) := fun i => ⟨hF i, fun n n' z => by
    rw [hF' i, eC_nat_mul, autFactor_eq]
    change _ * basicFactor τ n z ^ (M + 1) * _ = _
    ring⟩
  refine ⟨DVR.exists_gen_of_local (V := ℂ) L hL _ _, ?_, ?_⟩
  · intro s
    refine ⟨⊤, trivial, ?_⟩
    have hinv : ∀ z, (u.ex z).left ≫ (GrpObj.inv : X ⟶ X).left = (u.ex (-z)).left := by
      intro z
      have h0 : u.ex (-z) = (u.ex z)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← u.ex_add, neg_add_cancel]
        exact CubeValues.ex_zero u
      rw [h0, ← Over.comp_left]
      rfl
    let φ : Fin 2 → (X.left ⟶ X.left) := ![(GrpObj.inv : X ⟶ X).left, 𝟙 _]
    have hchart : ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.wchart φ j →
        ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 1) := by
      intro j z hz
      have := (CubeValues.le_preimage_wchart (u.ex z).left L φ j).1 hz
      refine ⟨?_, this 1⟩
      rw [← hinv]
      exact this 0
    obtain ⟨t, ht⟩ := exists_gen hex hext' (L.LinComb φ ![1, -1])
      (fun j z => u.fr (j 0) (-z) / u.fr (j 1) z) (fun j => by
        obtain ⟨W, ψ, hψ⟩ := hrat (M + 3) _ _
          (((((fh (j 0)).neg ha hb).mul (fF (j 1))).mul (((fF (j 0)).neg ha hb).pow M)).level ha hb
            (by convert hNe using 1; ring) _ (by ring))
          (((((fF (j 0)).neg ha hb).pow (M + 1)).mul (fh (j 1))).level ha hb
            (by convert hNe using 1; ring) _ (by ring))
        refine ⟨W, ψ, fun z hz => ?_⟩
        obtain ⟨h0, h1⟩ := hchart j z hz
        obtain ⟨a0, b0⟩ := (hU (j 0) (-z)).1.1 h0
        obtain ⟨a1, b1⟩ := (hU (j 1) z).1.1 h1
        have hq : F (j 0) (-z) ^ (M + 1) * h (j 1) z ≠ 0 := mul_ne_zero (pow_ne_zero _ b0) a1
        refine ⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩
        rw [(hU (j 0) (-z)).2, (hU (j 1) z).2]
        field_simp
        ring)
      (fun j j' z hz hz' => by
        obtain ⟨h0, h1⟩ := hchart j z hz
        obtain ⟨h0', h1'⟩ := hchart j' z hz'
        have hv := CubeValues.val_linComb (u.ex z).left valAt'_rules L φ ![1, -1] j j' hz hz'
        rw [Fin.prod_univ_two] at hv
        have e0 : (u.ex z).left ≫ φ 0 = (u.ex (-z)).left := hinv z
        have e1 : (u.ex z).left ≫ φ 1 = (u.ex z).left := Category.comp_id _
        rw [e0, e1] at hv
        refine Eq.trans ?_ (congrArg (· * (u.fr (j' 0) (-z) / u.fr (j' 1) z)) hv).symm
        have c0 := u.fr_compat (j 0) (j' 0) (-z) ((top_le_preimage_inf _ _ _).2 ⟨h0, h0'⟩)
        have c1 := u.fr_compat (j 1) (j' 1) z ((top_le_preimage_inf _ _ _).2 ⟨h1, h1'⟩)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]
        rw [c0, c1, mul_div_mul_comm, div_eq_mul_inv])
      (fun j z hz => div_ne_zero (u.fr_ne _ _ (hchart j z hz).1) (u.fr_ne _ _ (hchart j z hz).2))
    have hφ : (fun k => (X.hom ⁻¹ᵁ ⊤).ι ≫ φ k) =
        ![(X.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : X ⟶ X).left, (X.hom ⁻¹ᵁ ⊤).ι] := by
      funext k
      fin_cases k
      · rfl
      · exact Category.comp_id _
    rw [← hφ]
    exact ⟨_, DVR.pullGen_isGen_of_isGen φ _ t ht _⟩
  · have fθ : HasFactor τ a b 1 1 (fun z => theta a b z τ) := hasFactor_theta hS hH hτ
    refine exists_sec hex hext' L (fun i z => theta a b z τ * u.fr i z) (fun i => ?_) (fun i j z hi hj => ?_)
    · obtain ⟨W, ψ, hψ⟩ := hrat (M + 2) _ _
        (((fθ.mul (fh i)).mul ((fF i).pow M)).level ha hb (by convert hNe using 1; ring) _ (by ring))
        (((fF i).pow (M + 1)).level ha hb (by convert hNe using 1; ring) _ (by ring))
      refine ⟨W, ψ, fun z hz => ?_⟩
      obtain ⟨a0, b0⟩ := (hU i z).1.1 hz
      have hq : F i z ^ (M + 1) ≠ 0 := pow_ne_zero _ b0
      refine ⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩
      rw [(hU i z).2]
      field_simp
      ring
    · rw [u.fr_compat i j z ((top_le_preimage_inf _ _ _).2 ⟨hi, hj⟩)]
      ring
end GlobalTheory.ThetaBundleSym
