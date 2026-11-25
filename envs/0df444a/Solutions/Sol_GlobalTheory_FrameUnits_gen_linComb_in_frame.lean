-- Prove2me | solution 1 for GlobalTheory.FrameUnits.gen_linComb_in_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:47:42.919923+00:00
-- url     : https://prove2.me/submissions/98967bf9-f3d6-4eb9-8913-55476e121283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Theorems.Thm_GlobalTheory_FrameUnits_form_eq_zero_and_const
import Theorems.Thm_GlobalTheory_FrameUnits_differentiableOn_fun_prod
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_continuous_hermForm_self
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_swap
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_CubeValues_val_gen
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero
import Theorems.Thm_GlobalTheory_PullHermitian_exists_chart
import Theorems.Thm_GlobalTheory_PullHermitian_exists_glue
import Theorems.Thm_GlobalTheory_SelfCube_exists_chart
import Theorems.Thm_GlobalTheory_SelfCube_exists_glue
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.FrameUnits
theorem _root_.solution (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hu : u.IsAH Hm χ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Y : Scheme.{0}} (p : E → (Sp ℂ ⟶ Y))
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {z | ⊤ ≤ p z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (p z) U f) {z | ⊤ ≤ p z ⁻¹ᵁ U})
    (hS : ∃ R : ℝ, ∀ z : E, ∃ l, (∀ w, p (w + l) = p w) ∧ ‖z + l‖ ≤ R)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ A.left)) (ε : K → ℤ) (lam : K → E →ₗ[ℂ] (Fin g → ℂ))
    (hlam : ∀ k z, p z ≫ φ k = (u.ex (lam k z)).left)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    (∀ z w, ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k w) = 0) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (j : K → L.ι) (z : E), (∀ k, ⊤ ≤ (u.ex (lam k z)).left ⁻¹ᵁ L.U (j k)) →
        valAt' (p z) (L.wchart φ j) (t.s j).val = κ * ∏ k, u.fr (j k) (lam k z) ^ ε k := by
  have hv : ValueRules := valAt'_rules
  obtain ⟨R, hS⟩ := hS
  have hld : ∀ k, Differentiable ℂ (lam k) := fun k =>
    (LinearMap.toContinuousLinearMap (lam k)).differentiable
  let D : (K → L.ι) → Set E := fun j => {z | ⊤ ≤ p z ⁻¹ᵁ L.wchart φ j}
  have hD : ∀ j z, z ∈ D j ↔ ∀ k, ⊤ ≤ (u.ex (lam k z)).left ⁻¹ᵁ L.U (j k) := fun j z => by
    refine (le_preimage_wchart (p z) L φ j).trans ?_
    simp only [hlam]
  have hcov : ∀ z, ∃ j, z ∈ D j := fun z => by
    choose c hc using SelfCube.exists_chart hv hL u
    exact ⟨fun k => c (lam k z), (hD _ _).2 fun k => hc _⟩
  let T : (K → L.ι) → E → ℂ := fun j z => valAt' (p z) (L.wchart φ j) (t.s j).val
  let F : (K → L.ι) → E → ℂ := fun j z => ∏ k, u.fr (j k) (lam k z) ^ ε k
  have hF0 : ∀ j z, z ∈ D j → F j z ≠ 0 := fun j z hz =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ((hD j z).1 hz k))
  obtain ⟨ψ, hψ, hG⟩ := PullHermitian.exists_glue D (fun j => (hp _ 0).1) hcov
    (fun j z => T j z * (F j z)⁻¹)
    (fun j => by
      have dF : DifferentiableOn ℂ (fun z => ∏ k, u.fr (j k) (lam k z) ^ ε k) (D j) :=
        differentiableOn_fun_prod _ fun k => DifferentiableOn.zpow
          ((u.fr_hol (j k)).comp (hld k).differentiableOn fun z hz => (hD j z).1 hz k)
          (Or.inl fun z hz => u.fr_ne _ _ ((hD j z).1 hz k))
      exact (hp _ (t.s j).val).2.mul (dF.inv (hF0 j)))
    (fun j j' z hz hz' => by
      have e1 : T j z = _ * T j' z := val_gen (p z) hv t ht j j' hz hz'
      have e2 := val_linComb (p z) hv L φ ε j j' hz hz'
      simp only [hlam] at e2
      have e3 : T j z = (∏ k, valAt' (u.ex (lam k z)).left (L.U (j k) ⊓ L.U (j' k))
          (L.g (j k) (j' k)).val ^ ε k) * T j' z := e1.trans (congrArg (· * T j' z) e2)
      have c1 : F j z = (∏ k, valAt' (u.ex (lam k z)).left (L.U (j k) ⊓ L.U (j' k))
          (L.g (j k) (j' k)).val ^ ε k) * F j' z := by
        simp only [F]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2 ⟨(hD j z).1 hz k, (hD j' z).1 hz' k⟩), mul_zpow]
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff (hF0 _ _ hz) (hF0 _ _ hz'), e3, c1]
      ring)
  have hψ0 : ∀ z, ψ z ≠ 0 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    rw [hG j z hj]
    exact mul_ne_zero (val_unit_ne_zero _ hv hj _) (inv_ne_zero (hF0 j z hj))
  obtain ⟨h1, h2⟩ := form_eq_zero_and_const (S := {l | ∀ w, p (w + l) = p w}) hS ψ hψ hψ0
    (fun z w => ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k w))
    (continuous_finset_sum _ fun k _ => continuous_const.mul
      ((continuous_hermForm_self Hm).comp (hld k).continuous))
    (fun z z' w => by simp only [map_add, hermForm_add_left, mul_add, Finset.sum_add_distrib])
    (fun c z w => by
      simp only [map_smul, hermForm_smul_left, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun z w => by
      simp only [star_sum, star_mul', star_intCast]
      exact Finset.sum_congr rfl fun k _ => by rw [hermForm_swap hu.1])
    (fun l hl => by
      have hΛ : ∀ k, lam k l ∈ u.Λ := fun k => by
        rw [← u.ker, ← ex_zero u]
        apply Over.OverMorphism.ext
        rw [← hlam, ← map_zero (lam k), ← hlam, ← hl 0, zero_add]
      refine ⟨∏ k, χ ⟨lam k l, hΛ k⟩ ^ ε k, by simp [norm_prod, norm_zpow, hu.2.2.1], fun z => ?_⟩
      obtain ⟨j, hj⟩ := hcov z
      have hj' : z + l ∈ D j := by
        simp only [D, Set.mem_setOf_eq, hl z]
        exact hj
      have eT : T j (z + l) = T j z := by simp only [T, hl z]
      have c1 : F j z = (∏ k, χ ⟨lam k l, hΛ k⟩ ^ ε k) *
          cexp (π * ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k l) +
            π / 2 * ∑ k, (ε k : ℂ) * hermForm Hm (lam k l) (lam k l)) * F j (z + l) := by
        simp only [F]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.exp_sum,
          ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [hu.2.2.2 ⟨lam k l, hΛ k⟩ (j k) (lam k z) ((hD j z).1 hj k), map_add, mul_zpow, mul_zpow,
          ← Complex.exp_int_mul]
        congr 3
        simp only [hermForm]
        ring
      rw [hG j z hj, hG j _ hj', eT]
      have n1 := hF0 j z hj
      have n2 := hF0 j _ hj'
      have key : ∀ a b c d : ℂ, b ≠ 0 → c ≠ 0 → b = a * c → d * c⁻¹ = a * (d * b⁻¹) := by
        rintro a _ c d h1 h2 rfl
        have := left_ne_zero_of_mul h1
        field_simp
      exact key _ _ _ _ n1 n2 c1)
  refine ⟨h1, ψ 0, hψ0 0, fun j z hz => ?_⟩
  have hz' := (hD j z).2 hz
  rw [← h2 z, hG j z hz', inv_mul_cancel_right₀ (hF0 j z hz')]
end GlobalTheory.FrameUnits
