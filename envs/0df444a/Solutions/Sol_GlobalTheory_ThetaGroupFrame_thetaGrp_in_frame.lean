-- Prove2me | solution 1 for GlobalTheory.ThetaGroupFrame.thetaGrp_in_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:17.12811+00:00
-- url     : https://prove2.me/submissions/f7b5a5bb-f38b-42d6-a9c0-7998f3bc36d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_exists_const_of_cover
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_inf
import Theorems.Thm_P2M_GlobalTheory_ThetaGroupFrame_valAt__unit_ne_zero_1f417e79e6fc
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_wchart_two
import Theorems.Thm_P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_two_a0adc35401ff
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_lift_translPt
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_exp_herm_eq

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
open GlobalTheory GlobalTheory.ThetaGroupFrame
namespace GlobalTheory.ThetaGroupFrame
theorem _root_.solution :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a : u.Λ), 0 < k → ∀ (T : Over (Sp ℂ)) (p : (𝟙_ (Over (Sp ℂ)) ⟶ T)) (θ : Out.ThetaGrp P.A P.L k T), p ≫ θ.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) → ∃ C : ℂ, ∀ (j : Fin 2 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j 1) → valAt' (lift p (u.ex z)).left _ (θ.φ.s j).val * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k = C * cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) * u.fr (j 0) z ^ k) := by
  intro hv han P u Hm χ Ef hAH k a hk T p θ hp
  obtain ⟨hH, hχ, hEf, hfr⟩ := hAH
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'

  have h₀ : ∀ z, (lift p (u.ex z)).left ≫ (snd T P.A).left = (u.ex z).left := fun z => by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd]
  have h₁ : ∀ z, (lift p (u.ex z)).left ≫ (Out.translPt P.A θ.pt).left =
      (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left := fun z => by
    rw [← Over.comp_left, lift_translPt, hp, ← u.ex_add, add_comm]

  let D : (Fin 2 → P.L.ι) → Set (Fin P.g → ℂ) := fun j =>
    {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) ∧
      ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j 1)}
  let V : (Fin 2 → P.L.ι) → (Fin P.g → ℂ) → ℂ := fun j z =>
    valAt' (lift p (u.ex z)).left ((Out.thetaLB P.A P.L (k : ℤ) θ.pt).U j) (θ.φ.s j).val
  let G : (Fin 2 → P.L.ι) → (Fin P.g → ℂ) → ℂ := fun j z =>
    V j z * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k *
      cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) / u.fr (j 0) z ^ k
  have hopen : ∀ j, IsOpen (D j) := fun j =>
    ((u.hol _ 1).1).inter (((u.hol _ 1).1).preimage (continuous_id.add continuous_const))
  have hcov : ∀ z, ∃ j, z ∈ D j := by
    intro z
    have pick : ∀ y : Sp ℂ ⟶ P.A.left, ∃ i, ⊤ ≤ y ⁻¹ᵁ P.L.U i := fun y => by
      have hy : y (default : PrimeSpectrum ℂ) ∈ (⨆ i, P.L.U i) := by
        rw [P.isLB.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      exact ⟨i, ((hv _ y).1 _).2 hi⟩
    obtain ⟨i₀, hi₀⟩ := pick (u.ex z).left
    obtain ⟨i₁, hi₁⟩ := pick (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left
    exact ⟨![i₀, i₁], show _ ∧ _ from ⟨hi₀, hi₁⟩⟩
  have hVdiff : ∀ j, DifferentiableOn ℂ (V j) (D j) := by
    intro j
    have hh := han (Fin P.g → ℂ) Set.univ T P.A (fun _ => p) u.ex
      (fun U f => by
        by_cases hU : ⊤ ≤ p.left ⁻¹ᵁ U
        · simp only [Set.mem_univ, true_and, hU, Set.ofPred_true]
          exact ⟨isOpen_univ, differentiableOn_const _⟩
        · simp only [Set.mem_univ, true_and, hU, Set.ofPred_false]
          exact ⟨isOpen_empty, differentiableOn_empty⟩)
      (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
      ((Out.thetaLB P.A P.L (k : ℤ) θ.pt).U j) (θ.φ.s j).val
    refine hh.2.mono fun z hz => ⟨trivial, ?_⟩
    exact (top_le_wchart_two P.L (snd T P.A).left (Out.translPt P.A θ.pt).left j
      (lift p (u.ex z)).left _ _ (h₀ z) (h₁ z)).2 hz
  have hlin : Differentiable ℂ
      (fun z : Fin P.g → ℂ => z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))) := by
    simp only [dotProduct]
    fun_prop
  have hGdiff : ∀ j, DifferentiableOn ℂ (G j) (D j) := by
    intro j
    have hfr0 : DifferentiableOn ℂ (u.fr (j 0)) (D j) := (u.fr_hol _).mono fun z hz => hz.1
    have hfr1 : DifferentiableOn ℂ
        (fun z => u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (D j) :=
      (u.fr_hol _).comp (differentiable_id.add_const _).differentiableOn (fun z hz => hz.2)
    have hp0 : DifferentiableOn ℂ (fun z => u.fr (j 0) z ^ k) (D j) := hfr0.pow k
    have hp1 : DifferentiableOn ℂ
        (fun z => u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k) (D j) := hfr1.pow k
    have hE : DifferentiableOn ℂ
        (fun z => cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) (D j) :=
      (hlin.const_mul _).cexp.differentiableOn
    have hq := (((hVdiff j).mul hp1).mul hE).mul
      (hp0.inv (fun z (hz : z ∈ D j) => pow_ne_zero _ (u.fr_ne _ _ hz.1)))
    refine hq.congr fun z _ => ?_
    simp only [G, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]
  have hcompat : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z := by
    intro j j' z hz hz'
    have hgen : V j z =
        valAt' (u.ex z).left (P.L.U (j 0) ⊓ P.L.U (j' 0)) (P.L.g (j 0) (j' 0)).val ^ k *
          (valAt' (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left (P.L.U (j 1) ⊓ P.L.U (j' 1))
            (P.L.g (j 1) (j' 1)).val ^ k)⁻¹ * V j' z :=
      valAt'_gen_two hv P.L (snd T P.A).left (Out.translPt P.A θ.pt).left k θ.φ θ.isGen
        (lift p (u.ex z)).left _ _ (h₀ z) (h₁ z) j j' hz.1 hz.2 hz'.1 hz'.2
    have hc0 := u.fr_compat (j 0) (j' 0) z (top_le_inf _ hz.1 hz'.1)
    have hc1 := u.fr_compat (j 1) (j' 1) _ (top_le_inf _ hz.2 hz'.2)
    have hn0 := valAt'_unit_ne_zero hv _ _ (top_le_inf _ hz.1 hz'.1) (P.L.g (j 0) (j' 0))
    have hn1 := valAt'_unit_ne_zero hv _ _ (top_le_inf _ hz.2 hz'.2) (P.L.g (j 1) (j' 1))
    have hf0 := u.fr_ne _ _ hz'.1
    have hf1 := u.fr_ne _ _ hz'.2
    simp only [G]
    rw [hgen, hc0, hc1]
    field_simp
    ring
  have hper : ∀ j z, z ∈ D j → ∀ l ∈ (u.Λ : Set (Fin P.g → ℂ)),
      z + l ∈ D j ∧ G j (z + l) = G j z := by
    intro j z hz l hl
    have hex : ∀ y, u.ex (y + l) = u.ex y := fun y => by
      rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
    have hzl : z + l + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) = z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + l := by
      abel
    have hmem : z + l ∈ D j := by
      refine ⟨?_, ?_⟩
      · rw [hex]; exact hz.1
      · rw [hzl, hex]; exact hz.2
    refine ⟨hmem, ?_⟩
    have hV : V j (z + l) = V j z := by simp only [V, hex]
    have hf0 := u.fr_ne _ _ hmem.1
    have hf1 := u.fr_ne _ _ hmem.2
    rw [hzl] at hf1
    have e0 := hfr ⟨l, hl⟩ (j 0) z hz.1
    have e1 := hfr ⟨l, hl⟩ (j 1) _ hz.2
    dsimp only at e0 e1
    have hχ0 : χ ⟨l, hl⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hl⟩
    have hh := exp_herm_eq hH l (a : Fin P.g → ℂ) (Ef ⟨l, hl⟩ a) (hEf ⟨l, hl⟩ a)
    have eA : cexp ((Real.pi : ℂ) * ((z + l) ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) =
        cexp ((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) *
          cexp ((Real.pi : ℂ) * (l ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) := by
      rw [add_dotProduct, mul_add, Complex.exp_add]
    have eB : cexp ((Real.pi : ℂ) * ((z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ⬝ᵥ Hm.mulVec (star l)) +
          (Real.pi : ℂ) / 2 * (l ⬝ᵥ Hm.mulVec (star l))) ^ k =
        cexp ((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star l)) +
          (Real.pi : ℂ) / 2 * (l ⬝ᵥ Hm.mulVec (star l))) ^ k *
          cexp ((Real.pi : ℂ) * ((a : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star l))) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
      have hkk : (k : ℂ) * (k : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hk0
      linear_combination ((Real.pi : ℂ) * ((a : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star l))) * hkk
    simp only [G, hV]
    rw [hzl, e0, e1, eA, mul_pow, mul_pow, mul_pow, mul_pow, eB, hh]
    field_simp
  obtain ⟨C, hC⟩ := exists_const_of_cover D G hopen hcov hGdiff hcompat u.full hper
  refine ⟨C, fun j z hz0 hz1 => ?_⟩
  have h1 := hC j z ⟨hz0, hz1⟩
  have hf0 := u.fr_ne _ _ hz0
  simp only [G, V] at h1
  rw [div_eq_iff (pow_ne_zero _ hf0)] at h1
  have hE : cexp ((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) *
      cexp (-((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination cexp (-((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) * h1 -
    (valAt' (lift p (u.ex z)).left ((Out.thetaLB P.A P.L (k : ℤ) θ.pt).U j) (θ.φ.s j).val *
      u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k) * hE
end GlobalTheory.ThetaGroupFrame
