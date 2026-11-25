-- Prove2me | solution 1 for GlobalTheory.PulledBiextFrame.exists_appellHumbert_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:41.413206+00:00
-- url     : https://prove2.me/submissions/18e212a3-fd90-4624-87e1-1a042a2e3499

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAppellHumbertFrameOfPulledBiextension
import Theorems.Thm_GlobalTheory_CubeValues_comp_psum
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_SelfCube_herm_add_left
import Theorems.Thm_GlobalTheory_SelfCube_herm_add_right
import Theorems.Thm_GlobalTheory_SelfCube_prod_finset_fin_two
import Theorems.Thm_GlobalTheory_SelfCube_semicharacter_rule
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PulledBiextFrame
open GlobalTheory.CubeValues GlobalTheory.SelfCube
namespace GlobalTheory.PulledBiextFrame
theorem _root_.solution :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ) (w : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → (∀ z, u.ex (F z) = u.ex z ≫ w) → F + F' = LinearMap.id → (∀ z z', hermForm Hm (F z) z' = hermForm Hm z (F' z')) → ∃ (u₁ : HolUnif P.A (cubeLB P.A ![𝟙 P.A, w] P.L) P.g) (χ₁ : u₁.Λ → ℂ), u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ u₁.IsAH Hm χ₁ ∧ ∀ (l : u₁.Λ) (a b : u.Λ), (a : Fin P.g → ℂ) = l → (b : Fin P.g → ℂ) = F l → χ₁ l = (-1) ^ Ef a b := by
  intro _ _ _ _ P u Hm χ Ef w F F' ⟨hH, hpos, hχ, hfr⟩ hE hw hFF hadj
  classical
  have hv : ValueRules := GlobalTheory.valAt'_rules
  have hF : ∀ l ∈ u.Λ, F l ∈ u.Λ := fun l hl => by
    have h0 := hw 0
    rw [map_zero, ex_zero] at h0
    rw [← u.ker, hw, (u.ker l).2 hl, ← h0]
  have hsc := fun l m => semicharacter_rule hv P.isLB u hH χ hfr l m _ (hE l m)
  have hχ0 : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using hχ l
  let Y : Fin 2 → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := ![LinearMap.id, F]
  have hy : ∀ k z, u.ex z ≫ (![𝟙 P.A, w] : Fin 2 → _) k = u.ex (Y k z) := by
    intro k z
    fin_cases k
    · exact Category.comp_id _
    · exact (hw z).symm
  let p : ULift.{0} (Finset (Fin 2)) → (Fin P.g → ℂ) → (Fin P.g → ℂ) := fun I z => ∑ k ∈ I.down, Y k z
  have hpd : ∀ I, Differentiable ℂ (p I) := fun I =>
    Differentiable.fun_sum fun k _ => (LinearMap.toContinuousLinearMap (Y k)).differentiable
  have hps : ∀ (I : ULift.{0} (Finset (Fin 2))) z,
      (u.ex z).left ≫ (psum P.A ![𝟙 P.A, w] I.down).left = (u.ex (p I z)).left := fun I z => by
    rw [← Over.comp_left, comp_psum u (u.ex z) _ (fun k => Y k z) (fun k => hy k z)]
  refine ⟨combUnif u _ p hpd _ hps, fun l : u.Λ => (-1) ^ Ef l ⟨F l, hF l l.2⟩, rfl, rfl,
    ⟨hH, hpos, fun l => by simp [norm_zpow], ?_⟩, ?_⟩
  · intro (l : u.Λ) j z hz
    have hc : ∀ I, ⊤ ≤ (u.ex (p I z)).left ⁻¹ᵁ P.L.U (j I) := fun I => by
      rw [← hps]; exact (le_preimage_wchart (u.ex z).left P.L _ j).1 hz I
    change ∏ I, u.fr (j I) (p I z) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (-1) ^ Ef l ⟨F l, hF l l.2⟩ *
        Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) *
        ∏ I, u.fr (j I) (p I (z + l)) ^ ((-1 : ℤ) ^ (2 - I.down.card))
    rw [prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ z) ^ ((-1 : ℤ) ^ (2 - I.card)),
      prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ (z + l)) ^ ((-1 : ℤ) ^ (2 - I.card))]
    have p0 : ∀ x, p ⟨∅⟩ x = 0 := fun x => by simp [p]
    have p1 : ∀ x, p ⟨{0}⟩ x = x := fun x => by simp [p, Y]
    have p2 : ∀ x, p ⟨{1}⟩ x = F x := fun x => by simp [p, Y]
    have p3 : ∀ x, p ⟨{0, 1}⟩ x = x + F x := fun x => by simp [p, Y]
    have c1 := hc ⟨{0}⟩
    have c2 := hc ⟨{1}⟩
    have c3 := hc ⟨{0, 1}⟩
    rw [p1] at c1
    rw [p2] at c2
    rw [p3] at c3
    have e1 := hfr l _ _ c1
    have e2 := hfr ⟨F l, hF l l.2⟩ _ _ c2
    have e3 := hfr (l + ⟨F l, hF l l.2⟩) _ _ c3
    rw [hsc] at e3
    have k2 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
    have s3 : z + F z + ((l + ⟨F l, hF l l.2⟩ : u.Λ) : Fin P.g → ℂ) = z + l + F (z + l) := by
      simp only [Submodule.coe_add, map_add]; abel
    rw [s3] at e3
    have hsum : ∀ x y, hermForm Hm x (F y) + hermForm Hm (F x) y = hermForm Hm x y := fun x y => by
      rw [hadj, ← herm_add_right]
      exact congrArg _ (LinearMap.congr_fun hFF y)
    change _ = _ * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * _ at e1
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (F z) (F l) +
      Real.pi / 2 * hermForm Hm (F l) (F l)) * u.fr _ (F z + F l) at e2
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (z + F z) (l + F l) +
      Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) * _ at e3
    rw [← map_add] at e2
    have hx : Real.pi * hermForm Hm (z + F z) (l + F l) +
        Real.pi / 2 * hermForm Hm (l + F l) (l + F l) =
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm (F z) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      simp only [herm_add_left, herm_add_right]
      linear_combination (Real.pi : ℂ) * hsum z l + (Real.pi / 2 : ℂ) * hsum l l
    rw [hx, Complex.exp_add, Complex.exp_add (_ + _) (_ + _)] at e3
    simp only [p0, p1, p2, p3, k2, Finset.card_empty, Finset.card_singleton]
    rw [e1, e2, e3]
    have n1 := hχ0 l
    have n2 := hχ0 ⟨F l, hF l l.2⟩
    norm_num
    field_simp
  · intro (l : u.Λ) a b ha hb
    obtain rfl : a = l := Subtype.ext ha
    obtain rfl : b = ⟨F a, hF a a.2⟩ := Subtype.ext hb
    rfl
end GlobalTheory.PulledBiextFrame
