-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exists_fn_of_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:13.814421+00:00
-- url     : https://prove2.me/submissions/2601d793-71ba-401d-ac82-17a7c21c57ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_gen
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_hol
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
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
namespace GlobalTheory.ThetaFn
theorem _root_.solution (hL : L.IsLB) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hd : Differentiable ℂ Φ) (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
        r z = valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          u.fr (j 1) (Φ z) ^ b * u.fr (j 0) z ^ (-a) := by
  choose ch hch using exists_chart u valueRules hL
  let R : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ := fun j z =>
    valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
      u.fr (j 1) (Φ z) ^ b * u.fr (j 0) z ^ (-a)
  have hc : ∀ z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] ![ch z, ch (Φ z)] :=
    fun z => (exAt_mem_pairChart_iff (hΦ z) _).2 ⟨hch z, hch (Φ z)⟩
  have hRR : ∀ j j' z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
      ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j' → R j z = R j' z := by
    intro j j' z hj hj'
    obtain ⟨h0, h1⟩ := (exAt_mem_pairChart_iff (hΦ z) j).1 hj
    obtain ⟨h0', h1'⟩ := (exAt_mem_pairChart_iff (hΦ z) j').1 hj'
    have k0 := (le_preimage_inf _ _ _).2 ⟨h0, h0'⟩
    have k1 := (le_preimage_inf _ _ _).2 ⟨h1, h1'⟩
    have n0 := zpow_ne_zero a (val_unit_ne_zero _ valueRules k0 (L.g _ _))
    have n1 := zpow_ne_zero b (val_unit_ne_zero _ valueRules k1 (L.g _ _))
    have e1 := val_gen (exAt u p z) valueRules α hα j j' hj hj'
    have e2 := val_linComb (exAt u p z) valueRules L ![(snd T A).left, m.left] ![a, -b] j j' hj hj'
    rw [Fin.prod_univ_two] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, exAt_snd, hΦ] at e2
    replace e1 := e1.trans (congrArg (· * _) e2)
    simp only [R]
    rw [u.fr_compat _ _ _ k0, u.fr_compat _ _ _ k1]
    refine (congrArg (· * _ * _) e1).trans ?_
    simp only [mul_zpow, zpow_neg]
    field_simp
    exact congrArg (· / _) (_root_.mul_comm _ _)
  refine ⟨fun z => R ![ch z, ch (Φ z)] z, fun z => ?_, fun z => ?_, fun j z hj => hRR _ _ z (hc z) hj⟩
  · set j : Fin 2 → L.ι := ![ch z, ch (Φ z)]
    obtain ⟨ho, hv⟩ := exAt_hol u p _ (α.s j).val
    have hn := ho.mem_nhds (hc z)
    have d0 : DifferentiableAt ℂ (u.fr (j 0)) z :=
      (u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds (hch z))
    have d1 : DifferentiableAt ℂ (fun w => u.fr (j 1) (Φ w)) z :=
      ((u.fr_hol (j 1)).differentiableAt ((u.hol _ 0).1.mem_nhds (hch (Φ z)))).comp z (hd z)
    have hq := ((hv.differentiableAt hn).mul (d1.zpow (m := b)
      (Or.inl (u.fr_ne _ _ (hch (Φ z)))))).mul (d0.zpow (m := -a) (Or.inl (u.fr_ne _ _ (hch z))))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    exact hRR _ j w (hc w) hw
  · exact mul_ne_zero (mul_ne_zero (val_unit_ne_zero _ valueRules (hc z) _)
      (zpow_ne_zero _ (u.fr_ne _ _ (hch _)))) (zpow_ne_zero _ (u.fr_ne _ _ (hch _)))
end GlobalTheory.ThetaFn
