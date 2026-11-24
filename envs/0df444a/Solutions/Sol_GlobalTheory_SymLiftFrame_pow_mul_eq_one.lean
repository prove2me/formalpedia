-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.pow_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:15:02.44339+00:00
-- url     : https://prove2.me/submissions/399576f4-5f6b-4ebe-8c03-b42aa780f3a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_corr_one
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_powGen
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_theta
import Theorems.Thm_GlobalTheory_SymLiftFrame_exists_choice
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_right
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translT
import Theorems.Thm_GlobalTheory_ThetaFn_ex_natCast_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hc : HasAnConst u p Hm Θ x c) {n : ℕ} {l : u.Λ} (hl : (n : ℂ) • x = l)
    (h : LB.Gen.Corr L _ _ _ _ (powGen A L k Θ n) (LB.oneGen L)) : c ^ n * χ l ^ k = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hpt : ∀ i : ℕ, p ≫ Θ.pt ^ i = u.ex ((i : ℂ) • x) := fun i => by
    rw [MonObj.comp_pow, hc.1, ex_natCast_smul]
  have key : ∀ m : ℕ, (∏ i ∈ Finset.range m, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J) *
      u.fr (J (u.ex ((m : ℂ) • x)).left) ((m : ℂ) • x) ^ k =
      c ^ m * Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((m : ℂ) ^ 2 / 2) * hermForm Hm x x)) *
        u.fr (J (u.ex 0).left) 0 ^ k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have t := cval_theta hJ hc ((m : ℂ) • x)
      have hm1 : (m : ℂ) • x + x = ((m + 1 : ℕ) : ℂ) • x := by
        push_cast
        rw [add_smul, one_smul]
      rw [hm1] at t
      have hE : fockFactor Hm k x ((m : ℂ) • x) *
          Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((m : ℂ) ^ 2 / 2) * hermForm Hm x x)) =
          Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * (((m + 1 : ℕ) : ℂ) ^ 2 / 2) * hermForm Hm x x)) := by
        unfold fockFactor
        rw [← Complex.exp_add, hermForm_smul_left]
        congr 1
        push_cast
        ring
      rw [Finset.prod_range_succ]
      linear_combination (∏ i ∈ Finset.range m, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J) * t +
        (c * fockFactor Hm k x ((m : ℂ) • x)) * ih +
        (c ^ (m + 1) * u.fr (J (u.ex 0).left) 0 ^ k) * hE
  have hprod : ∏ i ∈ Finset.range n, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J = 1 := by
    have h1 := cval_corr_one hJ h (exAt u p 0)
    rw [cval_powGen hJ Θ n] at h1
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) h1
    rw [exAt_translT u (hpt i) 0, zero_add]
  have hl1 : u.ex (l : Fin g → ℂ) = u.ex 0 := by
    rw [hex0]
    exact (u.ker _).2 l.2
  have hk := key n
  rw [hprod, _root_.one_mul, hl, hl1] at hk
  have ha : u.fr (J (u.ex 0).left) 0 = χ l *
      Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) *
        u.fr (J (u.ex 0).left) (l : Fin g → ℂ) := by
    have := hAH.2.2.2 l (J (u.ex 0).left) 0 (hJ _)
    rw [zero_add] at this
    exact this
  have hak := congrArg (· ^ k) ha
  rw [mul_zpow, mul_zpow] at hak
  have h0 : hermForm Hm 0 (l : Fin g → ℂ) = 0 := zero_dotProduct _
  have hexp : Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) ^ k *
      Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((n : ℂ) ^ 2 / 2) * hermForm Hm x x)) = 1 := by
    rw [← Complex.exp_int_mul, ← Complex.exp_add, h0, ← hl, hermForm_smul_left, hermForm_smul_right,
      star_natCast, ← Complex.exp_zero]
    congr 1
    ring
  have hfr0 : u.fr (J (u.ex 0).left) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  apply mul_right_cancel₀ hfr0
  linear_combination (-1 : ℂ) * hak -
    (χ l ^ k * Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) ^ k) * hk -
    (χ l ^ k * c ^ n * u.fr (J (u.ex 0).left) 0 ^ k) * hexp
end GlobalTheory.SymLiftFrame
