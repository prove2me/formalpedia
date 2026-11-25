-- Prove2me | solution 1 for GlobalTheory.ThetaSplit.exists_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:20.720589+00:00
-- url     : https://prove2.me/submissions/d9865f2f-171e-4656-b942-c5cc6e6a74b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
import Theorems.Thm_GlobalTheory_ThetaSplit_exists_coboundary
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit
variable {X Y : Scheme.{0}} {L : LB X}
namespace GlobalTheory.ThetaSplit
theorem _root_.solution (hL : L.IsLB) {S₀ : Scheme.{0}} (p : X ⟶ S₀) (e : S₀ ⟶ X) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (hU : ∀ n : ℕ, 0 < n → ∀ y : Γ(S₀, ⊤)ˣ, ∃ x : Γ(S₀, ⊤)ˣ, x ^ n = y)
    {C : Type} [CommGroup C] (τ : C → (X ⟶ X)) (hτ : ∀ c c', τ (c * c') = τ c ≫ τ c') (hτp : ∀ c, τ c ≫ p = p)
    (m : ℤ) (v : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ c] ![m, -m])) (hv : ∀ c, (v c).IsGen)
    (hc : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      val (v c) r z J * val (v c') (r ≫ τ c) z J = val (v c') r z J * val (v c) (r ≫ τ c') z J) :
    ∃ b : C → Γ(S₀, ⊤)ˣ, ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      val (v (c * c')) r z J * gm (r ≫ p) z ⊤ (b (c * c')) =
        (val (v c) r z J * gm (r ≫ p) z ⊤ (b c)) * (val (v c') (r ≫ τ c) z J * gm (r ≫ p) z ⊤ (b c')) := by
  have ex : ∀ c c', ∃ a : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      val (v (c * c')) r z J = val (v c) r z J * val (v c') (r ≫ τ c) z J * gm (r ≫ p) z ⊤ a := fun c c' => by
    obtain ⟨a, ha⟩ := CommutatorPairing.exists_ratio hL (fun U _ g => by
        refine Eq.trans ?_ (Fintype.prod_sum_type _).symm
        simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
        show g (𝟙 X) ^ m * g (τ (c * c')) ^ (-m) =
          g (𝟙 X) ^ m * g (τ c) ^ (-m) * (g (τ c ≫ 𝟙 X) ^ m * g (τ c ≫ τ c') ^ (-m))
        rw [Category.comp_id, hτ]
        simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left]) p e he hp (hv (c * c'))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hv c) (DVR.pullGen_isGen _ _ _ _ (hv c') (τ c)))
    exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans
      (congrArg (val (v c) r z J * ·) (val_pull hJ _ _ _))))⟩
  choose a ha using ex
  have inj : ∀ u u' : Γ(S₀, ⊤)ˣ, (∀ (y : S₀) (J), Good L y J → gm (e ≫ p) y ⊤ u = gm (e ≫ p) y ⊤ u') → u = u' :=
    fun u u' h => unit_ext fun y _ => by
      choose J hJ using fun χ : S₀ ⟶ X => exists_chart hL (χ y)
      rw [← he]; exact h y J hJ
  obtain ⟨b, hb⟩ := exists_coboundary hU a (fun c c' => inj _ _ fun y J hJ => by
      have e₁ := ha c c' _ e y J hJ
      have e₂ := ha c' c _ e y J hJ
      rw [hc c c' _ e y J hJ] at e₁
      rw [mul_comm c' c, e₁] at e₂
      exact mul_left_cancel e₂) (fun c c' c'' => inj _ _ fun y J hJ => by
      have e₁ := ha c c' _ e y J hJ
      have e₂ := ha (c * c') c'' _ e y J hJ
      have e₃ := ha c' c'' _ (e ≫ τ c) y J hJ
      have e₄ := ha c (c' * c'') _ e y J hJ
      rw [_root_.mul_assoc c] at e₂
      rw [Category.assoc, Category.assoc, hτp, ← hτ] at e₃
      rw [map_mul, map_mul]
      apply Additive.ofMul.injective
      have a₁ := congrArg Additive.ofMul e₁
      have a₂ := congrArg Additive.ofMul e₂
      have a₃ := congrArg Additive.ofMul e₃
      have a₄ := congrArg Additive.ofMul e₄
      simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
      linear_combination (norm := abel) a₃ + a₄ - a₁ - a₂)
  refine ⟨b, fun c c' Z r z J hJ => ?_⟩
  rw [ha c c' Z r z J hJ, _root_.mul_assoc, ← map_mul, mul_comm (a c c'), hb, map_mul, _root_.mul_mul_mul_comm]
end GlobalTheory.ThetaSplit
