-- Prove2me | solution 1 for GlobalTheory.SameZeroScheme.exists_isGen_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:16:01.129326+00:00
-- url     : https://prove2.me/submissions/e07feab9-c041-45f8-b9b2-c03aa8583e73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroScheme
import Theorems.Thm_GlobalTheory_SameZeroScheme_resG_appLE
import Theorems.Thm_GlobalTheory_SameZeroScheme_appLE_appLE
import Theorems.Thm_GlobalTheory_SameZeroScheme_appLE_compat
import Theorems.Thm_GlobalTheory_SameZeroScheme_unit_eq_of_mul
import Theorems.Thm_GlobalTheory_SameZeroScheme_exists_unit_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SameZeroScheme
namespace GlobalTheory.SameZeroScheme
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (L : LB X) (θ : L.Sec) (φ ψ : Y ⟶ X), L.IsLB → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ L.U i), (φ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ ψ ⁻¹ᵁ L.U i), (ψ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ Y) (i j : L.ι) (h : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U j), ((t ≫ φ).appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ ((t ≫ ψ).appLE (L.U j) ⊤ h').hom (θ.f j) = 0) → ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![φ, ψ] ![1, -1]), t.IsGen := by
  intro X Y L θ φ ψ _ _ hψ H
  have h0 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L ![φ, ψ] j 0
  have h1 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ ψ ⁻¹ᵁ L.U (j 1) :=
    fun j => LB.wchart_le L ![φ, ψ] j 1
  have hc : ∀ j : Fin 2 → L.ι, ∃ c : Γ(Y, L.wchart ![φ, ψ] j)ˣ,
      (φ.appLE _ _ (h0 j)).hom (θ.f (j 0)) = c * (ψ.appLE _ _ (h1 j)).hom (θ.f (j 1)) := by
    intro j
    apply exists_unit_mul
    · intro V' h
      rw [resG_appLE]
      exact hψ _ _ _
    · intro T t h
      have k0 : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U (j 0) := fun x hx => h0 j (h hx)
      have k1 : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U (j 1) := fun x hx => h1 j (h hx)
      rw [appLE_appLE t φ _ h k0, appLE_appLE t ψ _ h k1]
      exact (H T t _ _ k0 k1).symm
  choose c hc using hc
  refine ⟨⟨c⟩, fun i j => ?_⟩
  let W : Y.Opens := L.wchart ![φ, ψ] i ⊓ L.wchart ![φ, ψ] j
  have wi : W ≤ L.wchart ![φ, ψ] i := inf_le_left
  have wj : W ≤ L.wchart ![φ, ψ] j := inf_le_right
  have ei := congrArg (resG Y wi) (hc i)
  have ej := congrArg (resG Y wj) (hc j)
  rw [map_mul, resG_appLE, resG_appLE] at ei ej
  have p0 : W ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) := le_inf (wi.trans (h0 i)) (wj.trans (h0 j))
  have p1 : W ≤ ψ ⁻¹ᵁ (L.U (i 1) ⊓ L.U (j 1)) := le_inf (wi.trans (h1 i)) (wj.trans (h1 j))
  have key := unit_eq_of_mul (c := res wi (c i)) (c' := res wj (c j)) (hψ _ _ _) ei ej
    (appLE_compat θ φ (i 0) (j 0) _ _ p0) (appLE_compat θ ψ (i 1) (j 1) _ _ p1)
  refine key.trans ?_
  congr 1
  exact (Fin.prod_univ_two (fun k : Fin 2 => (res (le_inf (wi.trans (LB.wchart_le L ![φ, ψ] i k))
    (wj.trans (LB.wchart_le L ![φ, ψ] j k)) : W ≤ (![φ, ψ] k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
    (pullU (![φ, ψ] k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ((![1, -1] : Fin 2 → ℤ) k))).symm
end GlobalTheory.SameZeroScheme
