-- Prove2me | solution 1 for GlobalTheory.ThetaFn.pull_analytic_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:30.0823+00:00
-- url     : https://prove2.me/submissions/a49cf195-768f-4d87-919a-49c864b2d045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_ThetaFn_exists_isPullConst
import Theorems.Thm_GlobalTheory_ThetaFn_IsPullConst_fn_eq
import Theorems.Thm_GlobalTheory_ThetaFn_IsPullConst_origin
import Theorems.Thm_GlobalTheory_ThetaFn_IsPullConst_eq_one

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
theorem _root_.solution (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} (hm : ψ ≫ snd T A = m)
    {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (hψ : ∀ z, exAt u p z ≫ ψ.left = exAt u p (Φ z)) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    (∀ z w, (b : ℂ) * hermForm Hm (Φ z) (Φ w) = a * hermForm Hm z w) ∧
    ∃ c : ℂ, c ≠ 0 ∧ IsPullConst u p Φ a b α c ∧
      (∀ (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) (θ θ' : (Fin g → ℂ) → ℂ),
        IsTwistPull A L ψ m hm a b α s s' → IsFnAt u p b s θ → IsFnAt u p a s' θ' →
          ∀ z, θ' z = c * θ (Φ z)) ∧
      ∀ rig : LB.Gen (L.pull (eSec A)), u.IsRig rig →
        (∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
          valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
              valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
            c * valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) ∧
        ((∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
          valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
              valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
            valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) →
          c = 1) := by
  have hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left := fun z => by
    rw [← hm, Over.comp_left, ← Category.assoc, hψ, exAt_snd]
  have hΦ0 : exAt u p 0 ≫ m.left = (u.ex 0).left := by rw [hΦ, map_zero]
  obtain ⟨h1, -, c, hc0, hc⟩ := exists_isPullConst hL hAH hΦ hα
  exact ⟨h1, c, hc0, hc, fun s s' θ θ' ht h h' => hc.fn_eq hL hψ ht h h', fun rig hrig =>
    ⟨hc.origin hrig (map_zero Φ) hΦ0, hc.eq_one hL hrig (map_zero Φ) hΦ0⟩⟩
end GlobalTheory.ThetaFn
