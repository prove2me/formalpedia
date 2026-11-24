-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsPullConst.origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:50.680253+00:00
-- url     : https://prove2.me/submissions/a72d5434-ba77-4a08-a824-0773203e4f93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero


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
namespace IsPullConst
theorem _root_.solution {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) {m : T ⊗ A ⟶ A}
    {Φ : (Fin g → ℂ) → Fin g → ℂ} (h0 : Φ 0 = 0) (hΦ : exAt u p 0 ≫ m.left = (u.ex 0).left)
    {a b : ℤ} {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c) (j : Fin 2 → L.ι)
    (hj : ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j) :
    valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
        valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
      c * valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a := by
  have key : ∀ i, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U i → u.fr i 0 =
      valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => i) (rig.s fun _ => i).val := fun i hi => by
    rw [ex_zero] at hi
    exact hrig (fun _ => i) fun _ hy => Set.mem_iInter.2 fun _ => hi hy
  obtain ⟨h1, h2⟩ := (exAt_mem_pairChart_iff hΦ j).1 hj
  rw [← key _ h1, ← key _ h2, ← hc j 0 hj, h0]
end IsPullConst
end GlobalTheory.ThetaFn
