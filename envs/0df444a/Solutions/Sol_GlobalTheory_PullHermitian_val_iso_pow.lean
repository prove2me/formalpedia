-- Prove2me | solution 1 for GlobalTheory.PullHermitian.val_iso_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:15:35.332862+00:00
-- url     : https://prove2.me/submissions/98db72f1-2065-408b-ac4d-e7bee518ff08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Theorems.Thm_P2M_GlobalTheory_PullHermitian_valAt__eq_unitVal_3711952a0e7e
import Theorems.Thm_GlobalTheory_PullHermitian_unitVal_comp_id
import Theorems.Thm_GlobalTheory_PullHermitian_wchart_of
import Theorems.Thm_GlobalTheory_PullHermitian_unitVal_linComb
import Theorems.Thm_GlobalTheory_PullHermitian_unitVal_iso
import Theorems.Thm_GlobalTheory_PullHermitian_idx_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.PullHermitian
theorem _root_.solution {Y : Scheme.{0}} {L : LB X} {L' : LB Y} (f : X ⟶ Y) (m n : ℕ)
    (w : LB.Iso (lbPow (L'.pull f) m) (lbPow L n)) (hw : w.IsGen) (i i' : L.ι) (j j' : L'.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L.U i') (hj : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j)
    (hj' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j') :
    valAt' x _ (w.s (idx f m n i j)).val *
        valAt' (x ≫ f) (L'.U j ⊓ L'.U j') (L'.g j j').val ^ m =
      valAt' x (L.U i ⊓ L.U i') (L.g i i').val ^ n * valAt' x _ (w.s (idx f m n i' j')).val := by
  have a := wchart_of x L (𝟙 X) i (by simpa using hi)
  have a' := wchart_of x L (𝟙 X) i' (by simpa using hi')
  have c := wchart_of x L' f j hj
  have c' := wchart_of x L' f j' hj'
  have b := wchart_of x (L'.pull f) (𝟙 X) (fun _ => j) c
  have b' := wchart_of x (L'.pull f) (𝟙 X) (fun _ => j') c'
  have h := unitVal_iso x w hw (fun _ => i) (fun _ => i') (fun _ _ => j) (fun _ _ => j') a a' b b'
  have h1 := unitVal_linComb x L (𝟙 X) n i i' (inf_of x a a') (inf_of x hi hi')
  have h2 := unitVal_linComb x (L'.pull f) (𝟙 X) m (fun _ => j) (fun _ => j') (inf_of x b b')
    (inf_of x c c')
  have h3 := unitVal_linComb x L' f 1 j j' (inf_of x c c') (inf_of _ hj hj')
  replace h1 := h1.trans (congrArg (· ^ (n : ℤ)) (unitVal_comp_id x _ (inf_of x hi hi') _))
  replace h2 := h2.trans (congrArg (· ^ (m : ℤ))
    ((unitVal_comp_id x _ (inf_of x c c') _).trans h3))
  replace h := h.trans (congrArg₂ (fun a b => a * b⁻¹ * _) h1 h2)
  rw [valAt'_eq_unitVal x (idx_chart x f m n i j hi hj),
    valAt'_eq_unitVal x (idx_chart x f m n i' j' hi' hj'),
    valAt'_eq_unitVal x (inf_of x hi hi'), valAt'_eq_unitVal _ (inf_of _ hj hj')]
  have h4 := congrArg Units.val h
  simp only [Units.val_mul, zpow_natCast, zpow_one, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val] at h4
  refine (congrArg (· * _) h4).trans ?_
  field_simp
end GlobalTheory.PullHermitian
