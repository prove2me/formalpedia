-- Prove2me | solution 1 for GlobalTheory.ValueTwoGen.exists_unit_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:37.995962+00:00
-- url     : https://prove2.me/submissions/902d81ce-4b63-490c-b734-552f646a4430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IntegralSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsValueAtEqUnitMul
import Theorems.Thm_GlobalTheory_EvVal_existsUnique_sec_eq_mul_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ModelMetric
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ValueTwoGen
namespace GlobalTheory.ValueTwoGen
theorem _root_.solution {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, (t'.s j).val =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (w : Γ(Y, ⊤)) * (t.s j).val := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t' ht') t ht
  obtain ⟨w', hw', -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t' ht'
  obtain ⟨_, -, hu⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t ht
  have h1 : (1 : Γ(Y, ⊤)) = w' * w := by
    have a := hu 1 (fun j => by simp [genSec])
    have b := hu (w' * w) (fun j => by
      have e1 := hw' j
      have e2 := hw j
      simp only [genSec] at e1 e2 ⊢
      rw [map_mul, _root_.mul_assoc, ← e2, ← e1])
    exact a.trans b.symm
  exact ⟨⟨w, w', by rw [_root_.mul_comm]; exact h1.symm, h1.symm⟩, fun j => hw j⟩
end GlobalTheory.ValueTwoGen
