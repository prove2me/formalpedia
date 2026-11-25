-- Prove2me | solution 1 for GlobalTheory.EndDivisible.exists_monomials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:46.489006+00:00
-- url     : https://prove2.me/submissions/6d109a6f-be0e-4889-8393-8f326f9e702f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeOfSumEqZero
import Theorems.Thm_GlobalTheory_exists_gen_zsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_powSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.EndDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace
namespace GlobalTheory.EndDivisible
theorem _root_.solution {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (t : ℕ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(t : ℤ), -1])) (hα : α.IsGen)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w ≫ m) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    ∃ b : (Z.presheaf.stalk z)ˣ, ∀ a ≤ t,
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => (N : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) * b.val := by
  obtain ⟨β, hβ⟩ : ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k)
      (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)), β.IsGen :=
    exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hα (f ≫ w)) _
  refine ⟨val β (𝟙 Z) z J, fun a ha => ?_⟩
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N ⊕ Fin 2)
      (Sum.elim (fun _ => f ≫ w) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k))
      (Sum.elim (fun _ => 1) (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)) (fun _ : Unit => u) (fun _ => (N : ℤ)) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, hu]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      Category.assoc, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha]
    rw [← _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
    simp [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullMulSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f β hβ)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp
end GlobalTheory.EndDivisible
