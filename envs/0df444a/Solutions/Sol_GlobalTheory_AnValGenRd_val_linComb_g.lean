-- Prove2me | solution 1 for GlobalTheory.AnValGenRd.val_linComb_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:25.215521+00:00
-- url     : https://prove2.me/submissions/fa9ec242-f050-4226-99ed-6ca6c758054f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsHolomorphicGeneratorReadingAutomorphy
import Theorems.Thm_GlobalTheory_AnValGenRd_val_prod
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__res_9bf5469fe96a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
section LC
variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
private theorem valAt'_app_hom_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (f : Γ(W, U)) :
    valAt' x (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) = valAt' (x ≫ ψ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']
private theorem valAt'_pullU_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (u : Γ(W, U)ˣ) :
    valAt' x (ψ ⁻¹ᵁ U) (pullU ψ U u).val = valAt' (x ≫ ψ) U u.val := by
  unfold pullU
  rw [Units.coe_map]
  exact valAt'_app_hom_eq_valAt'_comp x ψ U u.val
private theorem valAt'_res_unit_eq {W : Scheme.{0}} (x : Sp ℂ ⟶ W) {U V : W.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (u : Γ(W, U)ˣ) : valAt' x V (res hVU u).val = valAt' x U u.val := by
  unfold res
  rw [Units.coe_map]
  exact valAt'_res x hVU h u.val
private theorem valAt'_unit_zpow' {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(W, U)ˣ)
    (n : ℤ) : valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by
  have e := congrArg Units.val (map_zpow (Units.map (valHom x U h).toMonoidHom) u n)
  rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at e
  exact e
end LC
section Rd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε))
end Rd
end GlobalTheory.AnValGenRd
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace GlobalTheory.AnValGenRd
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  unfold LB.LinComb
  dsimp only
  rw [val_prod p _ h]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [valAt'_unit_zpow' p _ h]
  congr 1
  exact (valAt'_res_unit_eq p _ h _).trans (valAt'_pullU_eq_valAt'_comp p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))
end GlobalTheory.AnValGenRd
