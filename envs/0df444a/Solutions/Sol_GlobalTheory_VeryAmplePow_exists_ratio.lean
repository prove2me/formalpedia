-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:50.357644+00:00
-- url     : https://prove2.me/submissions/6ab5c216-1533-4605-b74d-a580608e4a17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_gs
import Theorems.Thm_P2M_GlobalTheory_VeryAmplePow_sec_trans__22f5df49d8af
import Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_iff_mem

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
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Y : Scheme.{0}} {M : LB Y} (s t : LB.Sec M) :
    ∃ ρ : Γ(Y, nonzeroLocus s), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ nonzeroLocus s → r z ∈ M.U k →
      gs r z _ (t.f k) = gs r z _ ρ * gs r z _ (s.f k) := by
  let V : M.ι → Y.Opens := fun k => Y.basicOpen (s.f k)
  obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(Y, V k), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ V k →
      gs r z _ (t.f k) = gs r z _ (u k) * gs r z _ (s.f k) := by
    have hs : ∀ k, IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le (s.f k) : V k ≤ M.U k)).op).hom (s.f k)) :=
      fun k => Y.toRingedSpace.isUnit_res_basicOpen (s.f k)
    choose w hw using fun k => (hs k).exists_left_inv
    refine ⟨fun k => (Y.presheaf.map (homOfLE (Y.basicOpen_le (s.f k))).op).hom (t.f k) * w k, fun Z r z k hz => ?_⟩
    have e := congrArg (gs r z (V k)) (hw k)
    have e' : gs r z (V k) (w k) * gs r z _ (s.f k) = 1 := by
      refine Eq.trans ?_ (e.trans (by rw [gs_eq r z _ hz, map_one, map_one]))
      exact ((gs_mul r z _ hz _ _).trans (congrArg _ (gs_res r z (Y.basicOpen_le (s.f k)) hz _))).symm
    rw [gs_mul r z _ hz, gs_res r z _ hz, _root_.mul_assoc, e', _root_.mul_one]
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' V (nonzeroLocus s) (fun k => homOfLE (le_iSup V k)) le_rfl u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Y) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Y) z inf_le_right hz _).symm)
      have h₁ : (𝟙 Y : Y ⟶ Y) z ∈ M.U j := Y.basicOpen_le _ hz.1
      have h₂ : (𝟙 Y : Y ⟶ Y) z ∈ M.U j' := Y.basicOpen_le _ hz.2
      have e₁ := hu _ (𝟙 Y) z j hz.1
      rw [sec_trans' t _ z h₁ h₂, sec_trans' s _ z h₁ h₂, hu _ (𝟙 Y) z j' hz.2, mul_left_comm (gs _ _ _ (u j)),
        Units.mul_right_inj] at e₁
      exact (((isUnit_gs (𝟙 Y) z _ h₂ _).2 hz.2).mul_left_inj.1 e₁).symm)
  refine ⟨a, fun Z r z k h hk => ?_⟩
  have hz : r z ∈ V k := (isUnit_gs r z _ hk _).1 ((isUnit_iff_mem s r z hk).2 h)
  rw [hu Z r z k hz, ← ha k]
  exact congrArg (· * _) (gs_res r z (le_iSup V k) hz a)
end GlobalTheory.VeryAmplePow
