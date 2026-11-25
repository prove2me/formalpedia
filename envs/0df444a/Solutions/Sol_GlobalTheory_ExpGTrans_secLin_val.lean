-- Prove2me | solution 1 for GlobalTheory.ExpGTrans.secLin_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:49:43.38996+00:00
-- url     : https://prove2.me/submissions/2cd01f39-214d-4d13-b07b-9884c18342bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ExpGTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
section Generic
variable {X X' Y Y' Y₁ Y₁' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K' : Type} [Fintype K] [Fintype K']
private theorem gs_sum_lemma {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {n : ℕ}
    (a : Fin n → Γ(Y, U)) : gs f z U (∑ i, a i) = ∑ i, gs f z U (a i) := by
  simp only [gs_eq _ _ _ h, map_sum]
end Generic
section Fam
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {D : DegPre R} {D' : DegPre R'}
end Fam
end GlobalTheory.ExpGTrans
namespace GlobalTheory
end GlobalTheory
end
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpGTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
variable {X X' Y Y' Y₁ Y₁' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.ExpGTrans
theorem _root_.solution {φ₁ : K' → (Y₁ ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y₁ ⟶ Y} {c : Fin n → Γ(Y₁, ⊤)}
    (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y₁) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  unfold GeneratorPullback.SecLin LB.Coh at H
  set j₁ : K' → L.ι := fun κ => J (r ≫ φ₁ κ) with hj₁
  set j₂ : K → L.ι := fun κ => J ((r ≫ h) ≫ φ κ) with hj₂
  have hsum : ∀ k, Sum.elim j₁ j₂ k = J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ k) k) := by
    rintro (a | a)
    · rfl
    · simp only [Sum.elim_inr, j₂, Category.assoc]
  have E := H j₁ j₂ fun k₁ k₂ e => by rw [hsum, hsum, e]
  have m₁ : r z ∈ L.wchart φ₁ j₁ := hJ.mem φ₁ r
  have m₂ : r z ∈ L.wchart (fun k => h ≫ φ k) j₂ := by
    have e : (fun k => J (r ≫ h ≫ φ k)) = j₂ := funext fun k => by simp only [j₂, Category.assoc]
    exact e ▸ hJ.mem (fun k => h ≫ φ k) r
  have m₃ : (r ≫ h) z ∈ L.wchart φ j₂ := hJ.mem φ (r ≫ h)
  have hV : r z ∈ L.wchart φ₁ j₁ ⊓ L.wchart (fun k => h ≫ φ k) j₂ := ⟨m₁, m₂⟩
  refine (sval_of s₁ r z J j₁ (fun _ => rfl)).trans ?_
  refine ((gs_res r z inf_le_left hV _).symm.trans (congrArg (gs r z _) E)).trans ?_
  rw [gs_sum_lemma r z _ hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul r z _ hV, sval_of (s i) (r ≫ h) z J j₂ (fun _ => rfl)]
  congr 1
  · simp only [resTop]
    exact gs_res r z le_top hV _
  · rw [gs_res r z _ hV]
    exact gs_pull r h z _ m₃ _
end GlobalTheory.ExpGTrans
