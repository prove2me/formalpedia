-- Prove2me | solution 1 for GlobalTheory.ExpansionTotal.secLin_of_secScal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:06:03.388368+00:00
-- url     : https://prove2.me/submissions/8588d758-f049-41f7-81b2-a69f192299ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal
import Theorems.Thm_GlobalTheory_FieldBaseChange_secLin_iff_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)
omit [Algebra (FractionRing R) F]
namespace GlobalTheory.ExpansionTotal
theorem _root_.solution {X Y Y' W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₀ K K₁ : Type} [Fintype K₀] [Fintype K]
    [Fintype K₁] {φ₀ : K₀ → (W ⟶ X)} {ε₀ : K₀ → ℤ} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ₁ : K₁ → (Y' ⟶ X)}
    {ε₁ : K₁ → ℤ} {h : Y ⟶ W} (p : Y' ⟶ Y) {h' : Y' ⟶ W} (hh : h' = p ≫ h) {ρ : Y ⟶ Spec (CommRingCat.of R)}
    {π : Y' ⟶ Spec (CommRingCat.of F)} (g : R →+* F) (hπ : p ≫ ρ = π ≫ Spec.map (CommRingCat.ofHom g)) {n : ℕ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {v : Fin n → LB.Sec (LB.LinComb L φ ε)}
    {σ : Fin n → LB.Sec (LB.LinComb L φ₀ ε₀)} {c d : Fin n → F} {r : Fin n → R} (hd : ∀ i, d i * g (r i) = c i)
    (hσ : ∀ i, GeneratorPullback.SecScal L φ ε (v i) φ₀ ε₀ (σ i) h (scal ρ (r i)))
    (hs : ∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = ∑ i, constVal (𝟙 Y' ≫ π) y (c i) * sval (v i) (𝟙 Y' ≫ p) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₀ ε₀ σ h' (fun i => scal π (d i)) := by
  subst hh
  refine (secLin_iff_val hL s₁ σ _ _).2 fun y J hJ => (hs y J hJ).trans (Finset.sum_congr rfl fun i _ => ?_)
  have key : ∀ q : Y' ⟶ Y, sval (σ i) (q ≫ h) y J = gs q y ⊤ (scal ρ (r i)) * sval (v i) q y J := fun q => by
    rw [sval_of (σ i) (q ≫ h) y J (fun k => J (q ≫ h ≫ φ₀ k)) (fun k => by rw [Category.assoc])]
    have hm : q y ∈ LB.wchart L φ (fun k => J (q ≫ φ k)) ⊓
        LB.wchart L (fun k => h ≫ φ₀ k) (fun k => J (q ≫ h ≫ φ₀ k)) :=
      ⟨hJ.mem φ q, hJ.mem (fun k => h ≫ φ₀ k) q⟩
    have e := congrArg (gs q y _) (hσ i (fun k => J (q ≫ φ k)) (fun k => J (q ≫ h ≫ φ₀ k)) (by
      rintro (a | a) (b | b) e <;> exact congrArg (fun t => J (q ≫ t)) e))
    exact ((gs_res q y _ hm _).trans (gs_pull q h y (LB.wchart L φ₀ (fun k => J (q ≫ h ≫ φ₀ k)))
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
      (e.trans ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res q y le_top hm _) (gs_res q y _ hm _))))
  rw [← Category.assoc, key, gs_scal, gs_scal, Category.assoc, hπ, ← Category.assoc, constVal_specMap,
    ← _root_.mul_assoc, ← hd i]
  congr 1
  exact (congrArg (gs _ y ⊤) (map_mul _ _ _)).trans (gs_mul _ y ⊤ trivial _ _)
end GlobalTheory.ExpansionTotal
