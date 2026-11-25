-- Prove2me | solution 1 for GlobalTheory.SS.exists_goodOpen_of_weight_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:03.531486+00:00
-- url     : https://prove2.me/submissions/7a8d886b-3b9d-4c4f-a5b8-1c29dcc6dc28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
import Theorems.Thm_GlobalTheory_SS_TorusSlice_ch_mul
import Theorems.Thm_GlobalTheory_SS_TorusSlice_ch_comp
import Theorems.Thm_GlobalTheory_SS_TorusSlice_ext_basis
import Theorems.Thm_GlobalTheory_SS_TorusSlice_exists_of_basis
import Theorems.Thm_GlobalTheory_SS_TorusSlice_appLE_comp_top
import Theorems.Thm_GlobalTheory_SS_TorusSlice_exists_goodOpen
import Theorems.Thm_GlobalTheory_SS_TorusSlice_exists_point

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS
open TorusSlice
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ χ : X, ∃ (U : G.left.Opens) (u : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit u ∧ Wt i U u χ) → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) := by
  intro k _ _ G _ hG X _ _ _ i hi H x
  obtain ⟨-, hsm, hsep, -, -⟩ := hG
  let b := Module.Free.chooseBasis ℤ X
  choose U u hne hu hw using H
  obtain ⟨p, hp⟩ := exists_point G (Z := closure {x}) ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  choose y hy using fun χ => exists_point G (hne χ) (U χ).isOpen.isLocallyClosed
  let ρ : X → (G ⟶ G) := fun χ => 𝟙 G * (toUnit G ≫ (p⁻¹ * y χ))
  have hρ : ∀ χ, p ≫ ρ χ = y χ := fun χ => by
    simp only [ρ, MonObj.comp_mul]
    rw [← Category.assoc, ← Category.assoc, toUnit_unique (p ≫ toUnit G) (𝟙 _)]
    simp
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  let O : G.left.Opens := ⟨⋂ n, ((ρ (b n)).left ⁻¹ᵁ U (b n) : G.left.Opens),
    isOpen_iInter_of_finite fun n => TopologicalSpace.Opens.isOpen _⟩
  have hO : p.left pt ∈ O := Set.mem_iInter.2 fun n => by
    change (ρ (b n)).left (p.left pt) ∈ U (b n)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hρ]
    exact hy _ _
  obtain ⟨Y₀, hY₀, hpY, hYO⟩ := exists_isAffineOpen_mem_and_subset hO
  let Y : Over (Sp k) := Over.mk (Y₀.ι ≫ G.hom)
  let j : Y ⟶ G := Over.homMk Y₀.ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion Y₀.ι)
  have : IsAffine Y.left := hY₀
  have hr : Set.range p.left ⊆ Set.range Y₀.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) s pt]
    exact hpY
  let y₀ : 𝟙_ (Over (Sp k)) ⟶ Y := Over.homMk (IsOpenImmersion.lift Y₀.ι p.left hr)
    ((IsOpenImmersion.lift_fac_assoc _ _ hr _).trans (Over.w p))
  have hy₀ : y₀ ≫ j = p := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ hr)
  have hle : ∀ n, ⊤ ≤ (j ≫ ρ (b n)).left ⁻¹ᵁ U (b n) := fun n z _ => by
    change (j ≫ ρ (b n)).left z ∈ U (b n)
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact Set.mem_iInter.1 (hYO z.2) n
  obtain ⟨σ, hσ⟩ := exists_of_basis (Z := Y) b fun n =>
    ((hu (b n)).map ((j ≫ ρ (b n)).left.appLE (U (b n)) ⊤ (hle n)).hom).unit
  have hE : Equivar i j σ := fun Z t a a' h => ext_basis b fun n => by
    have pre : ∀ c : Z ⟶ Y, ⊤ ≤ (c ≫ j ≫ ρ (b n)).left ⁻¹ᵁ U (b n) := fun c z _ => by
      change (c ≫ j ≫ ρ (b n)).left z ∈ U (b n)
      rw [Over.comp_left, Scheme.Hom.comp_apply]
      exact hle n (Set.mem_univ _)
    have e : (t ≫ i) * (a ≫ j ≫ ρ (b n)) = a' ≫ j ≫ ρ (b n) := by
      rw [← Category.assoc, ← Category.assoc a']
      simp only [ρ, MonObj.comp_mul (a ≫ j), MonObj.comp_mul (a' ≫ j), Category.comp_id]
      rw [← _root_.mul_assoc, ← h, ← Category.assoc, ← Category.assoc,
        toUnit_unique ((a ≫ j) ≫ toUnit G) ((a' ≫ j) ≫ toUnit G)]
    have := hw (b n) Z t (a ≫ j ≫ ρ (b n)) (e ▸ pre a') (pre a)
    rw [appLE_comp_top a' _ _ e _ _ (hle n), appLE_comp_top a _ _ rfl _ _ (hle n)] at this
    rw [ch_mul, ch_comp, ch_comp, hσ, IsUnit.unit_spec]
    exact this
  obtain ⟨V, hV, hpV⟩ := exists_goodOpen i j σ hE y₀
  rw [hy₀] at hpV
  obtain ⟨z, hz, rfl⟩ := mem_closure_iff.1 (hp pt) V V.isOpen (hpV pt)
  exact ⟨V, hz, hV⟩
end GlobalTheory.SS
