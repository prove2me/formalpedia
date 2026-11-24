-- Prove2me | solution 1 for GlobalTheory.SymmetricSemicharacter.exists_symmetry_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:57.070678+00:00
-- url     : https://prove2.me/submissions/ebc132e6-cc1c-4340-99ed-1c496e17a727

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_ex_neg_left
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_CubeValues_val_gen
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero


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
open GlobalTheory.SymmetricSemicharacter
open CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.SymmetricSemicharacter
theorem _root_.solution (hv : ValueRules) (hs : Out.Sym A L) :
    ∃ T : L.ι → L.ι → (Fin g → ℂ) → ℂ,
      (∀ i j, DifferentiableOn ℂ (T i j)
        {z | ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j}) ∧
      (∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j → T i j z ≠ 0) ∧
      (∀ i j i' j' z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
        ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i' → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j' →
        T i j z = valAt' (u.ex (-z)).left (L.U i ⊓ L.U i') (L.g i i').val *
          (valAt' (u.ex z).left (L.U j ⊓ L.U j') (L.g j j').val)⁻¹ * T i' j' z) ∧
      ∀ i j z (l : u.Λ), T i j (z + l) = T i j z := by
  obtain ⟨U, hU, t, ht⟩ := hs (default : PrimeSpectrum ℂ)
  have hr : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    have : A.hom x = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    change A.hom x ∈ U
    rw [this]
    exact hU
  obtain ⟨σ, hσ⟩ : ∃ σ : A.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, σ ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  revert t
  set φ : Fin 2 → ((A.hom ⁻¹ᵁ U).toScheme ⟶ A.left) :=
    ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] with hφ
  intro t ht
  have h0 : ∀ z, ((u.ex z).left ≫ σ) ≫ φ 0 = (u.ex (-z)).left := fun z => by
    simp only [hφ, Matrix.cons_val_zero, Category.assoc, reassoc_of% hσ, ex_neg_left]
  have h1 : ∀ z, ((u.ex z).left ≫ σ) ≫ φ 1 = (u.ex z).left := fun z => by
    simp only [hφ, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc, hσ, Category.comp_id]
  have hch : ∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
      ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ L.wchart φ ![i, j] := fun i j z hi hj => by
    refine (le_preimage_wchart ((u.ex z).left ≫ σ) L φ _).2 ?_
    rw [Fin.forall_fin_two]
    exact ⟨(h0 z).symm ▸ hi, (h1 z).symm ▸ hj⟩
  refine ⟨fun i j z => valAt' ((u.ex z).left ≫ σ) (L.wchart φ ![i, j]) (t.s ![i, j]).val,
    fun i j => ?_, fun i j z hi hj => ?_, fun i j i' j' z hi hj hi' hj' => ?_, fun i j z l => ?_⟩
  · have h := (u.hol (σ ⁻¹ᵁ L.wchart φ ![i, j]) ((σ.app _).hom (t.s ![i, j]).val)).2
    refine (h.mono fun z hz => hch i j z hz.1 hz.2).congr fun z _ => ?_
    exact ((hv _ (u.ex z).left).2.2.2.1 _ σ _ _).symm
  · exact val_unit_ne_zero _ hv (hch i j z hi hj) _
  · have k1 := hch i j z hi hj
    have k2 := hch i' j' z hi' hj'
    refine (val_gen _ hv t ht _ _ k1 k2).trans ?_
    congr 1
    refine (val_linComb ((u.ex z).left ≫ σ) hv L φ _ _ _ k1 k2).trans ?_
    rw [Fin.prod_univ_two, h0, h1]
    simp
  · simp only [ex_add_period u z l l.2]
end GlobalTheory.SymmetricSemicharacter
