-- Prove2me | solution 1 for GlobalTheory.heisenberg_weightSpace_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:53.750541+00:00
-- url     : https://prove2.me/submissions/c24fcc5c-a31a-4921-a199-f495afcf325a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_exists_comm_eq
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_mem_weightSpace_iff
import Theorems.Thm_GlobalTheory_finiteAbelian_weightDecomposition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open HeisenbergWeightDim
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → (⨆ χ, Wt χ = ⊤) ∧ ∀ χ, Module.finrank F (Wt χ) * Nat.card T = Module.finrank F E := by
  intro F _ _ A _ _ E _ _ _ e Φ hA hdim hm hc hn T lam hlam Wt hWt
  classical
  have hpos : 0 < Nat.card A := Nat.card_pos
  haveI : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hdim
      omega
    · exact h
  haveI : NeZero ((Nat.card A : ℕ) : F) := ⟨hA⟩
  haveI : NeZero (Nat.card A) := ⟨hpos.ne'⟩
  haveI h0 : HasEnoughRootsOfUnity F (Nat.card A) := inferInstance
  haveI hAe : HasEnoughRootsOfUnity F (Monoid.exponent A) :=
    h0.of_dvd F Group.exponent_dvd_nat_card
  haveI : HasEnoughRootsOfUnity F (Monoid.exponent T) :=
    hAe.of_dvd F (Monoid.exponent_submonoid_dvd T.toSubmonoid)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (Nat.card A)
  let ρ : Representation F T E :=
    { toFun := fun t => (lam t : E →ₗ[F] E)
      map_one' := by ext v; simp
      map_mul' := by intro s t; ext v; simp }
  obtain ⟨hfin, hint, -⟩ := finiteAbelian_weightDecomposition F (Nat.card A) ζ hpos
    (IsUnit.mk0 _ hA) hζ T (fun t => Subtype.ext (by simp)) E ρ
  have hW : (fun c : T →* Fˣ => ⨅ t, LinearMap.ker (ρ t - (c t : F) • LinearMap.id)) = Wt := by
    funext c
    ext v
    rw [hWt, FiniteAbelianWeights.mem_weightSpace_iff]
    rfl
  rw [hW] at hint
  refine ⟨hint.submodule_iSup_eq_top, ?_⟩
  have hle : ∀ χ ψ, Module.finrank F (Wt χ) ≤ Module.finrank F (Wt ψ) := by
    intro χ ψ
    obtain ⟨a, ha⟩ := exists_comm_eq hm hc hn T (ψ * χ⁻¹)
    have hmap : (Wt χ).map (Φ a : E →ₗ[F] E) ≤ Wt ψ := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hWt]
      intro t
      obtain ⟨c, h⟩ := hlam t
      have h1 := (hWt χ v).1 hv t
      simp only [LinearEquiv.coe_coe]
      rw [h, hc, smul_comm, ← map_smul, ← h, h1, map_smul, smul_smul, ha, ← Units.val_mul]
      simp
    exact (LinearEquiv.finrank_map_eq (Φ a) (Wt χ)).symm.le.trans (Submodule.finrank_mono hmap)
  intro χ
  haveI := Fintype.ofFinite (T →* Fˣ)
  have h1 : Module.finrank F E = ∑ ψ, Module.finrank F (Wt ψ) := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap Wt) hint).finrank_eq,
      Module.finrank_directSum]
  rw [h1, Finset.sum_congr rfl (fun ψ _ => le_antisymm (hle ψ χ) (hle χ ψ)), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T F, smul_eq_mul, mul_comm]
end GlobalTheory
