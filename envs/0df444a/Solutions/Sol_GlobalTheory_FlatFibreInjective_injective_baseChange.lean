-- Prove2me | solution 1 for GlobalTheory.FlatFibreInjective.injective_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:11.321281+00:00
-- url     : https://prove2.me/submissions/0a2979e3-8e33-413c-9479-cac1805d2fb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Theorems.Thm_GlobalTheory_FlatFibreInjective_one_tmul_ne_zero
import Theorems.Thm_GlobalTheory_FlatFibreInjective_one_tmul_eq_zero
import Theorems.Thm_GlobalTheory_FlatFibreInjective_exists_of_torsion

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
open GlobalTheory GlobalTheory.FlatFibreInjective
open TensorProduct
namespace GlobalTheory.FlatFibreInjective
theorem _root_.solution :
    ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R]
      [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀]
      [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁),
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k],
        Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R) := by
  intro R₀ R C₀ C₁ _ _ _ _ _ _ _ _ _ _ φ H
  change Function.Injective (φ.lTensor R)
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  haveI : Nontrivial (LinearMap.ker (φ.lTensor R)) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R₀ (LinearMap.ker (φ.lTensor R))
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, ⟨x, hx0⟩, hx⟩ := hp
  have hann : ∀ a : R₀, a • x = 0 ↔ a ∈ p := by
    intro a
    rw [hx]
    simp [Submodule.mem_colon_singleton]
  let M := Submodule.torsionBySet R₀ R p
  obtain ⟨y, rfl⟩ : ∃ y, M.subtype.rTensor C₀ y = x :=
    exists_of_torsion p (IsNoetherian.noetherian p) x (fun a ha => (hann a).2 ha)
  have hy0 : φ.lTensor M y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) M.subtype M.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor]
    exact hx0
  have hkill : ∀ a : R₀, (∀ m : M, a • m = 0) → ∀ z : M ⊗[R₀] C₀, a • z = 0 := by
    intro a ha z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => rw [smul_tmul', ha, zero_tmul]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  have hy : ∀ a : R₀, a • y = 0 → a ∈ p := by
    intro a ha
    rw [← hann, ← map_smul, ha, map_zero]
  have hcm : (p.map (algebraMap R₀ R)).comap (algebraMap R₀ R) = p := by
    refine le_antisymm ?_ Ideal.le_comap_map
    intro a ha
    refine hy a (hkill a (fun m => ?_) y)
    have hle : p.map (algebraMap R₀ R) ≤ LinearMap.ker (LinearMap.toSpanSingleton R R m) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      have := (Submodule.mem_torsionBySet_iff _ _).1 m.2 ⟨b, hb⟩
      simpa [Algebra.smul_def] using this
    have := hle ha
    apply Subtype.ext
    simpa [Algebra.smul_def] using this
  obtain ⟨q, hq, hqp⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).1 hcm
  refine one_tmul_ne_zero (k := q.ResidueField) p ?_ ?_ y hy
    (one_tmul_eq_zero φ (H q.ResidueField) y hy0)
  · intro a
    rw [IsScalarTower.algebraMap_apply R₀ R q.ResidueField, Ideal.algebraMap_residueField_eq_zero,
      ← hqp]
    rfl
  · intro z a
    refine hkill a (fun m => Subtype.ext ?_) z
    exact (Submodule.mem_torsionBySet_iff _ _).1 m.2 a
end GlobalTheory.FlatFibreInjective
