-- Prove2me | solution 1 for GlobalTheory.tensor_eq_zero_of_forall_geometric_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:53.888849+00:00
-- url     : https://prove2.me/submissions/1a528364-1584-4622-a89b-9728c519d7ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Theorems.Thm_GlobalTheory_exists_algHom_ker_eq_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] [IsReduced (TensorProduct O F A)] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] (t : TensorProduct O A M), (∀ φ : A →ₐ[O] F, TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) t = 0) → t = 0 := by
  intro O F _ _ _ _ hinj A _ _ _ _ _ M _ _ _ t ht
  classical
  haveI : IsArtinianRing (TensorProduct O F A) := IsArtinianRing.of_finite F _
  have hpt : ∀ m : MaximalSpectrum (TensorProduct O F A),
      ∃ ψ : TensorProduct O F A →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m.asIdeal := fun m =>
    haveI := m.isMaximal
    exists_algHom_ker_eq_of_isMaximal F _ m.asIdeal
  choose ψ hψ using hpt
  let φ : MaximalSpectrum (TensorProduct O F A) → (A →ₐ[O] F) := fun m =>
    ((ψ m).restrictScalars O).comp Algebra.TensorProduct.includeRight
  let L : A →ₗ[O] (MaximalSpectrum (TensorProduct O F A) → F) :=
    LinearMap.pi fun m => (φ m).toLinearMap
  have hR : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[O] TensorProduct O F A) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply hR
    rw [map_zero]
    have hmem : (Algebra.TensorProduct.includeRight a : TensorProduct O F A) ∈
        Ideal.jacobson (⊥ : Ideal (TensorProduct O F A)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hψ ⟨J, hJ⟩ _ (congrFun ha ⟨J, hJ⟩)
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := TensorProduct O F A)
    have h2 := Ideal.pow_mem_pow hmem n
    rw [hn] at h2
    exact IsNilpotent.eq_zero ⟨n, by simpa using h2⟩
  have hLM : Function.Injective (L.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap L hL
  haveI : Fintype (MaximalSpectrum (TensorProduct O F A)) := Fintype.ofFinite _
  apply hLM
  rw [map_zero]
  apply (TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)).injective
  rw [map_zero]
  funext m
  have key : ∀ s : TensorProduct O A M,
      TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)
        (L.rTensor M s) m
      = TensorProduct.map (φ m).toLinearMap (LinearMap.id : M →ₗ[O] M) s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [L, TensorProduct.piLeft]
    | add s s' h h' => rw [map_add, map_add, Pi.add_apply, h, h', map_add]
  rw [key, ht]
  rfl
end GlobalTheory
