-- Prove2me | solution 1 for GlobalTheory.SignedLengthMapLogDet.exists_relLength_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:15:05.511374+00:00
-- url     : https://prove2.me/submissions/3338cc82-0b68-48c8-b9a5-51709d3d01ab

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_length_coker_eq_ord_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.SignedLengthMapLogDet
theorem _root_.solution (A : Submodule R V) [Submodule.IsLattice K A] (φ : V →ₗ[K] V)
    (hφ : LinearMap.det φ ≠ 0) (hA : ∀ x ∈ A, φ x ∈ A) :
    ∃ n : ℕ, relLength A (A.map (φ.restrictScalars R)) = n ∧
      Ring.ordFrac R (LinearMap.det φ) = WithZero.exp (n : ℤ) := by
  classical
  let b := Module.Free.chooseBasis R A
  let c := b.extendOfIsLattice K
  have : Module.Finite K V := Module.Finite.of_basis c
  let f : A →ₗ[R] A := (φ.restrictScalars R).restrict hA
  have hinj : Function.Injective φ :=
    ((LinearMap.isUnit_iff_isUnit_det φ).mpr hφ.isUnit |> (Module.End.isUnit_iff φ).mp).1
  have hf : Function.Injective f := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have hdet : LinearMap.det φ = algebraMap R K (LinearMap.det f) := by
    rw [← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]
    congr 1
    ext i j
    have : φ (c j) = ∑ k, algebraMap R K (b.repr (f (b j)) k) • c k := by
      have h1 : φ (c j) = (f (b j) : V) := by
        rw [Basis.extendOfIsLattice_apply]; rfl
      have h2 := congrArg Subtype.val (b.sum_repr (f (b j)))
      rw [h1, ← h2, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Basis.extendOfIsLattice_apply, algebraMap_smul, Submodule.coe_smul]
    rw [LinearMap.toMatrix_apply, this, c.repr_sum_self]
    simp [LinearMap.toMatrix_apply]
  have hf0 : LinearMap.det f ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet
    exact hφ hdet
  have hnz := mem_nonZeroDivisors_of_ne_zero hf0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  refine ⟨n, ?_, ?_⟩
  · have : (A.map (φ.restrictScalars R)).submoduleOf A = LinearMap.range f := by
      ext x
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨⟨y, hy⟩, Subtype.ext h⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [relLength_def, this, length_coker_eq_ord_det f hf, hn]
  · rw [hdet, Ring.ordFrac_eq_ord R hf0, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm]
    rfl
end GlobalTheory.SignedLengthMapLogDet
