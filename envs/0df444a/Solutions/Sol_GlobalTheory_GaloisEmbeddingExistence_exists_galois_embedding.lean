-- Prove2me | solution 1 for GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:35.45218+00:00
-- url     : https://prove2.me/submissions/13675279-74e9-4407-89b9-e43f4349a201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGaloisEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GaloisEmbeddingExistence
namespace GlobalTheory.GaloisEmbeddingExistence
theorem _root_.solution (R R' : Type) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R']
    (hinj : Function.Injective (algebraMap R R')) :
    ∃ (L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R))),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
        ∃ (j : R' →ₐ[R] L), Function.Injective j := by
  classical
  set K := FractionRing R
  set Ω := AlgebraicClosure K
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
  have hΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2 hΩ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let φ : R' →ₐ[R] Ω := IsAlgClosed.lift
  have hφ : Function.Injective φ := by
    have h1 : (RingHom.ker φ).comap (algebraMap R R') = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hx
      exact hΩ (by simpa using hx)
    have h2 : RingHom.ker φ = ⊥ := Ideal.eq_bot_of_comap_eq_bot h1
    exact (RingHom.injective_iff_ker_eq_bot φ).2 h2
  obtain ⟨s, hs⟩ := (Module.finite_def.1 (inferInstance : Module.Finite R R'))
  let M : IntermediateField K Ω := IntermediateField.adjoin K (φ '' (s : Set R'))
  haveI : Finite (φ '' (s : Set R')) := (s.finite_toSet.image φ).to_subtype
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hmem : ∀ x : R', φ x ∈ L := by
    intro x
    have hx : x ∈ Submodule.span R (s : Set R') := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact hML (IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩)
    | zero => simpa using L.zero_mem
    | add x y _ _ hx hy => simpa using L.add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply R K Ω]
      exact L.mul_mem (L.algebraMap_mem _) hx
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  let j : R' →ₐ[R] L :=
    { toFun := fun x => ⟨φ x, hmem x⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (map_add φ x y)
      commutes' := fun r => Subtype.ext (φ.commutes r) }
  exact ⟨j, fun x y h => hφ (congrArg Subtype.val h)⟩
end GlobalTheory.GaloisEmbeddingExistence
