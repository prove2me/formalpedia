-- Prove2me | solution 1 for GlobalTheory.FibreAcyclic.exact_hom_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:40.25399+00:00
-- url     : https://prove2.me/submissions/8683b7de-a9b9-4d96-bf69-59bead26dc6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
import Theorems.Thm_GlobalTheory_FibreAcyclic_extZero_hom
import Theorems.Thm_GlobalTheory_DualCokernel_d_d_apply
import Theorems.Thm_GlobalTheory_DualCokernel_eq_zero_of_extZero
import Theorems.Thm_GlobalTheory_DualCokernel_exact_fibre
import Theorems.Thm_GlobalTheory_DualCokernel_exists_homotopy
import Theorems.Thm_GlobalTheory_DualCokernel_extZero_coker
import Theorems.Thm_GlobalTheory_DualCokernel_extZero_retract
import Theorems.Thm_GlobalTheory_exists_homotopy_of_forall_exact_residueField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
namespace GlobalTheory.FibreAcyclic
theorem _root_.solution [IsNoetherianRing R] (N : Ideal R) (hN : N ≤ maximalIdeal R) (M : Type) [AddCommGroup M]
    [Module R M] (hM : ∀ s ∈ N, ∀ x : M, s • x = 0) (g : ℕ) (hE : ∀ j < g, ExtZero (R := R) M j)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (hF : ∀ i, Module.Free R (C.X i) ∧ Module.Finite R (C.X i))
    (n : ℕ) (hn : ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : Ideal R, p.IsPrime → N ≤ p → ∃ (K : Type) (_ : Field K) (φ : R →+* K),
      RingHom.ker φ = p ∧ ∀ i, (p ≠ maximalIdeal R ∨ g < i) →
        (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) :
    LinearMap.ker (LinearMap.lcomp R M (C.d 0 1).hom) ≤ LinearMap.range (LinearMap.lcomp R M (C.d 1 2).hom) := by
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  let δ := fun i j => LinearMap.lcomp R M (C.d i j).hom
  have hDext : ∀ i, ∀ j < g, ExtZero (R := R) (C.X i →ₗ[R] M) j := fun i j hj => extZero_hom M j (hE j hj) _
  have hdd : ∀ i j k f, δ i j (δ j k f) = 0 := fun i j k f => by
    ext x
    simp [δ, d_d_apply]
  have hloc : ∀ i, ∀ p : Ideal R, p.IsPrime → p ≠ maximalIdeal R → ∃ s, s ∉ p ∧
      ∀ f, δ (i - 1) i f = 0 → s • f ∈ LinearMap.range (δ i (i + 1)) := by
    intro i p hp hpm
    by_cases hNp : N ≤ p
    · obtain ⟨K, _, φ, hφ, hK⟩ := hex p hp hNp
      obtain ⟨t, ht, k₀, k₁, hk⟩ := exists_homotopy C hF n hn p
        (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i
      refine ⟨t, ht, fun f hf => ⟨f ∘ₗ k₁, LinearMap.ext fun x => ?_⟩⟩
      have h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0 := LinearMap.congr_fun hf (k₀ x)
      have h2 := congrArg f (hk x)
      rw [map_add, h1, zero_add, map_smul] at h2
      exact h2
    · obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hNp
      exact ⟨s, hsp, fun f _ => ⟨0, by ext x; simp [hM s hs]⟩⟩
  have key : ∀ k i, i + k = g →
      LinearMap.ker (δ i (i + 1)) ≤ LinearMap.range (δ (i + 1) (i + 1 + 1)) ∧
      ∀ j < i, ExtZero (R := R) ((C.X i →ₗ[R] M) ⧸ LinearMap.range (δ i (i + 1))) j := by
    intro k
    induction k with
    | zero =>
      rintro i rfl
      obtain ⟨K, _, φ, hφ, hK⟩ := hex (maximalIdeal R) inferInstance hN
      obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField
        (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom)
        (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by
          exact exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1)
            (hK _ (Or.inr (by omega)))
      have hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x :=
        fun x => by simpa [d_d_apply] using LinearMap.congr_fun hst ((C.d i (i + 1)).hom x)
      let ι := (LinearMap.range (δ i (i + 1))).liftQ
        (LinearMap.id - δ i (i + 1) ∘ₗ LinearMap.lcomp R M s) (by
          rintro _ ⟨f, rfl⟩
          ext x
          simp [δ, hds])
      have hι : (LinearMap.range (δ i (i + 1))).mkQ ∘ₗ ι = LinearMap.id := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
        refine (Submodule.Quotient.eq _).2 ⟨-(f ∘ₗ s), ?_⟩
        ext x
        simp [ι, δ]
      refine ⟨fun f hf => ⟨f ∘ₗ t, LinearMap.ext fun x => ?_⟩,
        fun j hj => extZero_retract ι _ hι j (hDext i j hj)⟩
      have h1 : f ((C.d i (i + 1)).hom (s x)) = 0 := LinearMap.congr_fun hf (s x)
      have h2 := congrArg f (LinearMap.congr_fun hst x)
      simpa [h1, δ] using h2
    | succ k ih =>
      intro i hi
      obtain ⟨-, h2⟩ := ih (i + 1) (by omega)
      have hker : LinearMap.ker (δ i (i + 1)) ≤ LinearMap.range (δ (i + 1) (i + 1 + 1)) := fun x hx => by
        refine (Submodule.Quotient.mk_eq_zero _).1 (eq_zero_of_extZero (h2 0 (by omega)) _ fun p hp hm => ?_)
        obtain ⟨s, hs, hs'⟩ := hloc (i + 1) p hp hm
        exact ⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2 (hs' x hx)⟩
      have hle : LinearMap.range (δ (i + 1) (i + 1 + 1)) ≤ LinearMap.ker (δ i (i + 1)) := by
        rintro _ ⟨y, rfl⟩
        exact hdd _ _ _ y
      exact ⟨hker, fun j hj =>
        extZero_coker ((LinearMap.range (δ (i + 1) (i + 1 + 1))).liftQ _ hle) (LinearMap.range (δ i (i + 1))).mkQ
          (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker))
          (Submodule.mkQ_surjective _)
          (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]) j
          (h2 _ (by omega)) (hDext i j (by omega))⟩
  exact (key g 0 (zero_add g)).1
end GlobalTheory.FibreAcyclic
