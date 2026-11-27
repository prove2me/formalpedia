-- Prove2me | solution 1 for GlobalTheory.isSMulRegular_coker_dualMap_of_exact_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:51.247373+00:00
-- url     : https://prove2.me/submissions/056cfbb5-aebf-4234-84ee-81d18cfd733a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_DualCokernel_extZero_retract
import Theorems.Thm_GlobalTheory_DualCokernel_coker_step
import Theorems.Thm_GlobalTheory_DualCokernel_extZero_self
import Theorems.Thm_GlobalTheory_DualCokernel_d_d_apply
import Theorems.Thm_GlobalTheory_DualCokernel_exact_fibre
import Theorems.Thm_GlobalTheory_DualCokernel_exists_homotopy
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_free
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
open GlobalTheory
open DualCokernel
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (ϖ : A) (g : ℕ),
      ϖ ∈ nonZeroDivisors A → IsRegularLocalRing (A ⧸ Ideal.span {ϖ}) →
      ringKrullDim (A ⧸ Ideal.span {ϖ}) = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ϖ ∈ p.asIdeal → ∃ (K : Type) (_ : Field K) (φ : A →+* K),
        RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      IsSMulRegular (Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ϖ := by
  intro A _ _ _ ϖ g hϖ hreg hg C hF ⟨n, hn⟩ hex
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hm : ϖ ∈ maximalIdeal A := by
    refine le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
      (Ideal.mem_span_singleton_self ϖ)
  have hDreg : ∀ i, IsSMulRegular (Module.Dual A (C.X i)) ϖ := fun i =>
    IsSMulRegular.of_right_eq_zero_of_smul fun f hf => LinearMap.ext fun x =>
      (mem_nonZeroDivisors_iff.mp hϖ).1 _ (LinearMap.congr_fun hf x)
  have hDext : ∀ i, ∀ j < g + 1, ExtZero (R := A) (Module.Dual A (C.X i)) j := fun i j hj =>
    FiniteLengthComplex.subsingleton_ext_free _ j (extZero_self ϖ g hϖ hm hg j hj) _
  have hdd : ∀ i j k f, (C.d i j).hom.dualMap ((C.d j k).hom.dualMap f) = 0 := fun i j k f => by
    ext x
    simp [d_d_apply]

  have hloc : ∀ i, ∀ p : Ideal A, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal A → ∃ s, s ∉ p ∧
      ∀ f, (C.d (i - 1) i).hom.dualMap f = 0 →
        s • f ∈ LinearMap.range (C.d i (i + 1)).hom.dualMap := by
    intro i p hp hϖp hpm
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨p, hp⟩ hϖp
    obtain ⟨t, ht, k₀, k₁, hk⟩ := exists_homotopy C hF n hn p
      (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i
    refine ⟨t, ht, fun f hf => ⟨k₁.dualMap f, LinearMap.ext fun x => ?_⟩⟩
    have h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0 := LinearMap.congr_fun hf (k₀ x)
    have h2 := congrArg f (hk x)
    rw [map_add, h1, zero_add, map_smul] at h2
    exact h2
  have key : ∀ k i, i + k = g →
      IsSMulRegular (Module.Dual A (C.X i) ⧸ LinearMap.range (C.d i (i + 1)).hom.dualMap) ϖ ∧
      ∀ j < i + 1, ExtZero (R := A)
        (Module.Dual A (C.X i) ⧸ LinearMap.range (C.d i (i + 1)).hom.dualMap) j := by
    intro k
    induction k with
    | zero =>
      rintro i rfl
      obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨maximalIdeal A, inferInstance⟩ hm
      obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField
        (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom)
        (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by
          exact exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1)
            (hK _ (Or.inr (by omega)))
      have hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x :=
        fun x => by simpa [d_d_apply] using LinearMap.congr_fun hst ((C.d i (i + 1)).hom x)
      let ι := (LinearMap.range (C.d i (i + 1)).hom.dualMap).liftQ
        (LinearMap.id - (C.d i (i + 1)).hom.dualMap ∘ₗ s.dualMap) (by
          rintro _ ⟨f, rfl⟩
          ext x
          simp [hds])
      have hι : (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ ∘ₗ ι = LinearMap.id := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
        refine (Submodule.Quotient.eq _).2 ⟨-s.dualMap f, ?_⟩
        simp [ι]
      have hinj : Injective ι := HasLeftInverse.injective ⟨_, LinearMap.congr_fun hι⟩
      exact ⟨(hDreg i).of_injective ι hinj,
        fun j hj => extZero_retract ι _ hι j (hDext i j hj)⟩
    | succ k ih =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih (i + 1) (by omega)
      refine coker_step ϖ hm _ _ (hdd _ _ _) (hDreg i) i (fun j hj => hDext i j (by omega)) h1 h2
        (hloc (i + 1)) fun p hp hϖp hpm => ?_
      obtain ⟨s, hs, hs'⟩ := hloc i p hp hϖp hpm
      refine ⟨s, hs, fun f ⟨y, hy⟩ => hs' f (hDreg _ ?_)⟩
      have := hdd (i - 1) i (i + 1) y
      rw [hy, map_smul] at this
      exact this.trans (smul_zero ϖ).symm
  exact (key g 0 (zero_add g)).1
end GlobalTheory
