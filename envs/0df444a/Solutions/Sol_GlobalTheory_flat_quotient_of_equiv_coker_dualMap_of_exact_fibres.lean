-- Prove2me | solution 1 for GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:08.785508+00:00
-- url     : https://prove2.me/submissions/4f5ec8ae-c163-4b19-8114-4ccd90cdf42a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_DualCokernelFlat_mem_sup_of_exact_fibres
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_linearEquiv
import Theorems.Thm_GlobalTheory_flat_coker_of_complex_exact_mod_maximalIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory
open DualCokernelFlat
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A]
      [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)]
      [Module.Flat V A] (g : ℕ),
      IsRegularLocalRing (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) →
      ringKrullDim (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) ≤ p.asIdeal →
        ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
          ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ I : Ideal A, Nonempty ((Module.Dual A (C.X 0) ⧸
        LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] (A ⧸ I)) → Module.Flat V (A ⧸ I) := by
  intro V A _ _ _ _ _ _ _ _ _ g hreg hg C hF hn hex I ⟨e⟩
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hflat : ∀ i, Module.Flat V (Module.Dual A (C.X i)) := fun i => Module.Flat.trans V A _
  have key := mem_sup_of_exact_fibres (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective g hg C hF
    hn (by rw [Ideal.mk_ker]; exact hex)
  rw [Ideal.mk_ker] at key
  have h := GlobalTheory.flat_coker_of_complex_exact_mod_maximalIdeal V A (fun i => Module.Dual A (C.X i))
    (fun i => (C.d i (i + 1)).hom.dualMap) (fun i f => ?_) (hn.imp fun n h i hi => ?_) key
  · exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm
  · ext x
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← LinearMap.comp_apply (C.d _ _).hom,
      ← ModuleCat.hom_comp, C.d_comp_d]
    simp
  · have := ModuleCat.subsingleton_of_isZero (h i hi)
    infer_instance
end GlobalTheory
