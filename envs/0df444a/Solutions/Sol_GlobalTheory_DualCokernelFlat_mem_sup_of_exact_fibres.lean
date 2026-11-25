-- Prove2me | solution 1 for GlobalTheory.DualCokernelFlat.mem_sup_of_exact_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:47.039165+00:00
-- url     : https://prove2.me/submissions/f3110343-5bf5-4e73-9dce-3d8dbd7bc3d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_DualCokernelFlat_mem_sup_of_exact
import Theorems.Thm_GlobalTheory_exact_dualMap_of_exact_fibres_of_isRegularLocalRing


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
open GlobalTheory.DualCokernelFlat
namespace GlobalTheory.DualCokernelFlat
theorem _root_.solution {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsRegularLocalRing B] (π : A →+* B) (hs : Surjective π) (g : ℕ) (hg : ringKrullDim B = g)
    (C : CochainComplex (ModuleCat.{0} A) ℕ)
    (hF : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))
    (hn : ∃ n, ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : PrimeSpectrum A, RingHom.ker π ≤ p.asIdeal → ∃ (K : Type) (_ : Field K)
      (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
        ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i)
    (i : ℕ) (x : Module.Dual A (C.X (i + 1)))
    (hx : (C.d i (i + 1)).hom.dualMap x ∈
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X i)))) :
    x ∈ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ⊔
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X (i + 1)))) := by
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  let := π.toAlgebra
  have key := GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing B g hg (((ModuleCat.extendScalars π).mapHomologicalComplex _).obj C)
    (fun i => ⟨inferInstanceAs (Module.Free B (B ⊗[A] C.X i)),
      inferInstanceAs (Module.Finite B (B ⊗[A] C.X i))⟩)
    (hn.imp fun n h i hi => (ModuleCat.extendScalars π).map_isZero (h i hi)) (fun q => ?_) i
  · exact mem_sup_of_exact (B := B) hs _ _ key x hx
  obtain ⟨K, _, φ, hφ, hK⟩ := hex (q.comap π) (by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le)
  have hle : RingHom.ker π ≤ RingHom.ker φ := by
    rw [hφ, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  obtain ⟨ψ, rfl⟩ : ∃ ψ : B →+* K, ψ.comp π = φ :=
    ⟨π.liftOfSurjective hs ⟨φ, hle⟩, π.liftOfSurjective_comp hs _⟩
  refine ⟨K, inferInstance, ψ, ?_, fun j hj => ?_⟩
  · apply Ideal.comap_injective_of_surjective π hs
    rw [RingHom.comap_ker, hφ]
    rfl
  · refine (hK j (hj.imp_left fun h h' => h ?_)).of_iso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp π ψ) _).app C)
    have hm : (q.asIdeal.comap π).IsMaximal := by
      have : q.asIdeal.comap π = IsLocalRing.maximalIdeal A := h'
      rw [this]
      infer_instance
    have := (Ideal.comap_isMaximal_of_surjective π hs (K := IsLocalRing.maximalIdeal B))
    apply Ideal.comap_injective_of_surjective π hs
    rw [IsLocalRing.eq_maximalIdeal hm, IsLocalRing.eq_maximalIdeal this]
end GlobalTheory.DualCokernelFlat
