-- Prove2me | solution 1 for GlobalTheory.DualCokernel.exists_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:00.65508+00:00
-- url     : https://prove2.me/submissions/792757a6-3b11-4bfd-a898-e843b4cdcc19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_DualCokernel_exists_homotopy_step
import Theorems.Thm_GlobalTheory_DualCokernel_d_d_apply

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
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
namespace GlobalTheory.DualCokernel
theorem _root_.solution (hF : ∀ i, Module.Free R (C.X i) ∧ Module.Finite R (C.X i))
    (n : ℕ) (hn : ∀ i, n < i → IsZero (C.X i)) (p : Ideal R) [hp : p.IsPrime]
    (h : ∀ i, Exact ((C.d (i - 1) i).hom.lTensor p.ResidueField)
      ((C.d i (i + 1)).hom.lTensor p.ResidueField)) (i : ℕ) :
    ∃ (t : R) (_ : t ∉ p) (k₀ : C.X i →ₗ[R] C.X (i - 1)) (k₁ : C.X (i + 1) →ₗ[R] C.X i),
      ∀ x, (C.d (i - 1) i).hom (k₀ x) + k₁ ((C.d i (i + 1)).hom x) = t • x := by
  induction hk : n + 1 - i generalizing i with
  | zero =>
    have := ModuleCat.subsingleton_of_isZero (hn i (by omega))
    exact ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, 0, 0, fun x => Subsingleton.elim _ _⟩
  | succ k ih =>
    obtain ⟨s, hs, h₁, h₂, hh⟩ := ih (i + 1) (by omega)
    have := (hF i).1
    have := (hF i).2
    exact exists_homotopy_step p _ _ _ (d_d_apply C _ _ _) (d_d_apply C _ _ _) (h i) s hs h₁ h₂ hh
end GlobalTheory.DualCokernel
