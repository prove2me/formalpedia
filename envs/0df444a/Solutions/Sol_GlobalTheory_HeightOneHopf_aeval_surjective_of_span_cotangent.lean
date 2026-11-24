-- Prove2me | solution 1 for GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:39.856281+00:00
-- url     : https://prove2.me/submissions/a43bb072-13c6-4a97-9860-9cd3507e5df3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfSpanCotangent
import Theorems.Thm_GlobalTheory_NilpotentKernelSurjective_aeval_surjective_of_isNilpotent_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.HeightOneHopf
namespace GlobalTheory.HeightOneHopf
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (hnil : IsNilpotent (RingHom.ker ε)) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin d → R, y - ∑ i, l i • x i ∈ RingHom.ker ε ^ 2) :
    Function.Surjective (MvPolynomial.aeval (R := R) x) := by
  first
  | exact @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
  | exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
  | (apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker ..)
end GlobalTheory.HeightOneHopf
