-- Prove2me | solution 1 for GlobalTheory.CubeLift.lin_del
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:21.38253+00:00
-- url     : https://prove2.me/submissions/5eaa8a92-8448-47bf-a252-ac2931687aa5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_um_mem
import Theorems.Thm_GlobalTheory_CubeLift_lin_mul
import Theorems.Thm_GlobalTheory_CubeLift_lin_div
import Theorems.Thm_GlobalTheory_CubeLift_lin_um

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution {I : Ideal A} {g : (A[X])ˣ} (hg : g ∈ cong I) (a b c : X →+ Y) :
    lin I (del g a b c) = mv (a + b + c) (lin I g) + mv a (lin I g) + mv b (lin I g) + mv c (lin I g) -
      mv (a + b) (lin I g) - mv (a + c) (lin I g) - mv (b + c) (lin I g) := by
  have m : ∀ f : X →+ Y, um f g ∈ cong I := fun f => um_mem f hg
  have m₄ := mul_mem (mul_mem (mul_mem (m (a + b + c)) (m a)) (m b)) (m c)
  rw [del, lin_div (div_mem (div_mem m₄ (m _)) (m _)) (m _), lin_div (div_mem m₄ (m _)) (m _), lin_div m₄ (m _),
    lin_mul (mul_mem (mul_mem (m _) (m _)) (m _)) (m _), lin_mul (mul_mem (m _) (m _)) (m _), lin_mul (m _) (m _)]
  simp only [lin_um]
end GlobalTheory.CubeLift
