-- Prove2me | solution 1 for GlobalTheory.Sandwich.HodgeTateBound.range_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:22.908559+00:00
-- url     : https://prove2.me/submissions/d19e8683-35f4-4b5e-86c8-2fca8a1dc59c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.HodgeTateBound
variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}
namespace GlobalTheory.Sandwich.HodgeTateBound
theorem _root_.solution (θ : A →+* O) {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : θ μ = 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) :
    LinearMap.range (Matrix.toLin' (F.map θ)) ≤ LinearMap.ker (Matrix.toLin' (G.map θ)) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, ← Matrix.toLin'_mul_apply, ← Matrix.map_mul, hGF]
  have : (μ • (1 : Matrix (Fin h) (Fin h) A)).map θ = 0 := by
    ext i j
    simp [hμ]
  rw [this]
  simp
end GlobalTheory.Sandwich.HodgeTateBound
