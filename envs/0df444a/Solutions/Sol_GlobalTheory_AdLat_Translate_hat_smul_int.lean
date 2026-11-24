-- Prove2me | solution 1 for GlobalTheory.AdLat.Translate.hat_smul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:06:46.338038+00:00
-- url     : https://prove2.me/submissions/93367aee-debb-4702-bf36-653cd1791cd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Translate
theorem _root_.solution {S : Set (Fin n → E)} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    (a ⊗ₜ[F] (1 : E) : RA F E) • z ∈ hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * a', fun v => mul_mem (ha v) (ha' v), x, hx, ?_⟩
    ext i; simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end GlobalTheory.AdLat.Translate
