-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflGen.exists_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:01.015039+00:00
-- url     : https://prove2.me/submissions/3bf1001b-f563-48d0-b7b8-11ae85fea3a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections
import Theorems.Thm_GlobalTheory_UnRep_ReflGen_isUnE_mul
import Theorems.Thm_GlobalTheory_UnRep_ReflGen_isUnE_prod
import Theorems.Thm_GlobalTheory_UnRep_ReflGen_prod_fix
import Theorems.Thm_GlobalTheory_UnRep_ReflGen_herm_span
import Theorems.Thm_GlobalTheory_T_exists_quasiReflection_prod_mulVec_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UnRep.ReflGen
theorem _root_.solution (hG : IsHermForm c G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hermE c G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      ∀ i : Fin n, i.val < k → ((l.map fun p => refl c G p.1 p.2).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isUnE_mul (isUnE_prod hG l hl) hγ
      set δ := (l.map fun p => refl c G p.1 p.2).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ := GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq F E c n G hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix hG _ m fun p hp => ⟨(hm p hp).1, herm_span (h2 _ _ hne) ?_ (hm p hp).2.2⟩
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩
end GlobalTheory.UnRep.ReflGen
