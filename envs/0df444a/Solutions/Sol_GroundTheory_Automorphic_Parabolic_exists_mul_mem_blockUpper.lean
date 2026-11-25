-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_mul_mem_blockUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:43.38183+00:00
-- url     : https://prove2.me/submissions/77c3501e-9795-46f5-994e-8db1b47f3095

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimKey_lt_of_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimCol_mul_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_mem_blockUpper_dual
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (K : Subgroup (GL (Fin n) F))
    (hdiag : ∀ h ∈ K, ∀ a, (h : GL (Fin n) F) a a ≠ 0)
    (helim : ∀ h ∈ K, ∀ a, elimGL β ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a ∈ K)
    {g : GL (Fin n) F} (hg : g ∈ K) :
    ∃ q ∈ K ⊓ blockUpper F n (OrderDual.toDual ∘ β), q * g ∈ blockUpper F n β := by
  classical
  have key : ∀ s : Finset (Fin n), ∃ q ∈ K ⊓ blockUpper F n (OrderDual.toDual ∘ β),
      ∀ j ∈ s, ∀ i, elimKey β j < elimKey β i → (q * g : GL (Fin n) F) i j = 0 := by
    intro s
    induction s using Finset.induction_on_max_value (elimKey β) with
    | empty => exact ⟨1, one_mem _, fun j hj => absurd hj (Finset.notMem_empty j)⟩
    | insert a s ha hmax ih =>
      obtain ⟨q, hq, hz⟩ := ih
      set h : GL (Fin n) F := q * g with hh
      have hK : h ∈ K := K.mul_mem (Subgroup.mem_inf.1 hq).1 hg
      refine ⟨elimGL β (h : Matrix (Fin n) (Fin n) F) a * q,
        Subgroup.mem_inf.2 ⟨K.mul_mem (helim h hK a) (Subgroup.mem_inf.1 hq).1,
          Subgroup.mul_mem _ (elimGL_mem_blockUpper_dual _ a) (Subgroup.mem_inf.1 hq).2⟩, ?_⟩
      intro j hj i hji
      have hentry : ((elimGL β (h : Matrix (Fin n) (Fin n) F) a * q * g : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j =
          (h : Matrix (Fin n) (Fin n) F) i j -
            (elimCol β (h : Matrix (Fin n) (Fin n) F) a * (h : Matrix (Fin n) (Fin n) F)) i j := by
        rw [mul_assoc, Units.val_mul, ← hh]
        show ((1 - elimCol β (h : Matrix (Fin n) (Fin n) F) a) *
          (h : Matrix (Fin n) (Fin n) F)) i j = _
        rw [sub_mul, one_mul, Matrix.sub_apply]
      show ((elimGL β (h : Matrix (Fin n) (Fin n) F) a * q * g : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j = 0
      rw [hentry, elimCol_mul_apply]
      rcases Finset.mem_insert.1 hj with rfl | hjs
      · rw [if_pos hji, div_mul_cancel₀ _ (hdiag h hK j), sub_self]
      · have hja : elimKey β j < elimKey β a :=
          elimKey_lt_of_le (hmax j hjs) (fun e => ha (e ▸ hjs))
        have h1 : (h : GL (Fin n) F) i j = 0 := hz j hjs i hji
        have h2 : (h : GL (Fin n) F) a j = 0 := hz j hjs a hja
        change (h : Matrix (Fin n) (Fin n) F) i j - _ = 0 at *
        split_ifs
        · rw [show (h : Matrix (Fin n) (Fin n) F) a j = 0 from h2, mul_zero, sub_zero]
          exact h1
        · rw [sub_zero]
          exact h1
  obtain ⟨q, hq, hz⟩ := key Finset.univ
  refine ⟨q, hq, ?_⟩
  rw [mem_blockUpper]
  intro i j hji
  refine hz j (Finset.mem_univ j) i ?_
  rw [elimKey, elimKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inl hji
end GroundTheory.Automorphic.Parabolic
