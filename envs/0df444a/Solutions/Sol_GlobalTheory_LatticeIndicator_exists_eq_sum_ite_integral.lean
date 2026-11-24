-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.exists_eq_sum_ite_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:36.022961+00:00
-- url     : https://prove2.me/submissions/d80237a4-854a-42d7-ade5-371711267537

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_eq_sum_ite_le
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_matrix_of_smul_mem
import Theorems.Thm_GlobalTheory_LatticeIndicator_finite_quotient_smul_top
import Theorems.Thm_GlobalTheory_LatticeIndicator_eq_of_span_col_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
open Classical
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O m n R : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [CommRing R] {c : O} (hc : c ≠ 0) (ψ : Matrix m n O → R)
    (hinv : ∀ (z : Matrix m n O) (k : GL n O), ψ (z * (k : Matrix n n O)) = ψ z)
    (hper : ∀ z y : Matrix m n O, ψ (z + c • y) = ψ z) :
    ∃ (r : ℕ) (h : Fin r → Matrix m m O) (a : Fin r → R), (∀ l, (h l).det ≠ 0) ∧
      ∀ z, ψ z = ∑ l, a l * (if ∃ y : Matrix m n O, z = h l * y then 1 else 0) := by
  set A : Submodule O (m → O) := Ideal.span {c} • ⊤ with hA
  haveI : Finite ((m → O) ⧸ A) := finite_quotient_smul_top hc
  haveI : Finite (Submodule O ((m → O) ⧸ A)) :=
    Finite.of_injective _ (SetLike.coe_injective (A := Submodule O ((m → O) ⧸ A)))
  letI := Fintype.ofFinite (Submodule O ((m → O) ⧸ A))
  let Λ : Matrix m n O → Submodule O ((m → O) ⧸ A) := fun z =>
    Submodule.span O (Set.range fun j => A.mkQ (z.col j))
  have hfac : Function.FactorsThrough ψ Λ := fun z z' h => eq_of_span_col_eq c ψ hinv hper z z' h
  obtain ⟨a, ha⟩ := exists_eq_sum_ite_le (Function.extend Λ ψ 0)
  have hL : ∀ (q : Submodule O ((m → O) ⧸ A)) (v : m → O), c • v ∈ q.comap A.mkQ := by
    intro q v
    have : A.mkQ (c • v) = 0 := (Submodule.Quotient.mk_eq_zero A).2
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) trivial)
    rw [Submodule.mem_comap, this]
    exact q.zero_mem
  choose h hdet hh using fun q => exists_matrix_of_smul_mem hc _ (hL q)
  have hiff : ∀ q z, Λ z ≤ q ↔ ∃ y : Matrix m n O, z = h q * y := by
    intro q z
    rw [Submodule.span_le, Set.range_subset_iff]
    constructor
    · intro hz
      choose u hu using fun j => (hh q _).1 (hz j)
      refine ⟨Matrix.of fun i j => u j i, ?_⟩
      ext i j
      exact congrFun (hu j) i
    · rintro ⟨y, rfl⟩ j
      exact (hh q _).2 ⟨y.col j, rfl⟩
  let e := (Fintype.equivFin (Submodule O ((m → O) ⧸ A))).symm
  refine ⟨_, fun l => h (e l), fun l => a (e l), fun l => hdet _, fun z => ?_⟩
  rw [← hfac.extend_apply 0 z, ha, ← e.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hiff]
end GlobalTheory.LatticeIndicator
