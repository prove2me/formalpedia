-- Prove2me | solution 1 for GlobalTheory.SepIdem.exists_smul_kaehler_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:57:13.148596+00:00
-- url     : https://prove2.me/submissions/bbb58544-f102-4b49-b4c9-2c9b8c7f5375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormallyUnramifiedOfIsReduced
import Theorems.Thm_GlobalTheory_SepIdem_formallyUnramified_of_isReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.SepIdem
namespace GlobalTheory.SepIdem
theorem _root_.solution (O : Type) [CommRing O] [Module.Finite ℤ O] [IsReduced O] :
    ∃ N : ℕ, 0 < N ∧ ∀ ω : Ω[O⁄ℤ], (N : O) • ω = 0 := by
  let A := ℚ ⊗[ℤ] O
  letI : Algebra O A := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid O ℤ⁰) A :=
    IsLocalization.tensorRight ℚ ℤ⁰
  have : IsReduced A := isReduced_localizationPreserves (Algebra.algebraMapSubmonoid O ℤ⁰) A inferInstance
  have : Algebra.FormallyUnramified ℚ A := formallyUnramified_of_isReduced ℚ A
  have : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization ℤ⁰
  have hA : Algebra.FormallyUnramified ℤ A := Algebra.FormallyUnramified.comp ℤ ℚ A
  have : Algebra.FormallyEtale O A :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid O ℤ⁰)
  have hm := KaehlerDifferential.isLocalizedModule_map ℤ O A (Algebra.algebraMapSubmonoid O ℤ⁰)
  have key : ∀ ω : Ω[O⁄ℤ], ∃ n : ℤ, n ≠ 0 ∧ (n : O) • ω = 0 := by
    intro ω
    have h0 : KaehlerDifferential.map ℤ ℤ O A ω = 0 := Subsingleton.elim _ _
    obtain ⟨⟨s, n, hn, rfl⟩, hs⟩ :=
      (IsLocalizedModule.eq_zero_iff (Algebra.algebraMapSubmonoid O ℤ⁰) _).1 h0
    exact ⟨n, nonZeroDivisors.ne_zero hn, by simpa using hs⟩
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := O) (M := Ω[O⁄ℤ])
  choose n hn0 hn using key
  refine ⟨∏ x ∈ S, (n x).natAbs, Finset.prod_pos fun x _ => Int.natAbs_pos.2 (hn0 x), ?_⟩
  intro ω
  have hω : ω ∈ Submodule.span O (S : Set Ω[O⁄ℤ]) := hS ▸ Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => (n x).natAbs) hx
    obtain ⟨j, hj⟩ : n x ∣ ((n x).natAbs : ℤ) := Int.dvd_natAbs.2 dvd_rfl
    have : (((n x).natAbs : ℕ) : O) = (j : O) * (n x : O) := by
      rw [← Int.cast_natCast, hj]; push_cast; ring
    rw [hk, Nat.cast_mul, this, mul_comm, ← mul_assoc, mul_smul, hn, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]
end GlobalTheory.SepIdem
