-- Prove2me | solution 1 for GlobalTheory.mk_lt_mk_addMonoidHom_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:08.409852+00:00
-- url     : https://prove2.me/submissions/3c986b0b-419c-4ad6-aa8b-53ce615ad011

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod
import Theorems.Thm_GlobalTheory_mk_addMonoidHom_le_of_surjective_of_injective
import Theorems.Thm_GlobalTheory_exists_injective_zmod_addMonoidHom
import Theorems.Thm_GlobalTheory_mk_lt_mk_addMonoidHom_zmod_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function Cardinal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) : ∀ (A : Type) [AddCommGroup A],
    (∀ x : A, n • x = 0) → n ≠ 0 → Infinite A → #A < #(A →+ ZMod n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ hA hn hinf
  rcases eq_or_ne n 1 with rfl | h1
  · exfalso
    haveI : Subsingleton A := ⟨fun x y => by
      have hx : x = 0 := by simpa using hA x
      have hy : y = 0 := by simpa using hA y
      rw [hx, hy]⟩
    exact not_finite A
  obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
    ⟨n.minFac, Nat.minFac_prime h1, n / n.minFac, (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm⟩
  haveI := Fact.mk hp
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  let f : A →+ A := AddMonoidHom.mk' (fun x => p • x) (fun x y => nsmul_add x y p)
  let P : AddSubgroup A := f.range
  have hmul : #A = #(A ⧸ P) * #P := by
    rw [(AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := P)).cardinal_eq, mk_prod,
      lift_id, lift_id]
  have hPle : #P ≤ #A := mk_le_of_injective Subtype.val_injective
  have hQle : #(A ⧸ P) ≤ #A := mk_le_of_surjective (QuotientAddGroup.mk_surjective)
  have hAinf : ℵ₀ ≤ #A := aleph0_le_mk A
  rcases hPle.lt_or_eq with hPlt | hPeq
  · rcases hQle.lt_or_eq with hQlt | hQeq
    · exact absurd hmul (ne_of_gt (mul_lt_of_lt hAinf hQlt hPlt))

    · letI : Infinite (A ⧸ P) := Cardinal.infinite_iff.mpr (hQeq ▸ hAinf)
      have hQp : ∀ y : A ⧸ P, p • y = 0 := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        exact ⟨x, rfl⟩
      obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_right p m)
      calc #A = #(A ⧸ P) := hQeq.symm
        _ < #(A ⧸ P →+ ZMod p) := mk_lt_mk_addMonoidHom_zmod_prime p (A ⧸ P) hQp
        _ ≤ #(A →+ ZMod (p * m)) :=
          mk_addMonoidHom_le_of_surjective_of_injective (QuotientAddGroup.mk' P)
            (QuotientAddGroup.mk_surjective) ι hι

  · letI : Infinite P := Cardinal.infinite_iff.mpr (hPeq ▸ hAinf)
    have hPm : ∀ y : P, m • y = 0 := by
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      show m • (p • x) = 0
      rw [smul_smul, mul_comm, hA x]
    have hlt : m < p * m := by
      have := hp.two_le
      have := Nat.pos_of_ne_zero hm
      nlinarith
    have hP := ih m hlt P hPm hm inferInstance
    obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_left m p)
    calc #A = #P := hPeq.symm
      _ < #(P →+ ZMod m) := hP
      _ ≤ #(A →+ ZMod (p * m)) :=
        mk_addMonoidHom_le_of_surjective_of_injective f.rangeRestrict
          f.rangeRestrict_surjective ι hι
end GlobalTheory
