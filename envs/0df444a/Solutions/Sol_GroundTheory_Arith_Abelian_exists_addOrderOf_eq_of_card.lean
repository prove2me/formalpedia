-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.exists_addOrderOf_eq_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:41.150652+00:00
-- url     : https://prove2.me/submissions/7e3d3944-cff0-4706-8ef6-f3505e9cf398

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {A : Type*} [AddCommGroup A]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    ∃ P : A, addOrderOf P = n := by
  have hex : AddMonoid.ExponentExists A := ⟨n, hn, hA⟩
  obtain ⟨P, hP⟩ := AddMonoid.exists_addOrderOf_eq_exponent hex
  refine ⟨P, hP.trans ?_⟩
  have he : AddMonoid.exponent A ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hA
  have hepos : 0 < AddMonoid.exponent A := Nat.pos_of_dvd_of_pos he hn
  have h1 : Nat.card {a : A // AddMonoid.exponent A • a = 0} = Nat.card A :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun a => AddMonoid.exponent_nsmul_eq_zero a)
  have h2 := hker _ he
  rw [h1, hcard] at h2
  have h3 : n ≤ AddMonoid.exponent A := by
    by_contra h
    push Not at h
    have := Nat.pow_lt_pow_left h (two_ne_zero)
    omega
  exact le_antisymm (Nat.le_of_dvd hn he) h3
end GroundTheory.Arith.Abelian
