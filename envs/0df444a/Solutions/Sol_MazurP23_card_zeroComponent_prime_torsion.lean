-- Prove2me | solution 1 for MazurP23.card_zeroComponent_prime_torsion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:10:23.552181+00:00
-- url     : https://prove2.me/submissions/8017dbb8-c03e-486b-b0eb-967430812195

import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_ne_residueChar
import Theorems.Thm_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23

private theorem tw_submodule_eq_top_of_card_eq {R : Type*} [Semiring R] {V : Type*}
    [AddCommGroup V] [Module R V] [Finite V] {N : Submodule R V}
    (h : Nat.card ↥N = Nat.card V) : N = ⊤ := by
  rw [_root_.eq_top_iff]; intro x _
  have hbij := N.subtype_injective.bijective_of_nat_card_le (by rw [h])
  obtain ⟨⟨y, hy⟩, hy'⟩ := hbij.2 x
  exact hy' ▸ hy

private theorem tw_card_line {p : ℕ} (hp : p.Prime) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (hcard : Nat.card V = p ^ 2)
    {L : Submodule (ZMod p) V} (hLbot : L ≠ ⊥) (hLtop : L ≠ ⊤) : Nat.card ↥L = p := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 hp.pos.ne')
  have hdvd : Nat.card ↥L ∣ p ^ 2 := by
    rw [← hcard, L.card_eq_card_quotient_mul_card]; exact dvd_mul_right _ _
  obtain ⟨k, hk, hkN⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · exact absurd
      (have := (Nat.card_eq_one_iff_unique.mp (by simpa using hkN)).1
       Submodule.eq_bot_of_subsingleton) hLbot
  · simpa using hkN
  · exact absurd (tw_submodule_eq_top_of_card_eq (hkN.trans hcard.symm)) hLtop

private theorem tw_mem_tor {M : Type*} [AddCommGroup M] (n : ℕ) (x : M) :
    x ∈ Submodule.torsionBy ℤ M ((n : ℕ) : ℤ) ↔ n • x = 0 := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

theorem _root_.solution (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (hcard1 : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) = p ^ 2) :
    Nat.card {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • x = 0 ∧ W.InZeroComponentAt A x} = p := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨M, hMiff, -, -⟩ :=
    WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
      W hq hΔ hqΔ hqc₄ A hA (ℓ := p) hp
  have e : {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • x = 0 ∧ W.InZeroComponentAt A x} ≃ ↥M :=
    { toFun := fun s => ⟨⟨s.1, (tw_mem_tor p s.1).mpr s.2.1⟩, (hMiff _).mpr s.2.2⟩
      invFun := fun m => ⟨(m.1 : _), ⟨(tw_mem_tor p _).mp m.1.2, (hMiff m.1).mp m.2⟩⟩
      left_inv := fun s => rfl
      right_inv := fun m => rfl }
  rw [Nat.card_congr e]
  have hMbot : M ≠ ⊥ := by
    obtain ⟨P0, hP0ne, hP0in⟩ :=
      WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
        W hq hΔ hqΔ hqc₄ A hA (ℓ := p) hp hpq
    intro h
    refine hP0ne ?_
    have hmem := (hMiff P0).mpr hP0in
    rw [h] at hmem
    simpa using hmem
  have hMtop : M ≠ ⊤ := by
    obtain ⟨P1, hP1out⟩ :=
      WeierstrassCurve.exists_torsion_not_inZeroComponentAt_of_ne_residueChar
        W hq hΔ hqΔ hqc₄ A hA (ℓ := p) hp hpq
    exact fun h => hP1out ((hMiff P1).mp (h ▸ Submodule.mem_top))
  exact tw_card_line hp hcard1 hMbot hMtop

end MazurP23
