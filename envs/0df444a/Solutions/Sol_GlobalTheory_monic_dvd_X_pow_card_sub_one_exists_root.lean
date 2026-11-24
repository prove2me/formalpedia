-- Prove2me | solution 1 for GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:47.158257+00:00
-- url     : https://prove2.me/submissions/fa639fd0-e55e-457d-9666-843328d29251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]),
      f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 →
        ∃ y : S, f.eval y = 0 := by
  intro S _ _ _ f hmon hdeg hdvd
  classical
  letI : Fintype (ResidueField S) := Fintype.ofFinite _
  have hQ : Nat.card (ResidueField S) = Fintype.card (ResidueField S) := Nat.card_eq_fintype_card
  set Q := Fintype.card (ResidueField S) with hQdef
  set g : (ResidueField S)[X] := f.map (residue S) with hgdef
  have hgm : g.Monic := hmon.map _
  have hgdeg : g.natDegree ≠ 0 := by rw [hgdef, hmon.natDegree_map]; exact hdeg
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hdvd' : g ∣ X ^ Q - X := by
    have h1 : g ∣ X ^ (Q - 1) - 1 := by
      have := Polynomial.map_dvd (residue S) hdvd
      simpa [hQ, g] using this
    have : (X ^ Q - X : (ResidueField S)[X]) = X * (X ^ (Q - 1) - 1) := by
      conv_lhs => rw [show Q = (Q - 1) + 1 by omega]
      ring
    rw [this]; exact dvd_mul_of_dvd_right h1 _
  have hne : (X ^ Q - X : (ResidueField S)[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero (ResidueField S) hQ1
  have hsplit : Splits (X ^ Q - X : (ResidueField S)[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq (ResidueField S) hQ1]
    simp [Q]
  have hgs : Splits g := hsplit.of_dvd hne hdvd'
  obtain ⟨abar, habar⟩ := hgs.exists_eval_eq_zero
    (by rw [degree_eq_natDegree hgm.ne_zero]; exact_mod_cast hgdeg)
  have hchar : ringChar (ResidueField S) ∣ Q := by
    apply (ringChar.spec (ResidueField S) Q).mp
    exact FiniteField.cast_card_eq_zero (ResidueField S)
  have hsep : (X ^ Q - X : (ResidueField S)[X]).Separable :=
    galois_poly_separable (ringChar (ResidueField S)) Q hchar
  have hgsep := hsep.of_dvd hdvd'
  have hder : eval abar (derivative g) ≠ 0 := by
    have := hgsep.aeval_derivative_ne_zero (S := ResidueField S) (x := abar)
      (by simpa [aeval_def] using habar)
    simpa [aeval_def] using this
  obtain ⟨a, rfl⟩ := residue_surjective abar
  have key : ∀ p : S[X], residue S (p.eval a) = (p.map (residue S)).eval (residue S a) := by
    intro p; rw [eval_map, eval₂_hom]
  obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian f hmon a
    (by rw [← residue_eq_zero_iff, key]; exact habar)
    (by
      rw [← residue_ne_zero_iff_isUnit, key, ← derivative_map]
      exact hder)
  exact ⟨y, hy⟩
end GlobalTheory
