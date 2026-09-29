-- Prove2me | solution 1 for MvFormalGroup.CartierModule.frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/05c6e3aa-44fb-52e8-a53c-7feea236638a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule

namespace TwistAux

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {d : ℕ} {Φ : MvFormalGroup d B} [Φ.IsComm]

theorem smul_verschiebungInt_iterate (w : WittVector p B) (y : CartierModule p Φ) (m : ℕ) :
    w • (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] y =
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] ((⇑(WittVector.frobenius (p := p) (R := B)))^[m] w • y) := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', smul_verschiebungInt, ih, ← Function.iterate_succ_apply,
      Function.iterate_succ_apply' (⇑(verschiebungInt (p := p) (Φ := Φ)))]

theorem frobenius_iterate_eq (w : Fin 2 → WittVector p B)
    (hw : ∀ i : Fin 2, WittVector.frobenius (w i) = w (i + 1)) (k : ℕ) (i : Fin 2) :
    (⇑(WittVector.frobenius (p := p) (R := B)))^[k] (w i) = w ⟨((i : ℕ) + k) % 2, Nat.mod_lt _ two_pos⟩ := by
  induction k generalizing i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.add_zero]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply, hw, ih]
    congr 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one]
    omega

end TwistAux

open TwistAux in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (c : ℕ → Fin 2 → Fin 2 → B)
    (hc : ∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → c m i l = 0)
    (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (w : Fin 2 → WittVector p B)
    (hw : ∀ i : Fin 2, WittVector.frobenius (w i) = w (i + 1)) :
    ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (w i • f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (w l • f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N]
          ((⇑(WittVector.frobenius (p := p) (R := B)))^[N + 1] (w i) • h N i) := by
  intro N i
  rw [frobenius_smul, hexp N i, smul_add, Finset.smul_sum, hw,
    smul_verschiebungInt_iterate (w (i + 1)) (h N i) N]
  have hlast : (⇑(WittVector.frobenius (p := p) (R := B)))^[N] (w (i + 1)) =
      (⇑(WittVector.frobenius (p := p) (R := B)))^[N + 1] (w i) := by
    rw [Function.iterate_succ_apply, hw]
  have hsum : (∑ m ∈ Finset.range N, w (i + 1) •
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l : Fin 2, homothety (c m i l) (f l))) =
      ∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
        (∑ l : Fin 2, homothety (c m i l) (w l • f l)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_verschiebungInt_iterate (w (i + 1)) _ m, Finset.smul_sum]
    refine congrArg ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]) ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← homothety_smul_witt]
    by_cases hcl : c m i l = 0
    · rw [hcl, homothety_zero_left, homothety_zero_left]
    · have hl : (l : ℕ) = (m + i + 1) % 2 := by
        by_contra hne; exact hcl (hc m i l hne)
      have hidx : (⇑(WittVector.frobenius (p := p) (R := B)))^[m] (w (i + 1)) = w l := by
        rw [← hw, ← Function.iterate_succ_apply, frobenius_iterate_eq w hw (m + 1) i]
        congr 1
        apply Fin.ext
        simp only
        omega
      rw [hidx]
  rw [hsum, hlast]

end S_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq (solution)
