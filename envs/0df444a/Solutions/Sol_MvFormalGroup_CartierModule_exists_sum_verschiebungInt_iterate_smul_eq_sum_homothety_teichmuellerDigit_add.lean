-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4d5e4e66-91c1-5e79-9b58-29c8e2233a30

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

namespace P2MW.S_MvFormalGroup_CartierModule_exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add

set_option autoImplicit false

universe u

open MvPowerSeries

namespace EngineAux

section W1

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

open MvFormalGroup MvFormalGroup.WittLaw in

theorem mulFam_verschiebung_eq (w : WittVector p R) (n : ℕ) :
    mulFam p (WittVector.verschiebung w) n =
      subst (fun k => subst (frobPolyFam p R) (mulFam p w k)) (verFam R n) := by
  have hcV : cVec p (τ := ℕ) (WittVector.verschiebung w) = WittVector.verschiebung (cVec p w) :=
    WittVector.map_verschiebung _ w
  have hL : mulFam p (WittVector.verschiebung w) n =
      (((WittVector.verschiebung (cVec p w * WittVector.frobenius (xTaut p R))).coeff n :
        MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
    rw [mulFam_apply, WittVector.verschiebung_mul_frobenius, ← hcV]
    rfl
  have hR : ∀ k, subst (frobPolyFam p R) (mulFam p w k) =
      (((cVec p w * WittVector.frobenius (xTaut p R)).coeff k : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
    intro k
    have hf : frobPolyFam p R = fun m => (frobPoly p R m : MvPowerSeries ℕ R) := rfl
    rw [hf, mulFam_apply, ← WittLaw.coe_aeval, aeval_mulPoly, mk_frobPoly]
  have hS : HasSubst (fun k => subst (frobPolyFam p R) (mulFam p w k)) := by
    have h := (hasSubst_mulFam (p := p) w).comp (hasSubst_frobPolyFam (p := p) (R := R))
    simpa only [coe_substAlgHom] using h
  rw [hL]
  cases n with
  | zero =>
    rw [WittVector.verschiebung_coeff_zero, verFam_zero, MvPolynomial.coe_zero]
    rw [← coe_substAlgHom hS, map_zero]
  | succ k =>
    rw [WittVector.verschiebung_coeff_succ, verFam_succ, subst_X hS, hR]

open MvFormalGroup MvFormalGroup.CartierModule in

theorem verschiebung_smul_eq {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (w : WittVector p R) (f : CartierModule p Φ) :
    WittVector.verschiebung w • f = verschiebungInt (w • frobenius f) := by
  apply CartierModule.ext
  funext j
  show subst (WittLaw.mulFam p (WittVector.verschiebung w)) (f.toPowerSeries j) =
    subst (WittLaw.frobPolyFam p R) (subst (WittLaw.mulFam p w)
      (subst (WittLaw.verFam R) (f.toPowerSeries j)))
  have hS : HasSubst (fun k => subst (WittLaw.frobPolyFam p R) (WittLaw.mulFam p w k)) := by
    have h := (WittLaw.hasSubst_mulFam (p := p) w).comp (WittLaw.hasSubst_frobPolyFam (p := p) (R := R))
    simpa only [coe_substAlgHom] using h
  rw [subst_comp_subst_apply (WittLaw.hasSubst_mulFam w) WittLaw.hasSubst_frobPolyFam,
    subst_comp_subst_apply WittLaw.hasSubst_verFam hS]
  congr 1
  funext n
  exact mulFam_verschiebung_eq w n

end W1

section W2

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

theorem eq_teichmuller_add_verschiebung_shift (w : WittVector p R) :
    w = WittVector.teichmuller p (w.coeff 0) + WittVector.verschiebung (w.shift 1) := by
  have h := WittVector.init_add_tail w 1
  have hi : WittVector.init 1 w = WittVector.teichmuller p (w.coeff 0) := by
    ext n
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p (w.coeff 0) (n + 1) (Nat.succ_pos n)]
  have ht : WittVector.tail 1 w = WittVector.verschiebung (w.shift 1) := by
    ext n
    simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.verschiebung_coeff_zero]
    | succ n => simp [WittVector.verschiebung_coeff_succ, WittVector.shift_coeff, Nat.add_comm]
  rw [hi, ht] at h
  exact h.symm

open MvFormalGroup MvFormalGroup.CartierModule in

theorem smul_eq_homothety_add {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (w : WittVector p R) (f : CartierModule p Φ) :
    w • f = homothety (w.coeff 0) f + verschiebungInt (w.shift 1 • frobenius f) := by
  conv_lhs => rw [eq_teichmuller_add_verschiebung_shift w]
  rw [add_smul, teichmuller_smul, verschiebung_smul_eq]

end W2

section Iter

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

open MvFormalGroup MvFormalGroup.CartierModule

theorem iterV_add (m : ℕ) (x y : CartierModule p Φ) :
    (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (x + y) =
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] x + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] y := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_add]

theorem iterV_zero (m : ℕ) : (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (0 : CartierModule p Φ) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]

theorem iterV_sum {ι : Type*} (s : Finset ι) (g : ι → CartierModule p Φ) (m : ℕ) :
    (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ i ∈ s, g i) =
      ∑ i ∈ s, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, iterV_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iterV_add, ih]

theorem smul_iterV (w : WittVector p R) (y : CartierModule p Φ) (m : ℕ) :
    w • (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] y =
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] ((⇑(WittVector.frobenius (p := p) (R := R)))^[m] w • y) := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', smul_verschiebungInt, ih, ← Function.iterate_succ_apply,
      Function.iterate_succ_apply' (⇑(verschiebungInt (p := p) (Φ := Φ)))]

end Iter

end EngineAux

open EngineAux MvFormalGroup MvFormalGroup.CartierModule in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] {d : ℕ}
    (Φ : MvFormalGroup d B) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (c : ℕ → Fin d → Fin d → B)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (N : ℕ) (S : ℕ → Fin d → WittVector p B) :
    ∃ r : MvFormalGroup.CartierModule p Φ,
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, S m l • f l)) =
      (∑ n ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety
            ((((fun T : ℕ → Fin d → WittVector p B => fun (m : ℕ) (l' : Fin d) =>
                  T (m + 1) l' + ∑ l : Fin d,
                    (⇑(WittVector.frobenius (p := p) (R := B)))^[m] ((T 0 l).shift 1) *
                      WittVector.teichmuller p (c m l l'))^[n] S) 0 l).coeff 0) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] r := by
  obtain ⟨step, hstep⟩ : ∃ step : (ℕ → Fin d → WittVector p B) → (ℕ → Fin d → WittVector p B),
      step = (fun T : ℕ → Fin d → WittVector p B => fun (m : ℕ) (l' : Fin d) =>
        T (m + 1) l' + ∑ l : Fin d,
          (⇑(WittVector.frobenius (p := p) (R := B)))^[m] ((T 0 l).shift 1) *
            WittVector.teichmuller p (c m l l')) := ⟨_, rfl⟩
  rw [← hstep]
  have hstepv : ∀ (T : ℕ → Fin d → WittVector p B) (m : ℕ) (l' : Fin d), step T m l' =
      T (m + 1) l' + ∑ l : Fin d,
        (⇑(WittVector.frobenius (p := p) (R := B)))^[m] ((T 0 l).shift 1) *
          WittVector.teichmuller p (c m l l') := fun T m l' => by rw [hstep]
  induction N generalizing S with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨r', hr'⟩ := ih (step S)
    have hV1 : ∀ (x : CartierModule p Φ) (m : ℕ),
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m + 1] x =
          verschiebungInt ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] x) :=
      fun x m => Function.iterate_succ_apply' _ m x

    obtain ⟨P, hP⟩ : ∃ P : Fin d → CartierModule p Φ, ∀ l, (∑ m ∈ Finset.range N,
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l' : Fin d, ((⇑(WittVector.frobenius (p := p) (R := B)))^[m] ((S 0 l).shift 1) *
            WittVector.teichmuller p (c m l l')) • f l')) = P l := ⟨_, fun l => rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Fin d → CartierModule p Φ, ∀ l,
        (⇑(WittVector.frobenius (p := p) (R := B)))^[N] ((S 0 l).shift 1) • h N l = Q l :=
      ⟨_, fun l => rfl⟩

    have h0 : ∀ l : Fin d, S 0 l • f l = homothety ((S 0 l).coeff 0) (f l) +
        verschiebungInt (P l + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (Q l)) := by
      intro l
      have hX : (∑ m ∈ Finset.range N, (S 0 l).shift 1 •
          (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l' : Fin d, homothety (c m l l') (f l'))) =
          ∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
            (∑ l' : Fin d, ((⇑(WittVector.frobenius (p := p) (R := B)))^[m] ((S 0 l).shift 1) *
              WittVector.teichmuller p (c m l l')) • f l') := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_iterV, Finset.smul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun l' _ => by rw [← teichmuller_smul, smul_smul])
      rw [smul_eq_homothety_add, hexp N l, smul_add, Finset.smul_sum, smul_iterV, hQ, hX, hP]

    have hstepS : (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
        (∑ l : Fin d, step S m l • f l)) =
        (∑ l : Fin d, P l) + ∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, S (m + 1) l • f l) := by
      simp only [← hP]
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← iterV_sum, ← iterV_add]
      refine congrArg _ ?_
      simp only [hstepv, add_smul, Finset.sum_smul, Finset.sum_add_distrib]
      rw [add_comm, Finset.sum_comm]
    have hdig : (∑ n ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n]
        (∑ l : Fin d, homothety (((step^[n] (step S)) 0 l).coeff 0) (f l))) =
        ∑ n ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n]
          (∑ l : Fin d, homothety (((step^[n + 1] S) 0 l).coeff 0) (f l)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Function.iterate_succ_apply]
    rw [hstepS, hdig] at hr'

    have key := congrArg (⇑(verschiebungInt (p := p) (Φ := Φ))) hr'
    rw [map_add, map_add, map_sum, map_sum, map_sum] at key
    refine ⟨r' + ∑ l : Fin d, Q l, ?_⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun n =>
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n]
        (∑ l : Fin d, homothety (((step^[n] S) 0 l).coeff 0) (f l)))]
    simp only [Function.iterate_zero, id_eq]
    rw [Finset.sum_congr rfl (fun l _ => h0 l), Finset.sum_add_distrib]
    have hB : (∑ l : Fin d, verschiebungInt (P l + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (Q l))) =
        (∑ l : Fin d, verschiebungInt (P l)) +
          (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N + 1] (∑ l : Fin d, Q l) := by
      rw [hV1, iterV_sum, map_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by rw [map_add]
    rw [hB, iterV_add]
    simp only [hV1] at key ⊢
    have e := congrArg (fun z => z + ((∑ l : Fin d, homothety ((S 0 l).coeff 0) (f l)) +
      verschiebungInt ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (∑ l : Fin d, Q l)))) key
    refine Eq.trans ?_ (e.trans ?_) <;> abel

end S_MvFormalGroup_CartierModule_exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add (solution)
