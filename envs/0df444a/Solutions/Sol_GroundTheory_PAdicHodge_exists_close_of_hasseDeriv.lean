-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_close_of_hasseDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:12.855951+00:00
-- url     : https://prove2.me/submissions/77cf9684-6341-4ab8-8c34-ed5ddea9978a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_prod_eq
import Theorems.Thm_GroundTheory_PAdicHodge_norm_esymm_le
import Theorems.Thm_GroundTheory_PAdicHodge_exists_pow_card_le_of_prod_le
import Theorems.Thm_GroundTheory_PAdicHodge_exists_gal_apply_eq_of_mem_roots
import Theorems.Thm_GroundTheory_PAdicHodge_hasseDeriv_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (x : PadicAlgCl p) {ρ : ℝ}
    (hρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) {q : ℕ}
    (hq : q < (minpoly K x).natDegree) :
    ∃ b : PadicAlgCl p, (minpoly K b).natDegree ≤ (minpoly K x).natDegree - q ∧
      ‖((Nat.choose (minpoly K x).natDegree q : ℕ) : PadicAlgCl p)‖ *
        ‖x - b‖ ^ ((minpoly K x).natDegree - q) ≤ ρ ^ ((minpoly K x).natDegree - q) := by
  classical
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  set P := minpoly K x with hP
  set d := P.natDegree with hd
  set f := algebraMap K (PadicAlgCl p) with hf
  have hρ0 : 0 ≤ ρ := by simpa using hρ 1
  have hPm : (P.map f).Monic := (minpoly.monic hx).map f
  have hdm : (P.map f).natDegree = d := natDegree_map f
  have hroots : Multiset.card (P.map f).roots = d := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hdm]
  have hsplit : ((P.map f).roots.map fun a => X - C a).prod = P.map f :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm (by rw [hroots, hdm])
  set Q := hasseDeriv q P with hQ
  have hQm : hasseDeriv q (P.map f) = Q.map f := hasseDeriv_map f q P

  have htaylor : taylor x (P.map f) = ((P.map f).roots.map fun a => X + C (x - a)).prod := by
    calc taylor x (P.map f) = taylorAlgHom x (P.map f) := rfl
      _ = _ := by
        conv_lhs => rw [← hsplit]
        rw [map_multiset_prod, Multiset.map_map]
        congr 1
        refine Multiset.map_congr rfl fun a _ => ?_
        rw [Function.comp_apply]
        change taylor x (X - C a) = _
        rw [map_sub, taylor_X, taylor_C, C_sub]
        ring
  have heval : (Q.map f).eval x = ((P.map f).roots.map fun a => x - a).esymm (d - q) := by
    rw [← hQm, ← taylor_coeff, htaylor, Multiset.prod_X_add_C_coeff' _ (fun a => x - a)
      (by rw [hroots]; exact hq.le), hroots]
  have hevalle : ‖(Q.map f).eval x‖ ≤ ρ ^ (d - q) := by
    rw [heval]
    refine norm_esymm_le hρ0 (fun c hc => ?_) _
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hc
    obtain ⟨σ, rfl⟩ := exists_gal_apply_eq_of_mem_roots ha
    rw [norm_sub_rev]
    exact hρ σ

  have hQdeg : (Q.map f).natDegree = d - q := by
    rw [← hQm, natDegree_hasseDeriv, hdm]
  have hQlc : (Q.map f).leadingCoeff = ((Nat.choose d q : ℕ) : PadicAlgCl p) := by
    rw [leadingCoeff, hQdeg, ← hQm, hasseDeriv_coeff, Nat.sub_add_cancel hq.le, ← hdm,
      ← leadingCoeff, hPm.leadingCoeff, mul_one]
  have hlc0 : ((Nat.choose d q : ℕ) : PadicAlgCl p) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.choose_pos hq.le).ne'
  have hQcard : Multiset.card (Q.map f).roots = (Q.map f).natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hQfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hQcard
  have hQeval : (Q.map f).eval x =
      ((Nat.choose d q : ℕ) : PadicAlgCl p) * ((Q.map f).roots.map fun b => x - b).prod := by
    conv_lhs => rw [← hQfac]
    rw [eval_mul, eval_C, hQlc, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  have hne : (Q.map f).roots ≠ 0 := by
    intro h0
    have := hQcard
    rw [h0, hQdeg] at this
    simp at this
    omega
  have hprod : ((Q.map f).roots.map fun b => ‖x - b‖).prod ≤
      ρ ^ (d - q) / ‖((Nat.choose d q : ℕ) : PadicAlgCl p)‖ := by
    rw [le_div_iff₀ (norm_pos_iff.2 hlc0), mul_comm]
    calc ‖((Nat.choose d q : ℕ) : PadicAlgCl p)‖ * ((Q.map f).roots.map fun b => ‖x - b‖).prod
        = ‖(Q.map f).eval x‖ := by
          rw [hQeval, norm_mul, norm_multiset_prod_eq, Multiset.map_map]
          rfl
      _ ≤ ρ ^ (d - q) := hevalle
  obtain ⟨b, hb, hble⟩ := exists_pow_card_le_of_prod_le hne (fun _ _ => norm_nonneg _) hprod
  rw [hQcard, hQdeg, le_div_iff₀ (norm_pos_iff.2 hlc0), mul_comm] at hble
  refine ⟨b, ?_, hble⟩

  have hQ0 : Q ≠ 0 := by
    rintro h0
    rw [h0, Polynomial.map_zero, roots_zero] at hne
    exact hne rfl
  have hbQ : aeval b Q = 0 := by
    rw [mem_roots_map hQ0] at hb
    rwa [aeval_def]
  have := natDegree_le_of_dvd (minpoly.dvd K b hbQ) hQ0
  rw [hQ, natDegree_hasseDeriv] at this
  exact this
end GroundTheory.PAdicHodge
