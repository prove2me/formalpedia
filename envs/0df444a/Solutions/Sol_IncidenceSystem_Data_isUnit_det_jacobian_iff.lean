-- Prove2me | solution 1 for IncidenceSystem.Data.isUnit_det_jacobian_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/90586bbf-a17a-5696-866c-b0eacf14eb3a

import Mathlib
import Definitions.Def_IncidenceSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace IncidenceSystem
p2m_export "IncidenceSystem" "Var Data R xser wser sser subst cc Data.ptCoord wpoly spoly coordAt substAt map_eval_sser map_eval_subst Var.σ.injEq Var.w.injEq Var.σ Var.w Var.u Var.c"
p2m_open "IncidenceSystem"

section dT

variable {R : Type*} [CommRing R]

noncomputable def dT (d : R →+ R) (p : Polynomial R) : Polynomial R :=
  ⟨.ofCoeff (p.toFinsupp.coeff.mapRange d d.map_zero)⟩

@[scoped simp] theorem coeff_dT (d : R →+ R) (p : Polynomial R) (n : ℕ) : (dT d p).coeff n = d (p.coeff n) := by
  rcases p with ⟨f⟩
  simp [dT, Polynomial.coeff]

theorem dT_add (d : R →+ R) (p q : Polynomial R) : dT d (p + q) = dT d p + dT d q := by
  ext n; simp

theorem dT_zero (d : R →+ R) : dT d (0 : Polynomial R) = 0 := by
  ext n; simp

theorem dT_sum (d : R →+ R) {ι : Type*} (s : Finset ι) (f : ι → Polynomial R) :
    dT d (∑ i ∈ s, f i) = ∑ i ∈ s, dT d (f i) := by
  ext n; simp [map_sum]

theorem dT_monomial (d : R →+ R) (n : ℕ) (a : R) : dT d (Polynomial.monomial n a) = Polynomial.monomial n (d a) := by
  ext k; simp [Polynomial.coeff_monomial]; split_ifs <;> simp

theorem dT_C (d : R →+ R) (a : R) : dT d (Polynomial.C a) = Polynomial.C (d a) := by
  rw [← Polynomial.monomial_zero_left, dT_monomial, Polynomial.monomial_zero_left]

variable {A : Type*} [CommRing A] [Algebra A R]

theorem dT_mul (d : Derivation A R R) (p q : Polynomial R) :
    dT (d : R →+ R) (p * q) = dT (d : R →+ R) p * q + p * dT (d : R →+ R) q := by
  ext n
  simp only [coeff_dT, Polynomial.coeff_mul, Polynomial.coeff_add, map_sum, AddMonoidHom.coe_coe,
    Derivation.leibniz, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem dT_one (d : Derivation A R R) : dT (d : R →+ R) (1 : Polynomial R) = 0 := by
  rw [← Polynomial.C_1, dT_C]; simp

theorem dT_X (d : Derivation A R R) : dT (d : R →+ R) (Polynomial.X : Polynomial R) = 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, dT_monomial]; simp

theorem dT_algebraMap (d : Derivation A R R) (a : A) :
    dT (d : R →+ R) (algebraMap A (Polynomial R) a) = 0 := by
  rw [Polynomial.algebraMap_apply, dT_C]; simp

theorem dT_pow (d : Derivation A R R) (p : Polynomial R) (n : ℕ) :
    dT (d : R →+ R) (p ^ n) = n * p ^ (n - 1) * dT (d : R →+ R) p := by
  induction n with
  | zero => simp [dT_one]
  | succ n ih =>
    rw [pow_succ, dT_mul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.cast_succ, add_tsub_cancel_right]
      ring

theorem dT_aeval {σ : Type*} [Fintype σ] [DecidableEq σ] (d : Derivation A R R) (f : σ → Polynomial R)
    (H : MvPolynomial σ A) :
    dT (d : R →+ R) (MvPolynomial.aeval f H) =
      ∑ o : σ, MvPolynomial.aeval f (MvPolynomial.pderiv o H) * dT (d : R →+ R) (f o) := by
  induction H using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, Polynomial.algebraMap_apply, dT_C]
    simp
  | add p q hp hq =>
    simp only [map_add, dT_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p o hp =>
    rw [map_mul, MvPolynomial.aeval_X, dT_mul, hp, Finset.sum_mul]
    simp only [(MvPolynomial.pderiv _).leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul,
      MvPolynomial.aeval_X, add_mul, Finset.sum_add_distrib, Pi.single_apply, apply_ite (MvPolynomial.aeval f),
      map_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [add_comm]
    congr 1 <;> first | exact Finset.sum_congr rfl (fun x _ => by ring) | ring | rfl

end dT

end IncidenceSystem
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

namespace IncidenceSystem
p2m_export "IncidenceSystem" "Var Data R xser wser sser subst cc Data.ptCoord wpoly spoly coordAt substAt map_eval_sser map_eval_subst Var.σ.injEq Var.w.injEq Var.σ Var.w Var.u Var.c"
p2m_open "IncidenceSystem"

variable {g e m' : ℕ} {A : Type*} [CommRing A]

noncomputable abbrev dV (v : Var g e m') : Polynomial (R g e m' A) → Polynomial (R g e m' A) :=
  dT ((MvPolynomial.pderiv v : Derivation A (R g e m' A) (R g e m' A)) : R g e m' A →+ R g e m' A)

theorem dV_xser (v : Var g e m') (i : Fin g) :
    dV v (xser (e := e) (m' := m') (A := A) i) = Polynomial.C (if v = Var.u i then 1 else 0) := by
  rw [dV, xser, dT_add, dT_C, dT_X, add_zero]
  congr 1
  simp [MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

theorem dV_wser (v : Var g e m') (i : Fin g) (j : Fin e) :
    dV v (wser (m' := m') (A := A) i j) =
      ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (if v = Var.w i j r then (1 : R g e m' A) else 0) := by
  rw [dV, wser, dT_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [dT_monomial]
  congr 1
  simp [MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

theorem dV_sser (v : Var g e m') (k : Option (Fin (g * m'))) (i : Fin g) :
    dV v (sser (e := e) (A := A) k i) =
      ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (if v = Var.σ k i r then (1 : R g e m' A) else 0) := by
  rw [dV, sser, dT_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [dT_monomial]
  congr 1
  simp [MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

theorem dV_subst [DecidableEq (Option (Fin e))] (v : Var g e m') (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
    dV v (subst (m' := m') i H) =
      subst i (MvPolynomial.pderiv none H) * dV v (xser i) +
        ∑ j : Fin e, subst i (MvPolynomial.pderiv (some j) H) * dV v (wser i j) := by
  rw [dV, subst, dT_aeval, Fintype.sum_option]
  rfl

theorem coeff_zero_substAt (pt : Var g e m' → A) (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
    (substAt pt i H).coeff 0 = MvPolynomial.eval (Data.ptCoord pt i) H := by
  rw [substAt, Polynomial.coeff_zero_eq_aeval_zero, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hco : (fun o => Polynomial.aeval (0 : A) (coordAt pt i o)) = Data.ptCoord pt i := by
    funext o
    cases o with
    | none => simp [coordAt, Data.ptCoord]
    | some j =>
      simp only [coordAt, Data.ptCoord, Option.elim_some, wpoly, ← Polynomial.coeff_zero_eq_aeval_zero,
        Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single (0 : Fin (m' + 1))]
      · simp
      · intro r _ hr
        rw [if_neg]
        exact fun h => hr (Fin.ext (by simpa using h))
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [hco]
  rfl

end IncidenceSystem
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

namespace IncidenceSystem
p2m_export "IncidenceSystem" "Var Data R xser wser sser subst cc Data.ptCoord wpoly spoly coordAt substAt map_eval_sser map_eval_subst Var.σ.injEq Var.w.injEq Var.σ Var.w Var.u Var.c"
p2m_open "IncidenceSystem"

variable {g e m' : ℕ} {A : Type*} [CommRing A]

theorem pderiv_coeff (v : Var g e m') (Q : Polynomial (R g e m' A)) (r : ℕ) :
    MvPolynomial.pderiv v (Q.coeff r) = (dV v Q).coeff r := by
  rw [dV, coeff_dT]; rfl

namespace Data
p2m_export "IncidenceSystem.Data" "branch inv tc inc system jacobian tcMatrix ptCoord dG sVal map p s G"
p2m_open "IncidenceSystem.Data"

variable (D : Data g e m' A) [DecidableEq (Option (Fin e))]

theorem pderiv_branch (v : Var g e m') (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) :
    MvPolynomial.pderiv v (D.branch i j r) =
      (subst i (MvPolynomial.pderiv none (D.G i j)) * dV v (xser i) +
        ∑ j' : Fin e, subst i (MvPolynomial.pderiv (some j') (D.G i j)) * dV v (wser i j')).coeff r := by
  rw [branch, pderiv_coeff, dV_subst]

theorem pderiv_inv (v : Var g e m') (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.pderiv v (D.inv k i r) =
      (dV v (sser k i) * subst i (D.s k i) + sser k i * dV v (subst i (D.s k i))).coeff r := by
  rw [inv, pderiv_coeff]
  congr 1
  rw [dV, ← dV, show sser k i * subst i (D.s k i) - 1 = sser k i * subst i (D.s k i) + (-1) from sub_eq_add_neg _ _]
  rw [dV, dT_add, dT_mul, ← Polynomial.C_1, ← Polynomial.C_neg, dT_C]
  simp

theorem pderiv_tc (v : Var g e m') (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.pderiv v (D.tc k i r) =
      (dV v (subst i (D.p k i)) * sser k i + subst i (D.p k i) * dV v (sser k i)).coeff r := by
  rw [tc, pderiv_coeff, dV, dT_mul]

theorem pderiv_inc (v : Var g e m') (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.pderiv v (D.inc i r) =
      ∑ k : Option (Fin (g * m')), (MvPolynomial.pderiv v (cc k) * D.tc k i r + cc k * MvPolynomial.pderiv v (D.tc k i r)) := by
  rw [inc, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(MvPolynomial.pderiv v).leibniz, smul_eq_mul, smul_eq_mul]
  ring

end Data
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

theorem coeff_mul_monomial_one {S : Type*} [CommRing S] (Q : Polynomial S) (r r' : ℕ) :
    (Q * Polynomial.monomial r' 1).coeff r = if r' ≤ r then Q.coeff (r - r') else 0 := by
  rw [← Polynomial.X_pow_eq_monomial, Polynomial.coeff_mul_X_pow']

theorem coeff_monomial_one_mul {S : Type*} [CommRing S] (Q : Polynomial S) (r r' : ℕ) :
    (Polynomial.monomial r' 1 * Q).coeff r = if r' ≤ r then Q.coeff (r - r') else 0 := by
  rw [mul_comm, coeff_mul_monomial_one]

end IncidenceSystem
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

namespace IncidenceSystem
p2m_export "IncidenceSystem" "Var Data R xser wser sser subst cc Data.ptCoord wpoly spoly coordAt substAt map_eval_sser map_eval_subst Var.σ.injEq Var.w.injEq Var.σ Var.w Var.u Var.c"
p2m_open "IncidenceSystem"

variable {g e m' : ℕ} {A : Type*} [CommRing A]

section dVvalues

variable (i : Fin g)

@[scoped simp] theorem dV_u_xser (i' : Fin g) :
    dV (Var.u i') (xser (e := e) (m' := m') (A := A) i) = Polynomial.C (if i' = i then 1 else 0) := by
  rw [dV_xser]; congr 1; simp [eq_comm]

@[scoped simp] theorem dV_w_xser (i' : Fin g) (j' : Fin e) (r' : Fin (m' + 1)) :
    dV (Var.w i' j' r') (xser (e := e) (m' := m') (A := A) i) = 0 := by
  rw [dV_xser]; simp

@[scoped simp] theorem dV_σ_xser (k' : Option (Fin (g * m'))) (i' : Fin g) (r' : Fin (m' + 1)) :
    dV (Var.σ k' i' r') (xser (e := e) (m' := m') (A := A) i) = 0 := by
  rw [dV_xser]; simp

@[scoped simp] theorem dV_c_xser (k' : Fin (g * m')) :
    dV (Var.c k') (xser (e := e) (m' := m') (A := A) i) = 0 := by
  rw [dV_xser]; simp

@[scoped simp] theorem dV_u_wser (i' : Fin g) (j : Fin e) :
    dV (Var.u i') (wser (m' := m') (A := A) i j) = 0 := by
  rw [dV_wser]; simp

@[scoped simp] theorem dV_w_wser (i' : Fin g) (j j' : Fin e) (r' : Fin (m' + 1)) :
    dV (Var.w i' j' r') (wser (m' := m') (A := A) i j) =
      if i' = i ∧ j' = j then Polynomial.monomial (r' : ℕ) 1 else 0 := by
  rw [dV_wser]
  by_cases h : i' = i ∧ j' = j
  · rw [if_pos h, Finset.sum_eq_single r']
    · simp [h]
    · intro ρ _ hρ; rw [if_neg]; · simp
      rintro ⟨-, -, rfl⟩; exact hρ rfl
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [if_neg]; · simp
    intro hh
    simp only [Var.w.injEq, Var.σ.injEq] at hh
    exact h ⟨hh.1, hh.2.1⟩

@[scoped simp] theorem dV_σ_wser (k' : Option (Fin (g * m'))) (i' : Fin g) (r' : Fin (m' + 1)) (j : Fin e) :
    dV (Var.σ k' i' r') (wser (m' := m') (A := A) i j) = 0 := by
  rw [dV_wser]; simp

@[scoped simp] theorem dV_c_wser (k' : Fin (g * m')) (j : Fin e) :
    dV (Var.c k') (wser (m' := m') (A := A) i j) = 0 := by
  rw [dV_wser]; simp

@[scoped simp] theorem dV_u_sser (i' : Fin g) (k : Option (Fin (g * m'))) :
    dV (Var.u i') (sser (e := e) (A := A) k i) = 0 := by
  rw [dV_sser]; simp

@[scoped simp] theorem dV_w_sser (i' : Fin g) (j' : Fin e) (r' : Fin (m' + 1)) (k : Option (Fin (g * m'))) :
    dV (Var.w i' j' r') (sser (e := e) (A := A) k i) = 0 := by
  rw [dV_sser]; simp

@[scoped simp] theorem dV_σ_sser (k k' : Option (Fin (g * m'))) (i' : Fin g) (r' : Fin (m' + 1)) :
    dV (Var.σ k' i' r') (sser (e := e) (A := A) k i) =
      if k' = k ∧ i' = i then Polynomial.monomial (r' : ℕ) 1 else 0 := by
  rw [dV_sser]
  by_cases h : k' = k ∧ i' = i
  · rw [if_pos h, Finset.sum_eq_single r']
    · simp [h]
    · intro ρ _ hρ; rw [if_neg]; · simp
      rintro ⟨-, -, rfl⟩; exact hρ rfl
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [if_neg]; · simp
    intro hh
    simp only [Var.w.injEq, Var.σ.injEq] at hh
    exact h ⟨hh.1, hh.2.1⟩

@[scoped simp] theorem dV_c_sser (k' : Fin (g * m')) (k : Option (Fin (g * m'))) :
    dV (Var.c k') (sser (e := e) (A := A) k i) = 0 := by
  rw [dV_sser]; simp

variable [DecidableEq (Option (Fin e))] (H : MvPolynomial (Option (Fin e)) A)

theorem dV_u_subst (i' : Fin g) :
    dV (Var.u i') (subst (m' := m') i H) =
      if i' = i then subst i (MvPolynomial.pderiv none H) else 0 := by
  rw [dV_subst]; split_ifs <;> simp [*]

theorem dV_w_subst (i' : Fin g) (j' : Fin e) (r' : Fin (m' + 1)) :
    dV (Var.w i' j' r') (subst (m' := m') i H) =
      if i' = i then subst i (MvPolynomial.pderiv (some j') H) * Polynomial.monomial (r' : ℕ) 1 else 0 := by
  rw [dV_subst]
  simp only [dV_w_xser, mul_zero, zero_add, dV_w_wser]
  by_cases h : i' = i
  · simp only [h, true_and, if_true, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  · simp [h]

theorem dV_σ_subst (k' : Option (Fin (g * m'))) (i' : Fin g) (r' : Fin (m' + 1)) :
    dV (Var.σ k' i' r') (subst (m' := m') i H) = 0 := by
  rw [dV_subst]; simp

theorem dV_c_subst (k' : Fin (g * m')) :
    dV (Var.c k') (subst (m' := m') i H) = 0 := by
  rw [dV_subst]; simp

end dVvalues
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

@[scoped simp] theorem pderiv_cc_u (i : Fin g) (k : Option (Fin (g * m'))) :
    MvPolynomial.pderiv (Var.u i) (cc (e := e) (A := A) k) = 0 := by
  cases k <;> simp [cc]

@[scoped simp] theorem pderiv_cc_w (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) (k : Option (Fin (g * m'))) :
    MvPolynomial.pderiv (Var.w i j r) (cc (A := A) k) = 0 := by
  cases k <;> simp [cc]

@[scoped simp] theorem pderiv_cc_σ (k' : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) (k : Option (Fin (g * m'))) :
    MvPolynomial.pderiv (Var.σ k' i r) (cc (e := e) (A := A) k) = 0 := by
  cases k <;> simp [cc]

theorem pderiv_cc_c (k' : Fin (g * m')) (k : Option (Fin (g * m'))) :
    MvPolynomial.pderiv (Var.c k') (cc (e := e) (A := A) k) = if k = some k' then 1 else 0 := by
  cases k <;> simp [cc, Pi.single_apply, eq_comm]

end IncidenceSystem
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

namespace IncidenceSystem
p2m_export "IncidenceSystem" "Var Data R xser wser sser subst cc Data.ptCoord wpoly spoly coordAt substAt map_eval_sser map_eval_subst Var.σ.injEq Var.w.injEq Var.σ Var.w Var.u Var.c"
p2m_open "IncidenceSystem"

variable {g e m' : ℕ} {A : Type*} [CommRing A]

theorem eval_coeff (pt : Var g e m' → A) (Q : Polynomial (R g e m' A)) (n : ℕ) :
    MvPolynomial.eval pt (Q.coeff n) = (Q.map (MvPolynomial.eval pt)).coeff n := by
  rw [Polynomial.coeff_map]

namespace Data
p2m_export "IncidenceSystem.Data" "branch inv tc inc system jacobian tcMatrix ptCoord dG sVal map p s G"
p2m_open "IncidenceSystem.Data"

variable (D : Data g e m' A) (pt : Var g e m' → A)

section Entries

variable [DecidableEq (Option (Fin e))]

private theorem _root_.IncidenceSystem.Data.entry_branch_w (i i' : Fin g) (j j' : Fin e) (r r' : Fin (m' + 1)) :
    MvPolynomial.eval pt (MvPolynomial.pderiv (Var.w i' j' r') (D.branch i j r)) =
      if i' = i then (if (r' : ℕ) ≤ r then (substAt pt i (MvPolynomial.pderiv (some j') (D.G i j))).coeff (r - r')
        else 0) else 0 := by
  rw [pderiv_branch, eval_coeff]
  simp only [dV_w_xser, mul_zero, zero_add, dV_w_wser]
  by_cases h : i' = i
  · simp only [h, true_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Polynomial.map_mul, map_eval_subst, Polynomial.map_monomial, map_one, coeff_mul_monomial_one]
  · simp [h]

p2m_export "IncidenceSystem.Data" "entry_branch_w"

private theorem _root_.IncidenceSystem.Data.entry_branch_σ (i i' : Fin g) (j : Fin e) (k' : Option (Fin (g * m'))) (r r' : Fin (m' + 1)) :
    MvPolynomial.eval pt (MvPolynomial.pderiv (Var.σ k' i' r') (D.branch i j r)) = 0 := by
  rw [pderiv_branch, eval_coeff]
  simp

p2m_export "IncidenceSystem.Data" "entry_branch_σ"

private theorem _root_.IncidenceSystem.Data.entry_inv_σ (i i' : Fin g) (k k' : Option (Fin (g * m'))) (r r' : Fin (m' + 1)) :
    MvPolynomial.eval pt (MvPolynomial.pderiv (Var.σ k' i' r') (D.inv k i r)) =
      if k' = k ∧ i' = i then (if (r' : ℕ) ≤ r then (substAt pt i (D.s k i)).coeff (r - r') else 0) else 0 := by
  rw [pderiv_inv, eval_coeff]
  simp only [dV_σ_sser, dV_σ_subst, mul_zero, add_zero]
  split_ifs with h
  · simp only [Polynomial.map_mul, Polynomial.map_monomial, map_one, map_eval_subst, coeff_monomial_one_mul, if_pos ‹_›]
  · simp only [Polynomial.map_mul, Polynomial.map_monomial, map_one, map_eval_subst, coeff_monomial_one_mul, if_neg ‹_›]
  · simp

p2m_export "IncidenceSystem.Data" "entry_inv_σ"

private theorem _root_.IncidenceSystem.Data.entry_inc_c (i : Fin g) (r : Fin (m' + 1)) (k' : Fin (g * m')) :
    MvPolynomial.eval pt (MvPolynomial.pderiv (Var.c k') (D.inc i r)) = MvPolynomial.eval pt (D.tc (some k') i r) := by
  rw [pderiv_inc]
  have htc : ∀ k, MvPolynomial.pderiv (Var.c k') (D.tc k i r) = 0 := fun k => by
    rw [pderiv_tc, dV_c_subst, dV_c_sser]; simp
  simp only [htc, mul_zero, add_zero, pderiv_cc_c, ite_mul, one_mul, zero_mul, map_sum]
  rw [Finset.sum_eq_single (some k')]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ _) h

p2m_export "IncidenceSystem.Data" "entry_inc_c"
variable (hc : ∀ k, pt (Var.c k) = 0)
  (hp : ∀ i, D.p none i = (MvPolynomial.X none - MvPolynomial.C (pt (Var.u i))) ^ (m' + 1))

include hc in

private theorem _root_.IncidenceSystem.Data.eval_pderiv_inc_of_c (v : Var g e m') (hv : ∀ k, MvPolynomial.pderiv v (cc (e := e) (A := A) k) = 0)
    (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (MvPolynomial.pderiv v (D.inc i r)) =
      MvPolynomial.eval pt (MvPolynomial.pderiv v (D.tc none i r)) := by
  rw [pderiv_inc, map_sum, Fintype.sum_option]
  simp only [hv, zero_mul, zero_add]
  simp [cc, hc]

p2m_export "IncidenceSystem.Data" "eval_pderiv_inc_of_c"
include hp in
private theorem _root_.IncidenceSystem.Data.substAt_p_none (i : Fin g) : substAt pt i (D.p none i) = Polynomial.X ^ (m' + 1) := by
  rw [hp, substAt, map_pow, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_apply]
  simp [coordAt]

p2m_export "IncidenceSystem.Data" "substAt_p_none"
include hp in
private theorem _root_.IncidenceSystem.Data.pderiv_some_p_none (i : Fin g) (j : Fin e) : MvPolynomial.pderiv (some j) (D.p none i) = 0 := by
  rw [hp]
  simp [(MvPolynomial.pderiv (some j)).leibniz_pow, MvPolynomial.pderiv_X]

p2m_export "IncidenceSystem.Data" "pderiv_some_p_none"
include hp in
private theorem _root_.IncidenceSystem.Data.substAt_pderiv_none_p_none (i : Fin g) :
    substAt pt i (MvPolynomial.pderiv none (D.p none i)) = ((m' + 1 : ℕ) : Polynomial A) * Polynomial.X ^ m' := by
  rw [hp, (MvPolynomial.pderiv none).leibniz_pow]
  simp [substAt, coordAt, MvPolynomial.pderiv_X, smul_eq_mul, map_mul, map_pow]

p2m_export "IncidenceSystem.Data" "substAt_pderiv_none_p_none"
include hc hp in

private theorem _root_.IncidenceSystem.Data.entry_inc_w (i i' : Fin g) (j' : Fin e) (r r' : Fin (m' + 1)) :
    MvPolynomial.eval pt (MvPolynomial.pderiv (Var.w i' j' r') (D.inc i r)) = 0 := by
  rw [D.eval_pderiv_inc_of_c pt hc _ (fun k => pderiv_cc_w i' j' r' k), pderiv_tc, eval_coeff, dV_w_subst,
    D.pderiv_some_p_none pt hp, dV_w_sser]
  simp [subst]

p2m_export "IncidenceSystem.Data" "entry_inc_w"
include hc hp in

private theorem _root_.IncidenceSystem.Data.entry_inc_σ (i i' : Fin g) (k' : Option (Fin (g * m'))) (r r' : Fin (m' + 1)) :
    MvPolynomial.eval pt (MvPolynomial.pderiv (Var.σ k' i' r') (D.inc i r)) = 0 := by
  rw [D.eval_pderiv_inc_of_c pt hc _ (fun k => pderiv_cc_σ k' i' r' k), pderiv_tc, eval_coeff]
  simp only [dV_σ_subst, zero_mul, zero_add, dV_σ_sser]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [Polynomial.map_mul, map_eval_subst, D.substAt_p_none pt hp, Polynomial.map_monomial, map_one,
      coeff_mul_monomial_one]
    split_ifs
    · rw [Polynomial.coeff_X_pow, if_neg]; omega
    · rfl
  · simp

p2m_export "IncidenceSystem.Data" "entry_inc_σ"
variable (hσ : ∀ i r, pt (Var.σ none i r) = if (r : ℕ) = 0 then 1 else 0)

include hσ in
theorem spoly_none (i : Fin g) : spoly pt none i = 1 := by
  rw [spoly, Finset.sum_eq_single (0 : Fin (m' + 1))]
  · simp [hσ]
  · intro r _ hr
    rw [hσ, if_neg, Polynomial.monomial_zero_right]
    exact fun h => hr (Fin.ext (by simpa using h))
  · intro h; exact absurd (Finset.mem_univ _) h

include hc hp hσ in

private theorem _root_.IncidenceSystem.Data.entry_inc_u (i i' : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (MvPolynomial.pderiv (Var.u i') (D.inc i r)) =
      if i' = i ∧ (r : ℕ) = m' then ((m' + 1 : ℕ) : A) else 0 := by
  rw [D.eval_pderiv_inc_of_c pt hc _ (fun k => pderiv_cc_u i' k), pderiv_tc, eval_coeff]
  simp only [dV_u_subst, dV_u_sser, mul_zero, add_zero]
  by_cases h : i' = i
  · simp only [h, if_true, true_and, Polynomial.map_mul, map_eval_subst, map_eval_sser,
      D.substAt_pderiv_none_p_none pt hp, spoly_none pt hσ, mul_one]
    rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp
  · simp [h]

p2m_export "IncidenceSystem.Data" "entry_inc_u"
end Entries
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

end Data
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

end IncidenceSystem
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

namespace IncidenceSystem
p2m_export "IncidenceSystem" "Var Data R xser wser sser subst cc Data.ptCoord wpoly spoly coordAt substAt map_eval_sser map_eval_subst Var.σ.injEq Var.w.injEq Var.σ Var.w Var.u Var.c"
p2m_open "IncidenceSystem"

variable {g e m' : ℕ} {A : Type*} [CommRing A]

abbrev IU (g m' : ℕ) := Fin g ⊕ Fin (g * m')

abbrev IW (g e m' : ℕ) := Fin g ×ₗ (Fin e ×ₗ Fin (m' + 1))

abbrev IS (g m' : ℕ) := Fin (g * m' + 1) ×ₗ (Fin g ×ₗ Fin (m' + 1))

scoped instance instDecidableEqIW : DecidableEq (IW g e m') :=
  inferInstanceAs (DecidableEq (Fin g × (Fin e × Fin (m' + 1))))
scoped instance instDecidableEqIS : DecidableEq (IS g m') :=
  inferInstanceAs (DecidableEq (Fin (g * m' + 1) × (Fin g × Fin (m' + 1))))
scoped instance instFintypeIW : Fintype (IW g e m') := inferInstanceAs (Fintype (Fin g × (Fin e × Fin (m' + 1))))
scoped instance instFintypeIS : Fintype (IS g m') := inferInstanceAs (Fintype (Fin (g * m' + 1) × (Fin g × Fin (m' + 1))))

def toBlock : Var g e m' → IU g m' ⊕ (IW g e m' ⊕ IS g m')
  | Var.u i => Sum.inl (Sum.inl i)
  | Var.c k => Sum.inl (Sum.inr k)
  | Var.w i j r => Sum.inr (Sum.inl (toLex (i, toLex (j, r))))
  | Var.σ k i r => Sum.inr (Sum.inr (toLex ((finSuccEquiv (g * m')).symm k, toLex (i, r))))

def ofBlock : IU g m' ⊕ (IW g e m' ⊕ IS g m') → Var g e m'
  | Sum.inl (Sum.inl i) => Var.u i
  | Sum.inl (Sum.inr k) => Var.c k
  | Sum.inr (Sum.inl p) => Var.w (ofLex p).1 (ofLex (ofLex p).2).1 (ofLex (ofLex p).2).2
  | Sum.inr (Sum.inr p) => Var.σ (finSuccEquiv (g * m') (ofLex p).1) (ofLex (ofLex p).2).1 (ofLex (ofLex p).2).2

def blockEquiv : Var g e m' ≃ IU g m' ⊕ (IW g e m' ⊕ IS g m') where
  toFun := toBlock
  invFun := ofBlock
  left_inv v := by cases v <;> simp [toBlock, ofBlock]
  right_inv p := by
    rcases p with (i | k) | (p | p)
    · rfl
    · rfl
    · simp [toBlock, ofBlock]
    · simp [toBlock, ofBlock]

@[scoped simp] theorem blockEquiv_symm_apply (p : IU g m' ⊕ (IW g e m' ⊕ IS g m')) :
    (blockEquiv (g := g) (e := e) (m' := m')).symm p = ofBlock p := rfl

namespace Data
p2m_export "IncidenceSystem.Data" "branch inv tc inc system jacobian tcMatrix ptCoord dG sVal map p s G"
p2m_open "IncidenceSystem.Data"

variable (D : Data g e m' A) (pt : Var g e m' → A)

theorem prod_pow_eq_prod_lex {M : Type*} [CommMonoid M] {α β : Type*} [Fintype α] [Fintype β] (n : ℕ)
    (f : α → β → M) :
    (∏ p : α ×ₗ (β ×ₗ Fin n), f (ofLex p).1 (ofLex (ofLex p).2).1) = ∏ a, ∏ b, f a b ^ n := by
  rw [← Fintype.prod_equiv (toLex.trans (Equiv.refl _)) (fun q : α × (β ×ₗ Fin n) => f q.1 (ofLex q.2).1) _ (fun _ => rfl)]
  rw [Fintype.prod_prod_type]
  refine Fintype.prod_congr _ _ fun a => ?_
  rw [← Fintype.prod_equiv toLex (fun q : β × Fin n => f a q.1) _ (fun _ => rfl), Fintype.prod_prod_type]
  simp

private theorem _root_.IncidenceSystem.Data.det_jacobian
    (htri : ∀ i (j j' : Fin e), j < j' → MvPolynomial.pderiv (some j') (D.G i j) = 0)
    (hc : ∀ k, pt (Var.c k) = 0)
    (hσ : ∀ i r, pt (Var.σ none i r) = if (r : ℕ) = 0 then 1 else 0)
    (hp : ∀ i, D.p none i = (MvPolynomial.X none - MvPolynomial.C (pt (Var.u i))) ^ (m' + 1))
    (hs : ∀ i, D.s none i = 1) :
    (D.jacobian pt).det =
      ((m' + 1 : ℕ) : A) ^ g * (D.tcMatrix pt).det *
        ((∏ i, ∏ j, D.dG pt i j ^ (m' + 1)) * ∏ k, ∏ i, D.sVal pt k i ^ (m' + 1)) := by
  rw [← Matrix.det_reindex_self blockEquiv (D.jacobian pt)]
  set M := Matrix.reindex blockEquiv blockEquiv (D.jacobian pt) with hM
  have hMapply : ∀ a b, M a b = D.jacobian pt (ofBlock a) (ofBlock b) := fun a b => rfl

  have h12 : M.toBlocks₁₂ = 0 := by
    ext a b
    rcases a with i | k <;> rcases b with p | p <;>
      simp [Matrix.toBlocks₁₂, hMapply, ofBlock, jacobian, system, D.entry_inc_w pt hc hp, D.entry_inc_σ pt hc hp]

  have h11 : M.toBlocks₁₁ = Matrix.fromBlocks (((m' + 1 : ℕ) : A) • (1 : Matrix (Fin g) (Fin g) A))
      (Matrix.of fun i k' => MvPolynomial.eval pt (D.tc (some k') i (Fin.last m'))) 0 (D.tcMatrix pt) := by
    ext a b
    rcases a with i | k <;> rcases b with i' | k'
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hMapply, ofBlock, jacobian, system, Matrix.fromBlocks_apply₁₁,
        D.entry_inc_u pt hc hp hσ, Fin.val_last, and_true, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    · simp [Matrix.toBlocks₁₁, hMapply, ofBlock, jacobian, system, D.entry_inc_c pt]
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hMapply, ofBlock, jacobian, system, Matrix.fromBlocks_apply₂₁,
        D.entry_inc_u pt hc hp hσ, Matrix.zero_apply]
      rw [if_neg]
      rintro ⟨-, h⟩
      exact absurd h (ne_of_lt (Fin.castSucc_lt_last _))
    · simp [Matrix.toBlocks₁₁, hMapply, ofBlock, jacobian, system, D.entry_inc_c pt, tcMatrix]

  have h2212 : M.toBlocks₂₂.toBlocks₁₂ = 0 := by
    ext p p'
    simp [Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, hMapply, ofBlock, jacobian, system, D.entry_branch_σ pt]

  have hWentry : ∀ (i i' : Fin g) (j j' : Fin e) (r r' : Fin (m' + 1)),
      M.toBlocks₂₂.toBlocks₁₁ (toLex (i, toLex (j, r))) (toLex (i', toLex (j', r'))) =
        if i' = i then (if (r' : ℕ) ≤ r then
          (substAt pt i (MvPolynomial.pderiv (some j') (D.G i j))).coeff (r - r') else 0) else 0 := by
    intro i i' j j' r r'
    simp only [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply, hMapply, ofBlock, ofLex_toLex, jacobian, system,
      D.entry_branch_w pt]
  have hWtri : (M.toBlocks₂₂.toBlocks₁₁).BlockTriangular OrderDual.toDual := by
    intro p p' hlt
    have hlt' : p < p' := hlt
    obtain ⟨i, j, r⟩ := p
    obtain ⟨i', j', r'⟩ := p'
    have key : i < i' ∨ i = i' ∧ (j < j' ∨ j = j' ∧ r < r') := by
      have h1 := Prod.Lex.lt_iff.mp hlt'
      rcases h1 with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, Prod.Lex.lt_iff.mp h2⟩
    rw [show ((i, j, r) : IW g e m') = toLex (i, toLex (j, r)) from rfl,
      show ((i', j', r') : IW g e m') = toLex (i', toLex (j', r')) from rfl, hWentry]
    rcases key with hii | ⟨rfl, hjr⟩
    · rw [if_neg (ne_of_gt hii)]
    · rw [if_pos rfl]
      rcases hjr with hjj | ⟨rfl, hrr⟩
      · rw [htri i j j' hjj]; simp [substAt]
      · rw [if_neg (not_le.mpr (Fin.lt_def.mp hrr))]
  have hWdet : (M.toBlocks₂₂.toBlocks₁₁).det = ∏ i, ∏ j, D.dG pt i j ^ (m' + 1) := by
    rw [Matrix.det_of_lowerTriangular _ hWtri]
    have hdiag : ∀ p : IW g e m', M.toBlocks₂₂.toBlocks₁₁ p p = D.dG pt (ofLex p).1 (ofLex (ofLex p).2).1 := by
      intro p
      obtain ⟨i, j, r⟩ := p
      rw [show ((i, j, r) : IW g e m') = toLex (i, toLex (j, r)) from rfl, hWentry]
      simp [coeff_zero_substAt, dG]
    simp_rw [hdiag]
    exact prod_pow_eq_prod_lex (m' + 1) (D.dG pt)
  have hSentry : ∀ (κ κ' : Fin (g * m' + 1)) (i i' : Fin g) (r r' : Fin (m' + 1)),
      M.toBlocks₂₂.toBlocks₂₂ (toLex (κ, toLex (i, r))) (toLex (κ', toLex (i', r'))) =
        if finSuccEquiv (g * m') κ' = finSuccEquiv (g * m') κ ∧ i' = i then (if (r' : ℕ) ≤ r then
          (substAt pt i (D.s (finSuccEquiv (g * m') κ) i)).coeff (r - r') else 0) else 0 := by
    intro κ κ' i i' r r'
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, hMapply, ofBlock, ofLex_toLex, jacobian, system, D.entry_inv_σ pt]
  have hStri : (M.toBlocks₂₂.toBlocks₂₂).BlockTriangular OrderDual.toDual := by
    intro p p' hlt
    have hlt' : p < p' := hlt
    obtain ⟨κ, i, r⟩ := p
    obtain ⟨κ', i', r'⟩ := p'
    have key : κ < κ' ∨ κ = κ' ∧ (i < i' ∨ i = i' ∧ r < r') := by
      have h1 := Prod.Lex.lt_iff.mp hlt'
      rcases h1 with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, Prod.Lex.lt_iff.mp h2⟩
    rw [show ((κ, i, r) : IS g m') = toLex (κ, toLex (i, r)) from rfl,
      show ((κ', i', r') : IS g m') = toLex (κ', toLex (i', r')) from rfl, hSentry]
    rcases key with hkk | ⟨rfl, hir⟩
    · rw [if_neg]
      rintro ⟨h, -⟩
      exact absurd ((finSuccEquiv (g * m')).injective h) (ne_of_gt hkk)
    · rcases hir with hii | ⟨rfl, hrr⟩
      · rw [if_neg]
        rintro ⟨-, h⟩
        exact absurd h (ne_of_gt hii)
      · rw [if_pos ⟨rfl, rfl⟩, if_neg (not_le.mpr (Fin.lt_def.mp hrr))]
  have hSdet : (M.toBlocks₂₂.toBlocks₂₂).det = ∏ k, ∏ i, D.sVal pt k i ^ (m' + 1) := by
    rw [Matrix.det_of_lowerTriangular _ hStri]
    have hdiag : ∀ p : IS g m', M.toBlocks₂₂.toBlocks₂₂ p p =
        D.sVal pt (finSuccEquiv (g * m') (ofLex p).1) (ofLex (ofLex p).2).1 := by
      intro p
      obtain ⟨κ, i, r⟩ := p
      rw [show ((κ, i, r) : IS g m') = toLex (κ, toLex (i, r)) from rfl, hSentry]
      simp [coeff_zero_substAt, sVal]
    simp_rw [hdiag]
    exact (prod_pow_eq_prod_lex (m' + 1) (fun κ i => D.sVal pt (finSuccEquiv (g * m') κ) i)).trans
      (Fintype.prod_equiv (finSuccEquiv (g * m')) _ _ (fun _ => rfl))
  have h22 : M.toBlocks₂₂.det = (∏ i, ∏ j, D.dG pt i j ^ (m' + 1)) * ∏ k, ∏ i, D.sVal pt k i ^ (m' + 1) := by
    rw [← Matrix.fromBlocks_toBlocks M.toBlocks₂₂, h2212, Matrix.det_fromBlocks_zero₁₂, hWdet, hSdet]
  rw [← Matrix.fromBlocks_toBlocks M, h12, Matrix.det_fromBlocks_zero₁₂, h11, Matrix.det_fromBlocks_zero₂₁, h22,
    Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

p2m_export "IncidenceSystem.Data" "det_jacobian"
end Data
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

end IncidenceSystem
p2m_reactivate "P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem"

open _root_.IncidenceSystem _root_.P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.IncidenceSystem in
theorem solution
    {g e m' : ℕ} {A : Type*} [CommRing A] (D : IncidenceSystem.Data g e m' A) (pt : Var g e m' → A)
    (htri : ∀ i (j j' : Fin e), j < j' → MvPolynomial.pderiv (some j') (D.G i j) = 0)
    (hc : ∀ k, pt (Var.c k) = 0)
    (hσ : ∀ i r, pt (Var.σ none i r) = if (r : ℕ) = 0 then 1 else 0)
    (hp : ∀ i, D.p none i = (MvPolynomial.X none - MvPolynomial.C (pt (Var.u i))) ^ (m' + 1))
    (hs : ∀ i, D.s none i = 1)
    (hG : ∀ i j, IsUnit (D.dG pt i j)) (hsv : ∀ k i, IsUnit (D.sVal pt k i)) :
    IsUnit (D.jacobian pt).det ↔ IsUnit (((m' + 1 : ℕ) : A) ^ g) ∧ IsUnit (D.tcMatrix pt).det := by
  classical
  have hu : IsUnit ((∏ i, ∏ j, D.dG pt i j ^ (m' + 1)) * ∏ k, ∏ i, D.sVal pt k i ^ (m' + 1)) :=
    (IsUnit.prod_univ_iff.mpr fun i => IsUnit.prod_univ_iff.mpr fun j => (hG i j).pow _).mul
      (IsUnit.prod_univ_iff.mpr fun k => IsUnit.prod_univ_iff.mpr fun i => (hsv k i).pow _)
  rw [D.det_jacobian pt htri hc hσ hp hs, IsUnit.mul_iff, IsUnit.mul_iff, and_iff_left hu]

end S_IncidenceSystem_Data_isUnit_det_jacobian_iff
end P2MW
export P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff (solution)
