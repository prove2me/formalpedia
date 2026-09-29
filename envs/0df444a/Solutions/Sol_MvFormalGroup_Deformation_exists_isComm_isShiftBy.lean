-- Prove2me | solution 1 for MvFormalGroup.Deformation.exists_isComm_isShiftBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2079289f-5b1c-5460-9eba-876d672667c5

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
import Theorems.Thm_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
import Theorems.Thm_MvFormalGroup_mem_firstOrderCocycles_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Deformation_exists_isComm_isShiftBy

set_option autoImplicit false

noncomputable section

open MvPowerSeries MvFormalGroup IsLocalRing

namespace GRAux

section Sides
variable {k : Type} [CommRing k] {d : ℕ} (G₀ : MvFormalGroup d k)

def sideL (z : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (l : Fin d) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
  MvPowerSeries.subst (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G₀.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))) (z l) +
    ∑ i, MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (z i) * MvPowerSeries.subst (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G₀.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))) (MvPowerSeries.pderivLin (Sum.inl i) (G₀.toPowerSeries l))

def sideR (z : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (l : Fin d) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
  MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G₀.toPowerSeries q))) (z l) +
    ∑ i, MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (z i) * MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G₀.toPowerSeries q))) (MvPowerSeries.pderivLin (Sum.inr i) (G₀.toPowerSeries l))

theorem famL_cc (s : (Fin d ⊕ Fin d)) : MvPowerSeries.constantCoeff ((Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G₀.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))) s) = 0 := by
  rcases s with j | j
  · exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _))
      (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _) (G₀.constantCoeff_eq_zero j)
  · exact MvPowerSeries.constantCoeff_X _

theorem famR_cc (s : (Fin d ⊕ Fin d)) : MvPowerSeries.constantCoeff ((Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G₀.toPowerSeries q))) s) = 0 := by
  rcases s with j | j
  · exact MvPowerSeries.constantCoeff_X _
  · exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _))
      (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _) (G₀.constantCoeff_eq_zero j)

theorem hasSubst_XY : MvPowerSeries.HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _)
theorem hasSubst_YZ : MvPowerSeries.HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _)
theorem hasSubst_SW : MvPowerSeries.HasSubst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) k)) fun q => MvPowerSeries.X (Sum.inl q)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _)

end Sides

section Push
variable {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) {d : ℕ} (G : MvFormalGroup d R)

theorem pderiv_map {σ : Type} (s : σ) (g : MvPowerSeries σ R) :
    MvPowerSeries.pderivLin s (MvPowerSeries.map π g) = MvPowerSeries.map π (MvPowerSeries.pderivLin s g) := by
  refine MvPowerSeries.ext fun n => ?_
  rw [MvPowerSeries.kw_coeff_pderiv, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, MvPowerSeries.kw_coeff_pderiv, map_nsmul]

theorem map_subst_rename {σ₁ σ₂ : Type} [Fintype σ₁] (wR : σ₁ → MvPowerSeries σ₂ R) (wS : σ₁ → MvPowerSeries σ₂ S)
    (hw : ∀ s, MvPowerSeries.map π (wR s) = wS s) (hcc : ∀ s, MvPowerSeries.constantCoeff (wR s) = 0) (g : MvPowerSeries σ₁ R) :
    MvPowerSeries.map π (MvPowerSeries.subst wR g) = MvPowerSeries.subst wS (MvPowerSeries.map π g) := by
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hcc)]
  congr 1
  funext s; exact hw s

theorem map_famL (s : (Fin d ⊕ Fin d)) :
    MvPowerSeries.map π ((Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))) s) = (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) S)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) ((G.map π).toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) S))) s := by
  rcases s with j | j
  · exact map_subst_rename π _ _ (by rintro (l | l) <;> exact MvPowerSeries.map_X _ _) (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _) _
  · exact MvPowerSeries.map_X _ _

theorem map_famR (s : (Fin d ⊕ Fin d)) :
    MvPowerSeries.map π ((Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G.toPowerSeries q))) s) = (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) S)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) S)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) ((G.map π).toPowerSeries q))) s := by
  rcases s with j | j
  · exact MvPowerSeries.map_X _ _
  · exact map_subst_rename π _ _ (by rintro (l | l) <;> exact MvPowerSeries.map_X _ _) (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _) _

theorem isComm_map [G.IsComm] : (G.map π).IsComm := by
  constructor
  intro i
  show MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) S)) fun q => MvPowerSeries.X (Sum.inl q)) (MvPowerSeries.map π (G.toPowerSeries i)) = MvPowerSeries.map π (G.toPowerSeries i)
  rw [← map_subst_rename π (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) R)) fun q => MvPowerSeries.X (Sum.inl q)) (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) S)) fun q => MvPowerSeries.X (Sum.inl q)) (by rintro (l | l) <;> exact MvPowerSeries.map_X _ _)
    (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _), MvFormalGroup.IsComm.comm]

end Push

section Pert

variable {B : Type} [CommRing B] [IsLocalRing B] {d n : ℕ} (G : MvFormalGroup d B)
  (j : Fin n → B) (hj2 : ∀ i i', j i * j i' = 0) (hjm : ∀ i, ∀ m ∈ maximalIdeal B, m * j i = 0)
  (Z : Fin n → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (z : Fin n → Fin d → MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))
  (hZ : ∀ i l, MvPowerSeries.map (residue B) (Z i l) = z i l)

def pert (l : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) B := G.toPowerSeries l + ∑ i, j i • Z i l

include hjm in
theorem smul_eq_of_map_eq {σ : Type} (i : Fin n) (T T' : MvPowerSeries σ B)
    (h : MvPowerSeries.map (residue B) T = MvPowerSeries.map (residue B) T') : j i • T = j i • T' :=
  MvPowerSeries.smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero (maximalIdeal B) (j i) (hjm i) T T' fun m => by
    rw [← Ideal.Quotient.eq, ← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map]
    exact congrArg (MvPowerSeries.coeff m) h

include hjm in
theorem smul_eq_zero_of_map_eq_zero {σ : Type} (i : Fin n) (T : MvPowerSeries σ B)
    (h : MvPowerSeries.map (residue B) T = 0) : j i • T = 0 := by
  rw [smul_eq_of_map_eq j hjm i T 0 (by rw [h, map_zero]), smul_zero]

include hjm in
theorem mul_eq_zero_of_residue_eq_zero (i : Fin n) (m : B) (hm : residue B m = 0) : j i * m = 0 := by
  rw [mul_comm]; exact hjm i m ((IsLocalRing.residue_eq_zero_iff m).mp hm)

include hjm hZ in
theorem pert_constantCoeff (h0 : ∀ i l, MvPowerSeries.constantCoeff (z i l) = 0) (l : Fin d) :
    MvPowerSeries.constantCoeff (pert G j Z l) = 0 := by
  rw [pert, map_add, G.constantCoeff_eq_zero, zero_add, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul]
  apply mul_eq_zero_of_residue_eq_zero j hjm i
  rw [← MvPowerSeries.coeff_map, hZ, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]

include hjm hZ in
theorem pert_coeff_single (s : (Fin d ⊕ Fin d)) (c : B) (l : Fin d) (hG : MvPowerSeries.coeff (Finsupp.single s 1) (G.toPowerSeries l) = c)
    (hz : ∀ i, MvPowerSeries.coeff (Finsupp.single s 1) (z i l) = 0) :
    MvPowerSeries.coeff (Finsupp.single s 1) (pert G j Z l) = c := by
  rw [pert, map_add, hG, map_sum, add_eq_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPowerSeries.coeff_smul]
  apply mul_eq_zero_of_residue_eq_zero j hjm i
  rw [← MvPowerSeries.coeff_map, hZ, hz]

include hjm hZ in
theorem pert_comm [G.IsComm] (hsw : ∀ i l, MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))) fun q => MvPowerSeries.X (Sum.inl q)) (z i l) = z i l) (l : Fin d) :
    MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) B)) fun q => MvPowerSeries.X (Sum.inl q)) (pert G j Z l) = pert G j Z l := by
  rw [pert, ← MvPowerSeries.coe_substAlgHom hasSubst_SW, map_add, map_sum, MvPowerSeries.coe_substAlgHom, MvFormalGroup.IsComm.comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_SW, map_smul, MvPowerSeries.coe_substAlgHom]
  apply smul_eq_of_map_eq j hjm i
  rw [map_subst_rename (residue B) (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) B)) fun q => MvPowerSeries.X (Sum.inl q)) (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))) fun q => MvPowerSeries.X (Sum.inl q)) (by rintro (q | q) <;> exact MvPowerSeries.map_X _ _)
    (by rintro (q | q) <;> exact MvPowerSeries.constantCoeff_X _), hZ, hsw]

end Pert

section PertAssoc

variable {B : Type} [CommRing B] [IsLocalRing B] {d n : ℕ} (G : MvFormalGroup d B)
  (j : Fin n → B) (hj2 : ∀ i i', j i * j i' = 0) (hjm : ∀ i, ∀ m ∈ maximalIdeal B, m * j i = 0)
  (Z : Fin n → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (z : Fin n → Fin d → MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))
  (hZ : ∀ i l, MvPowerSeries.map (residue B) (Z i l) = z i l)

include hj2 in

theorem isNilpotent_sum_mul (c : Fin n → B) : IsNilpotent (∑ i, j i * c i) :=
  ⟨2, by
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => by
      rw [mul_mul_mul_comm, hj2, zero_mul]⟩

include hj2 in
theorem hasSubst_pert_fam {σ τ : Type} [Fintype σ] (fam : σ → MvPowerSeries τ B) (Bf : σ → Fin n → MvPowerSeries τ B)
    (hfam : ∀ s, MvPowerSeries.constantCoeff (fam s) = 0) :
    MvPowerSeries.HasSubst (fun s => fam s + ∑ i, j i • Bf s i) :=
  MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by
    rw [map_add, hfam, zero_add, map_sum]
    simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul]
    exact isNilpotent_sum_mul j hj2 _

include hj2 in

theorem subst_pert_pert {σ τ : Type} [Fintype σ] [Fintype τ] (fam : σ → MvPowerSeries τ B) (Bf : σ → Fin n → MvPowerSeries τ B)
    (hfam : ∀ s, MvPowerSeries.constantCoeff (fam s) = 0) (g : MvPowerSeries σ B) (Zg : Fin n → MvPowerSeries σ B) :
    MvPowerSeries.subst (fun s => fam s + ∑ i, j i • Bf s i) (g + ∑ i, j i • Zg i) =
      MvPowerSeries.subst fam g + ∑ i, j i • (∑ s, Bf s i * MvPowerSeries.subst fam (MvPowerSeries.pderivLin s g) + MvPowerSeries.subst fam (Zg i)) := by
  have hS := hasSubst_pert_fam j hj2 fam Bf hfam
  rw [← MvPowerSeries.coe_substAlgHom hS, map_add, map_sum]
  simp only [map_smul, MvPowerSeries.coe_substAlgHom]
  rw [MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv j hj2 g fam hfam Bf]
  simp only [MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv j hj2 _ fam hfam Bf, smul_add, Finset.smul_sum,
    smul_smul, hj2, zero_smul, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  abel

include hj2 hjm hZ in
theorem pert_assoc (hassoc : ∀ i l, sideL (G.map (residue B)) (z i) l = sideR (G.map (residue B)) (z i) l) (l : Fin d) :
    MvPowerSeries.subst (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (pert G j Z q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) (pert G j Z l) = MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (pert G j Z q))) (pert G j Z l) := by

  have hL : (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (pert G j Z q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) =
      fun s => (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) s + ∑ i, j i • (fun s i => Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (Z i q)) (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) s) s i := by
    funext s
    rcases s with q | q
    · show MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G.toPowerSeries q + ∑ i, j i • Z i q) = _
      rw [← MvPowerSeries.coe_substAlgHom hasSubst_XY, map_add, map_sum]
      simp only [map_smul, Sum.elim_inl]
    · simp only [Sum.elim_inr, smul_zero, Finset.sum_const_zero, add_zero]
  have hR : (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (pert G j Z q))) =
      fun s => (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G.toPowerSeries q))) s + ∑ i, j i • (fun s i => Sum.elim (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (Z i q)) s) s i := by
    funext s
    rcases s with q | q
    · simp only [Sum.elim_inl, smul_zero, Finset.sum_const_zero, add_zero]
    · show MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G.toPowerSeries q + ∑ i, j i • Z i q) = _
      rw [← MvPowerSeries.coe_substAlgHom hasSubst_YZ, map_add, map_sum]
      simp only [map_smul, Sum.elim_inr]
  rw [hL, hR, show pert G j Z l = G.toPowerSeries l + ∑ i, j i • Z i l from rfl,
    subst_pert_pert j hj2 _ _ (famL_cc G) _ _, subst_pert_pert j hj2 _ _ (famR_cc G) _ _, G.assoc l]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  apply smul_eq_of_map_eq j hjm i

  have eL : MvPowerSeries.map (residue B) (∑ s, Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (Z i q)) (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) s *
        MvPowerSeries.subst (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) (MvPowerSeries.pderivLin s (G.toPowerSeries l)) +
        MvPowerSeries.subst (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) (Z i l)) = sideL (G.map (residue B)) (z i) l := by
    rw [sideL, map_add, map_sum, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, map_zero, Finset.sum_const_zero, add_zero, map_mul]
    rw [add_comm]
    congr 1
    · rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (famL_cc G)), hZ]
      congr 1; funext s; exact map_famL (residue B) G s
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_subst_rename (residue B) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (IsLocalRing.ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (by rintro (a | a) <;> exact MvPowerSeries.map_X _ _)
        (by rintro (a | a) <;> exact MvPowerSeries.constantCoeff_X _), hZ,
        MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (famL_cc G)), ← pderiv_map]
      congr 2
      · funext s; exact map_famL (residue B) G s
  have eR : MvPowerSeries.map (residue B) (∑ s, Sum.elim (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (Z i q)) s *
        MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G.toPowerSeries q))) (MvPowerSeries.pderivLin s (G.toPowerSeries l)) +
        MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G.toPowerSeries q))) (Z i l)) = sideR (G.map (residue B)) (z i) l := by
    rw [sideR, map_add, map_sum, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, map_zero, Finset.sum_const_zero, zero_add, map_mul]
    rw [add_comm]
    congr 1
    · rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (famR_cc G)), hZ]
      congr 1; funext s; exact map_famR (residue B) G s
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_subst_rename (residue B) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (IsLocalRing.ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (by rintro (a | a) <;> exact MvPowerSeries.map_X _ _)
        (by rintro (a | a) <;> exact MvPowerSeries.constantCoeff_X _), hZ,
        MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (famR_cc G)), ← pderiv_map]
      congr 2
      · funext s; exact map_famR (residue B) G s
  rw [eL, eR, hassoc]

end PertAssoc

end GRAux

end

open MvPowerSeries MvFormalGroup IsLocalRing

open GRAux in
theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] :
    ∃ G' : Deformation (F.map (algebraMap B B₁)) B, G'.F.IsComm ∧ Deformation.IsShiftBy V ι F w G G' := by
  classical

  haveI hFk : (F.map (residue B)).IsComm := GRAux.isComm_map (residue B) F
  have hGF : G.F.map (residue B) = F.map (residue B) := by
    apply MvFormalGroup.ext
    funext l
    refine MvPowerSeries.ext fun m => ?_
    show MvPowerSeries.coeff m (MvPowerSeries.map (residue B) (G.F.toPowerSeries l)) =
      MvPowerSeries.coeff m (MvPowerSeries.map (residue B) (F.toPowerSeries l))
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply hI
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map]
    exact congrArg (fun H : MvFormalGroup d B₁ => MvPowerSeries.coeff m (H.toPowerSeries l)) G.map_eq

  let b := Module.finBasis (ResidueField B) V
  have hrep : ∀ i, ∃ zz : ↥(firstOrderCocycles (F.map (residue B))), Submodule.Quotient.mk zz = w (b.coord i) :=
    fun i => Submodule.Quotient.mk_surjective _ _
  choose zc hzc using hrep
  have hsurj : Function.Surjective (residue B) := Ideal.Quotient.mk_surjective
  let Zl : Fin (Module.finrank (ResidueField B) V) → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B :=
    fun i l m => Function.surjInv hsurj ((zc i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) l m)
  have hZl : ∀ i l, MvPowerSeries.map (residue B) (Zl i l) = (zc i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) l := by
    intro i l
    refine MvPowerSeries.ext fun m => ?_
    rw [MvPowerSeries.coeff_map]
    exact Function.surjInv_eq hsurj _

  have hjm : ∀ i, ∀ m ∈ maximalIdeal B, m * ι (b i) = 0 := by
    intro i m hm
    rw [← smul_eq_mul, ← LinearMap.map_smul, ← algebraMap_smul (ResidueField B) m (b i),
      show algebraMap B (ResidueField B) m = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hm, zero_smul, map_zero]
  have hjI : ∀ i, ι (b i) ∈ maximalIdeal B := by
    intro i
    apply hI
    have : ι (b i) ∈ LinearMap.range ι := LinearMap.mem_range_self ι (b i)
    rw [hιI] at this
    exact this
  have hj2 : ∀ i i', ι (b i) * ι (b i') = 0 := fun i i' => by rw [mul_comm]; exact hjm i _ (hjI i')

  have hz : ∀ i, _ := fun i => (MvFormalGroup.mem_firstOrderCocycles_iff (F.map (residue B))
    ((zc i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)))).mp (zc i).2

  have hassoc : ∀ i l, GRAux.sideL (G.F.map (residue B)) ((zc i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B))) l =
      GRAux.sideR (G.F.map (residue B)) ((zc i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B))) l := by
    rw [hGF]; exact fun i l => (hz i).2.2.2 l
  let G'law : MvFormalGroup d B :=
    { toPowerSeries := GRAux.pert G.F (fun i => ι (b i)) Zl
      constantCoeff_eq_zero := GRAux.pert_constantCoeff G.F _ hjm Zl _ hZl (fun i l => (hz i).1 l)
      coeff_single_inl := fun l q => GRAux.pert_coeff_single G.F _ hjm Zl _ hZl (Sum.inl q) _ l (G.F.coeff_single_inl l q)
        (fun i => ((hz i).2.1 l q).1)
      coeff_single_inr := fun l q => GRAux.pert_coeff_single G.F _ hjm Zl _ hZl (Sum.inr q) _ l (G.F.coeff_single_inr l q)
        (fun i => ((hz i).2.1 l q).2)
      assoc := fun l => GRAux.pert_assoc G.F _ hj2 hjm Zl _ hZl hassoc l }
  haveI hG'c : G'law.IsComm := ⟨fun l => GRAux.pert_comm G.F _ hjm Zl _ hZl (fun i l => (hz i).2.2.1 l) l⟩
  have hmap : G'law.map (algebraMap B B₁ : B →+* B₁) = F.map (algebraMap B B₁ : B →+* B₁) := by
    rw [← G.map_eq]
    apply MvFormalGroup.ext
    funext l
    show MvPowerSeries.map (algebraMap B B₁ : B →+* B₁) (G.F.toPowerSeries l + ∑ i, ι (b i) • Zl i l) =
      MvPowerSeries.map (algebraMap B B₁ : B →+* B₁) (G.F.toPowerSeries l)
    rw [map_add, map_sum, add_eq_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C]
    have : (algebraMap B B₁ : B →+* B₁) (ι (b i)) = 0 := by
      have h := LinearMap.mem_range_self ι (b i)
      rw [hιI] at h
      exact h
    rw [this, map_zero, zero_mul]
  refine ⟨⟨G'law, hmap⟩, hG'c, Module.finrank (ResidueField B) V, b, zc, Zl, hZl, fun ξ => ?_, fun l => rfl⟩
  conv_lhs => rw [← Module.Basis.sum_dual_apply_smul_coord b ξ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hzc]

end S_MvFormalGroup_Deformation_exists_isComm_isShiftBy
end P2MW
export P2MW.S_MvFormalGroup_Deformation_exists_isComm_isShiftBy (solution)
