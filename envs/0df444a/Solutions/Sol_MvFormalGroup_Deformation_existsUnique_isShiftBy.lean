-- Prove2me | solution 1 for MvFormalGroup.Deformation.existsUnique_isShiftBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ac812fa6-2c48-5fee-b0e9-bfbd604a69af

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy
import Theorems.Thm_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range
import Theorems.Thm_MvFormalGroup_mem_firstOrderCocycles_iff
import Theorems.Thm_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
import Theorems.Thm_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Deformation_existsUnique_isShiftBy

set_option autoImplicit false

open IsLocalRing MvFormalGroup

noncomputable section GTPsec
open MvPowerSeries MvFormalGroup IsLocalRing
namespace GTP

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

private theorem _root_.GTP.isComm_map [G.IsComm] : (G.map π).IsComm := by
  constructor
  intro i
  show MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) S)) fun q => MvPowerSeries.X (Sum.inl q)) (MvPowerSeries.map π (G.toPowerSeries i)) = MvPowerSeries.map π (G.toPowerSeries i)
  rw [← map_subst_rename π (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) R)) fun q => MvPowerSeries.X (Sum.inl q)) (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) S)) fun q => MvPowerSeries.X (Sum.inl q)) (by rintro (l | l) <;> exact MvPowerSeries.map_X _ _)
    (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _), MvFormalGroup.IsComm.comm]

p2m_export "GTP" "isComm_map"
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

theorem famL_pert :
    (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (pert G j Z q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) =
      fun s => (Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G.toPowerSeries q)) (fun q => (MvPowerSeries.X (Sum.inr (Sum.inr q)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) s + ∑ i, j i • (fun s i => Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (Z i q)) (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) s) s i := by
  funext s
  rcases s with q | q
  · show MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (G.toPowerSeries q + ∑ i, j i • Z i q) = _
    rw [← MvPowerSeries.coe_substAlgHom hasSubst_XY, map_add, map_sum]
    simp only [map_smul, Sum.elim_inl, MvPowerSeries.coe_substAlgHom]
  · simp only [Sum.elim_inr, smul_zero, Finset.sum_const_zero, add_zero]

theorem famR_pert :
    (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (pert G j Z q))) =
      fun s => (Sum.elim (fun q => (MvPowerSeries.X (Sum.inl q) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G.toPowerSeries q))) s + ∑ i, j i • (fun s i => Sum.elim (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (Z i q)) s) s i := by
  funext s
  rcases s with q | q
  · simp only [Sum.elim_inl, smul_zero, Finset.sum_const_zero, add_zero]
  · show MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (G.toPowerSeries q + ∑ i, j i • Z i q) = _
    rw [← MvPowerSeries.coe_substAlgHom hasSubst_YZ, map_add, map_sum]
    simp only [map_smul, Sum.elim_inr, MvPowerSeries.coe_substAlgHom]

include hZ in
theorem residue_TL (i : Fin n) (l : Fin d) :
    MvPowerSeries.map (residue B) (∑ s, Sum.elim (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (Z i q)) (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) s *
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

include hZ in
theorem residue_TR (i : Fin n) (l : Fin d) :
    MvPowerSeries.map (residue B) (∑ s, Sum.elim (fun _ => (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun q => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (Z i q)) s *
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

end PertAssoc

end GTP

end GTPsec

theorem GTransAux.isComm_map {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') {d : ℕ} (F : MvFormalGroup d B) [hF : F.IsComm] :
    (F.map φ).IsComm := by
  constructor
  intro i
  have key := congrArg (MvPowerSeries.map φ) (hF.comm i)
  have hS : MvPowerSeries.HasSubst (Sum.elim
      (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) B))
      fun j => MvPowerSeries.X (Sum.inl j)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    rintro (j | j) <;> exact MvPowerSeries.constantCoeff_X _
  rw [MvPowerSeries.map_subst hS] at key
  have hfam : (fun s => MvPowerSeries.map φ (Sum.elim
      (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) B))
      (fun j => MvPowerSeries.X (Sum.inl j)) s))
      = Sum.elim
        (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) B'))
        fun j => MvPowerSeries.X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
  rw [hfam] at key
  exact key

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (G G' : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] [G'.F.IsComm] :
    ∃! w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)),
      Deformation.IsShiftBy V ι F w G G' := by
  classical
  haveI : (F.map (residue B)).IsComm := GTransAux.isComm_map (residue B) F

  set k := ResidueField B with hk
  have hres : ∀ b : B, algebraMap B (ResidueField B) b = residue B b := fun b => rfl

  let r : ℕ := Module.finrank (ResidueField B) V
  let bV : Module.Basis (Fin r) (ResidueField B) V := Module.finBasis (ResidueField B) V

  have hΔ : ∀ (l : Fin d) (n : (Fin d ⊕ Fin d) →₀ ℕ),
      MvPowerSeries.coeff n (G'.F.toPowerSeries l - G.F.toPowerSeries l) ∈ LinearMap.range ι := by
    intro l n
    have h1 := congrArg (fun H : MvFormalGroup d B₁ => MvPowerSeries.coeff n (H.toPowerSeries l)) G.map_eq
    have h2 := congrArg (fun H : MvFormalGroup d B₁ => MvPowerSeries.coeff n (H.toPowerSeries l)) G'.map_eq
    simp only [MvFormalGroup.map, MvPowerSeries.coeff_map] at h1 h2
    have hker : MvPowerSeries.coeff n (G'.F.toPowerSeries l) - MvPowerSeries.coeff n (G.F.toPowerSeries l)
        ∈ RingHom.ker (algebraMap B B₁) := by
      rw [RingHom.mem_ker, map_sub, h1, h2, sub_self]
    have : MvPowerSeries.coeff n (G'.F.toPowerSeries l) - MvPowerSeries.coeff n (G.F.toPowerSeries l)
        ∈ Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)) := hker
    rw [← hιI] at this
    simpa [map_sub] using this

  have hJ := fun l => IsLocalRing.existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range V ι hι bV
      (G'.F.toPowerSeries l - G.F.toPowerSeries l) (hΔ l)
  have hex : ∀ l, ∃ z : Fin r → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B),
      ∀ zl : Fin r → MvPowerSeries (Fin d ⊕ Fin d) B, (∀ i, MvPowerSeries.map (residue B) (zl i) = z i) →
        G'.F.toPowerSeries l - G.F.toPowerSeries l = ∑ i, ι (bV i) • zl i := fun l => (hJ l).1.exists
  choose zc hzc using hex
  have hlift : ∀ l, ∃ zl : Fin r → MvPowerSeries (Fin d ⊕ Fin d) B, ∀ i, MvPowerSeries.map (residue B) (zl i) = zc l i :=
    fun l => (hJ l).2 (zc l)
  choose zlc hzlc using hlift

  let z : Fin r → Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B) := fun i l => zc l i
  let zl : Fin r → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B := fun i l => zlc l i
  have hzl : ∀ i l, MvPowerSeries.map (residue B) (zl i l) = z i l := fun i l => hzlc l i
  have hG' : ∀ l, G'.F.toPowerSeries l = G.F.toPowerSeries l + ∑ i, ι (bV i) • zl i l := by
    intro l
    have := hzc l (zlc l) (hzlc l)
    rw [sub_eq_iff_eq_add'] at this
    simpa [zl] using this

  have hann0 : ∀ (v : V) (m : B), m ∈ maximalIdeal B → m * ι v = 0 := by
    intro v m hm
    have h1 : m * ι v = ι (m • v) := by rw [LinearMap.map_smul, smul_eq_mul]
    have h2 : m • v = (algebraMap B (ResidueField B) m) • v := (algebraMap_smul (ResidueField B) m v).symm
    have h3 : algebraMap B (ResidueField B) m = 0 := by
      rw [hres]; exact (IsLocalRing.residue_eq_zero_iff m).mpr hm
    rw [h1, h2, h3, zero_smul, LinearMap.map_zero]
  have hindep0 : ∀ c : Fin r → B, ∑ i, ι (bV i) * c i = 0 → ∀ i, residue B (c i) = 0 := by
    intro c hc i
    have hterm : ∀ i, ι (bV i) * c i = ι ((residue B (c i)) • bV i) := by
      intro i
      rw [← hres, algebraMap_smul, LinearMap.map_smul, smul_eq_mul, mul_comm]
    have hsum : ι (∑ i, (residue B (c i)) • bV i) = 0 := by
      rw [map_sum, ← hc]
      exact Finset.sum_congr rfl fun i _ => (hterm i).symm
    have hzero : ∑ i, (residue B (c i)) • bV i = 0 := hι (by rw [hsum, LinearMap.map_zero])
    have := bV.linearIndependent
    rw [Fintype.linearIndependent_iff] at this
    exact this (fun i => residue B (c i)) hzero i
  have hindep : ∀ {τ : Type} (E : Fin r → MvPowerSeries τ B), ∑ i, ι (bV i) • E i = 0 →
      ∀ i, MvPowerSeries.map (residue B) (E i) = 0 := by
    intro τ E hE i
    refine MvPowerSeries.ext fun nn => ?_
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_zero]
    have := congrArg (MvPowerSeries.coeff nn) hE
    simp only [map_sum, map_smul, smul_eq_mul, MvPowerSeries.coeff_zero] at this
    exact hindep0 (fun i => MvPowerSeries.coeff nn (E i)) this i

  have h0 : ∀ i l, MvPowerSeries.constantCoeff (z i l) = 0 := by
    intro i l
    have hE : ∑ i, ι (bV i) * MvPowerSeries.constantCoeff (zl i l) = 0 := by
      have h' := G'.F.constantCoeff_eq_zero l
      rw [hG' l, map_add, G.F.constantCoeff_eq_zero, zero_add, map_sum] at h'
      simpa only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul, smul_eq_mul] using h'
    have := hindep0 _ hE i
    rw [← hzl i l, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, this]
  have h1 : ∀ i l q, MvPowerSeries.coeff (Finsupp.single (Sum.inl q) 1) (z i l) = 0 ∧
      MvPowerSeries.coeff (Finsupp.single (Sum.inr q) 1) (z i l) = 0 := by
    intro i l q
    have key : ∀ s : Fin d ⊕ Fin d,
        (MvPowerSeries.coeff (Finsupp.single s 1) (G'.F.toPowerSeries l) = MvPowerSeries.coeff (Finsupp.single s 1) (G.F.toPowerSeries l)) →
        MvPowerSeries.coeff (Finsupp.single s 1) (z i l) = 0 := by
      intro s hs
      have hE : ∑ i, ι (bV i) * MvPowerSeries.coeff (Finsupp.single s 1) (zl i l) = 0 := by
        rw [hG' l, map_add, map_sum] at hs
        simp only [map_smul, smul_eq_mul] at hs
        linear_combination hs
      have := hindep0 _ hE i
      rw [← hzl i l, MvPowerSeries.coeff_map, this]
    refine ⟨key (Sum.inl q) ?_, key (Sum.inr q) ?_⟩
    · rw [G'.F.coeff_single_inl, G.F.coeff_single_inl]
    · rw [G'.F.coeff_single_inr, G.F.coeff_single_inr]
  have hsw : ∀ i l, MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)))
      fun q => MvPowerSeries.X (Sum.inl q)) (z i l) = z i l := by
    intro i l
    have hc' := MvFormalGroup.IsComm.comm (F := G'.F) l
    rw [hG' l, ← MvPowerSeries.coe_substAlgHom GTP.hasSubst_SW, map_add, map_sum] at hc'
    simp only [map_smul, MvPowerSeries.coe_substAlgHom] at hc'
    rw [MvFormalGroup.IsComm.comm (F := G.F) l] at hc'
    have hE : ∑ i, ι (bV i) • (MvPowerSeries.subst (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) B)) fun q => MvPowerSeries.X (Sum.inl q)) (zl i l) - zl i l) = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => smul_sub _ _ _), Finset.sum_sub_distrib, sub_eq_zero]
      exact add_left_cancel hc'
    have h := hindep _ hE i
    rw [map_sub, sub_eq_zero, GTP.map_subst_rename (residue B) (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) B)) fun q => MvPowerSeries.X (Sum.inl q)) (Sum.elim (fun q => (MvPowerSeries.X (Sum.inr q) : MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))) fun q => MvPowerSeries.X (Sum.inl q)) (by rintro (q | q) <;> exact MvPowerSeries.map_X _ _)
      (by rintro (q | q) <;> exact MvPowerSeries.constantCoeff_X _), hzl] at h
    exact h

  have hassoc : ∀ i, ∀ l, MvPowerSeries.subst (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) ((F.map (residue B)).toPowerSeries j)) (fun j => (MvPowerSeries.X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B)))) (z i l) + ∑ i', MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) (z i i') * MvPowerSeries.subst (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))) ((F.map (residue B)).toPowerSeries j)) (fun j => (MvPowerSeries.X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B)))) (MvPowerSeries.pderivLin (Sum.inl i') ((F.map (residue B)).toPowerSeries l))
            = MvPowerSeries.subst (Sum.elim (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) ((F.map (residue B)).toPowerSeries j))) (z i l) + ∑ i', MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) (z i i') * MvPowerSeries.subst (Sum.elim (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (ResidueField B))) (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))) ((F.map (residue B)).toPowerSeries j))) (MvPowerSeries.pderivLin (Sum.inr i') ((F.map (residue B)).toPowerSeries l)) := by
    intro i l
    have hjm : ∀ i, ∀ m ∈ maximalIdeal B, m * ι (bV i) = 0 := fun i m hm => hann0 (bV i) m hm
    have hjI : ∀ i, ι (bV i) ∈ maximalIdeal B := fun i => hI (by
      have h := LinearMap.mem_range_self ι (bV i); rw [hιI] at h; exact h)
    have hj2 : ∀ i i', ι (bV i) * ι (bV i') = 0 := fun i i' => by rw [mul_comm]; exact hjm i _ (hjI i')
    have hGF : G.F.map (residue B) = F.map (residue B) := by
      apply MvFormalGroup.ext
      funext l'
      refine MvPowerSeries.ext fun m => ?_
      show MvPowerSeries.coeff m (MvPowerSeries.map (residue B) (G.F.toPowerSeries l')) =
        MvPowerSeries.coeff m (MvPowerSeries.map (residue B) (F.toPowerSeries l'))
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      apply hI
      rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map]
      exact congrArg (fun H : MvFormalGroup d B₁ => MvPowerSeries.coeff m (H.toPowerSeries l')) G.map_eq
    have hGf : G'.F.toPowerSeries = GTP.pert G.F (fun i => ι (bV i)) zl := funext fun l => hG' l
    have ha' := G'.F.assoc l
    simp only [hGf] at ha'
    rw [GTP.famL_pert G.F (fun i => ι (bV i)) zl, GTP.famR_pert G.F (fun i => ι (bV i)) zl,
      show GTP.pert G.F (fun i => ι (bV i)) zl l = G.F.toPowerSeries l + ∑ i, ι (bV i) • zl i l from rfl,
      GTP.subst_pert_pert _ hj2 _ _ (GTP.famL_cc G.F) _ _, GTP.subst_pert_pert _ hj2 _ _ (GTP.famR_cc G.F) _ _, G.F.assoc l] at ha'
    have hE := sub_eq_zero.mpr (add_left_cancel ha')
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => (smul_sub _ _ _).symm)] at hE
    have h := hindep _ hE i
    rw [map_sub, sub_eq_zero, GTP.residue_TL G.F zl z hzl i l, GTP.residue_TR G.F zl z hzl i l, hGF] at h
    exact h
  have hz : ∀ i, z i ∈ firstOrderCocycles (F.map (residue B)) := by
    intro i
    exact (MvFormalGroup.mem_firstOrderCocycles_iff (F.map (residue B)) (z i)).mpr ⟨h0 i, h1 i, hsw i, hassoc i⟩

  let zZ : Fin r → ↥(firstOrderCocycles (F.map (residue B))) := fun i => ⟨z i, hz i⟩
  let w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)) :=
    ∑ i, (Module.Dual.eval (ResidueField B) V (bV i)).smulRight (Submodule.Quotient.mk (zZ i))
  have hw : ∀ ξ : Module.Dual (ResidueField B) V, w ξ = ∑ i, ξ (bV i) • Submodule.Quotient.mk (zZ i) := by
    intro ξ
    simp [w, LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Dual.eval_apply]
  refine ⟨w, ⟨r, (fun i => bV i), zZ, zl, ?_, hw, hG'⟩, ?_⟩
  · intro i l; exact hzl i l
  ·
    intro w' hw'
    obtain ⟨n', v', z', zl', hzl', hw'ξ, hG''⟩ := hw'

    have hann : ∀ (v : V) (m : B), m ∈ maximalIdeal B → m * ι v = 0 := by
      intro v m hm
      have h1 : m * ι v = ι (m • v) := by rw [LinearMap.map_smul, smul_eq_mul]
      have h2 : m • v = (algebraMap B (ResidueField B) m) • v := (algebraMap_smul (ResidueField B) m v).symm
      have h3 : algebraMap B (ResidueField B) m = 0 := by
        rw [hres]; exact (IsLocalRing.residue_eq_zero_iff m).mpr hm
      rw [h1, h2, h3, zero_smul, LinearMap.map_zero]

    let c : Fin n' → Fin r → ResidueField B := fun j i => bV.repr (v' j) i
    have hc : ∀ j, v' j = ∑ i, c j i • bV i := fun j => (bV.sum_repr (v' j)).symm
    have hsurj : Function.Surjective (residue B) := Ideal.Quotient.mk_surjective
    choose ch hch using fun j i => hsurj (c j i)
    have hιv' : ∀ j, ι (v' j) = ∑ i, ch j i * ι (bV i) := by
      intro j
      rw [hc j, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : c j i • bV i = ch j i • bV i := by
        rw [← hch j i, ← hres, algebraMap_smul]
      rw [this, LinearMap.map_smul, smul_eq_mul]

    have hΔ' : ∀ l, G'.F.toPowerSeries l - G.F.toPowerSeries l = ∑ i, ι (bV i) • ∑ j, ch j i • zl' j l := by
      intro l
      rw [hG'' l, add_sub_cancel_left]
      simp_rw [hιv', Finset.sum_smul, Finset.smul_sum, mul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _

    have hzz' : ∀ l i, z i l = ∑ j, c j i • ((z' j : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) l) := by
      intro l
      have huniq := (hJ l).1.unique (hzc l) (y₂ := fun i => ∑ j, c j i • ((z' j : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) l)) ?_
      · intro i; exact congrFun huniq i
      · intro zl'' hzl''
        rw [hΔ' l]
        refine Finset.sum_congr rfl fun i _ => ?_
        apply MvPowerSeries.smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero (maximalIdeal B) (ι (bV i))
          (fun m hm => hann (bV i) m hm)
        intro nn
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
        have e1 := congrArg (MvPowerSeries.coeff nn) (hzl'' i)
        rw [MvPowerSeries.coeff_map] at e1
        rw [e1]
        simp only [map_sum, map_smul, smul_eq_mul, map_mul, hch]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e2 := congrArg (MvPowerSeries.coeff nn) (hzl' j l)
        rw [MvPowerSeries.coeff_map] at e2
        rw [e2]

    have hzZ : ∀ i, zZ i = ∑ j, c j i • z' j := by
      intro i
      apply Subtype.ext
      funext l
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [Submodule.coe_smul, Pi.smul_apply]
      exact hzz' l i
    apply LinearMap.ext
    intro ξ
    rw [hw'ξ ξ, hw ξ]
    have hξ : ∀ j, ξ (v' j) = ∑ i, c j i * ξ (bV i) := by
      intro j; rw [hc j, map_sum]; simp [map_smul, smul_eq_mul]
    simp_rw [hξ, hzZ]
    have hmk : ∀ i, (Submodule.Quotient.mk (∑ j, c j i • z' j) :
        firstOrderDeformationSpace (F.map (residue B))) = ∑ j, c j i • Submodule.Quotient.mk (z' j) := by
      intro i
      rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
    simp_rw [hmk, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]

end S_MvFormalGroup_Deformation_existsUnique_isShiftBy
end P2MW
export P2MW.S_MvFormalGroup_Deformation_existsUnique_isShiftBy (solution)
