-- Prove2me | solution 1 for MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d5f0bc30-3908-5bec-829f-fb77ea36cc59

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
import Theorems.Thm_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
import Theorems.Thm_MvFormalGroup_mem_firstOrderCoboundaries_iff
import Theorems.Thm_MvFormalGroup_exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero
import Theorems.Thm_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Deformation_isIso_of_isShiftBy_of_isShiftBy
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

noncomputable section

open MvPowerSeries MvFormalGroup IsLocalRing

namespace SWAux

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

end PertAssoc

section Bf
variable {k : Type} [CommRing k] {d : ℕ} (G₀ : MvFormalGroup d k)

def bf (η : Fin d → MvPowerSeries (Fin d) k) (l : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) k :=
  ∑ i, MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (η i) * MvPowerSeries.pderivLin (Sum.inl i) (G₀.toPowerSeries l)
    + ∑ i, MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (η i) * MvPowerSeries.pderivLin (Sum.inr i) (G₀.toPowerSeries l)
    - MvPowerSeries.subst G₀.toPowerSeries (η l)

theorem hasSubst_Xl : MvPowerSeries.HasSubst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
theorem hasSubst_Xr : MvPowerSeries.HasSubst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) k)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)

theorem bf_neg (η : Fin d → MvPowerSeries (Fin d) k) (l : Fin d) : bf G₀ (-η) l = -bf G₀ η l := by
  simp only [bf, Pi.neg_apply, ← MvPowerSeries.coe_substAlgHom (hasSubst_Xl (k := k) (d := d)), ← MvPowerSeries.coe_substAlgHom (hasSubst_Xr (k := k) (d := d)),
    ← MvPowerSeries.coe_substAlgHom G₀.hasSubst_toPowerSeries, map_neg, neg_mul, Finset.sum_neg_distrib]
  abel

end Bf

end SWAux

namespace SWAux
section Iso

variable {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
  (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
  (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
  [Module B V] [IsScalarTower B (ResidueField B) V]
  (ι : V →ₗ[B] B) (hι : Function.Injective ι)
  (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
  {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]

theorem map_bf {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) (G : MvFormalGroup d R) (η : Fin d → MvPowerSeries (Fin d) R) (l : Fin d) :
    MvPowerSeries.map π (bf G η l) = bf (G.map π) (fun q => MvPowerSeries.map π (η q)) l := by
  have hG : (G.map π).toPowerSeries = fun q => MvPowerSeries.map π (G.toPowerSeries q) := rfl
  rw [bf, bf, map_sub, map_add, map_sum, map_sum, hG, MvPowerSeries.map_subst G.hasSubst_toPowerSeries]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pderiv_map, map_subst_rename π (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) S)) (fun _ => MvPowerSeries.map_X _ _) (fun _ => MvPowerSeries.constantCoeff_X _)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pderiv_map, map_subst_rename π (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) S)) (fun _ => MvPowerSeries.map_X _ _) (fun _ => MvPowerSeries.constantCoeff_X _)]

end Iso
end SWAux

open MvFormalGroup IsLocalRing

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' G'' : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] [G'.F.IsComm] [G''.F.IsComm]
    (h' : Deformation.IsShiftBy V ι F w G G') (h'' : Deformation.IsShiftBy V ι F w G G'') :
    G'.IsIso G'' := by
  classical
  obtain ⟨n', v', z', zl', hz', hw', hG'⟩ := h'
  obtain ⟨n'', v'', z'', zl'', hz'', hw'', hG''⟩ := h''
  haveI hFk : (F.map (residue B)).IsComm := SWAux.isComm_map (residue B) F

  have hres : ∀ (E : Deformation (F.map (algebraMap B B₁)) B) (l : Fin d),
      MvPowerSeries.map (residue B) (E.F.toPowerSeries l) = (F.map (residue B)).toPowerSeries l := by
    intro E l
    refine MvPowerSeries.ext fun m => ?_
    show MvPowerSeries.coeff m (MvPowerSeries.map (residue B) (E.F.toPowerSeries l)) =
      MvPowerSeries.coeff m (MvPowerSeries.map (residue B) (F.toPowerSeries l))
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply hI
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map]
    exact congrArg (fun H : MvFormalGroup d B₁ => MvPowerSeries.coeff m (H.toPowerSeries l)) E.map_eq
  have hG'F : G'.F.map (residue B) = F.map (residue B) := MvFormalGroup.ext (funext fun l => hres G' l)

  let b := Module.finBasis (ResidueField B) V
  have hjm : ∀ i, ∀ m ∈ maximalIdeal B, m * ι (b i) = 0 := by
    intro i m hm
    rw [← smul_eq_mul, ← LinearMap.map_smul, ← algebraMap_smul (ResidueField B) m (b i),
      show algebraMap B (ResidueField B) m = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hm, zero_smul, map_zero]
  have hjker : ∀ i, (algebraMap B B₁) (ι (b i)) = 0 := fun i => by
    have h := LinearMap.mem_range_self ι (b i); rw [hιI] at h; exact h
  have hjI : ∀ i, ι (b i) ∈ maximalIdeal B := fun i => hI (hjker i)
  have hj2 : ∀ i i', ι (b i) * ι (b i') = 0 := fun i i' => by rw [mul_comm]; exact hjm i _ (hjI i')
  have hsurj : Function.Surjective (residue B) := Ideal.Quotient.mk_surjective

  let cl : V → Fin (Module.finrank (ResidueField B) V) → B := fun v i => Function.surjInv hsurj (b.repr v i)
  have hcl : ∀ v i, residue B (cl v i) = b.repr v i := fun v i => Function.surjInv_eq hsurj _
  have hιv : ∀ v, ι v = ∑ i, cl v i * ι (b i) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hcl v i, show (residue B (cl v i)) • b i = cl v i • b i from algebraMap_smul (ResidueField B) (cl v i) (b i),
      LinearMap.map_smul, smul_eq_mul]

  let dl : Fin (Module.finrank (ResidueField B) V) → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B :=
    fun i l => ∑ j, cl (v'' j) i • zl'' j l - ∑ j, cl (v' j) i • zl' j l
  have hsumι : ∀ {n : ℕ} (v : Fin n → V) (zl : Fin n → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (l : Fin d),
      ∑ j, ι (v j) • zl j l = ∑ i, ι (b i) • ∑ j, cl (v j) i • zl j l := by
    intro n v zl l
    have step : ∀ j, ι (v j) • zl j l = ∑ i, ι (b i) • (cl (v j) i • zl j l) := fun j => by
      rw [hιv (v j), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul]
    rw [Finset.sum_congr rfl (fun j _ => step j), Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
  have hGG : ∀ l, G''.F.toPowerSeries l = G'.F.toPowerSeries l + ∑ i, ι (b i) • dl i l := by
    intro l
    rw [hG'' l, hG' l, hsumι v'' zl'' l, hsumι v' zl' l, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_add]
    congr 1
    show _ = ∑ j, cl (v' j) i • zl' j l + (∑ j, cl (v'' j) i • zl'' j l - ∑ j, cl (v' j) i • zl' j l)
    abel

  let dZ : Fin (Module.finrank (ResidueField B) V) → ↥(firstOrderCocycles (F.map (residue B))) :=
    fun i => ∑ j, b.repr (v'' j) i • z'' j - ∑ j, b.repr (v' j) i • z' j
  have hdres : ∀ i l, MvPowerSeries.map (residue B) (dl i l) = (dZ i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) l := by
    intro i l
    show MvPowerSeries.map (residue B) (∑ j, cl (v'' j) i • zl'' j l - ∑ j, cl (v' j) i • zl' j l) = _
    simp only [dZ, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      map_sub, map_sum, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, hcl, hz', hz'']
  have hclass : ∀ i, Submodule.Quotient.mk (p := (firstOrderCoboundaries (F.map (residue B))).comap (firstOrderCocycles (F.map (residue B))).subtype) (dZ i) = 0 := by
    intro i
    have e1 := hw' (b.coord i)
    have e2 := hw'' (b.coord i)
    simp only [Module.Basis.coord_apply] at e1 e2
    show ((firstOrderCoboundaries (F.map (residue B))).comap (firstOrderCocycles (F.map (residue B))).subtype).mkQ (dZ i) = 0
    simp only [dZ, map_sub, map_sum, map_smul, Submodule.mkQ_apply]
    rw [← e1, ← e2, sub_self]
  have hdB : ∀ i, (dZ i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) ∈ firstOrderCoboundaries (F.map (residue B)) := fun i =>
    Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp (hclass i))

  have hK4 := fun i => (MvFormalGroup.mem_firstOrderCoboundaries_iff (F.map (residue B)) _).mp (hdB i)
  choose η hη0 hηd using hK4

  let ηl0 : Fin (Module.finrank (ResidueField B) V) → Fin d → MvPowerSeries (Fin d) B := fun i q m => Function.surjInv hsurj (η i q m)
  let ηl : Fin (Module.finrank (ResidueField B) V) → Fin d → MvPowerSeries (Fin d) B :=
    fun i q => ηl0 i q - MvPowerSeries.C (MvPowerSeries.constantCoeff (ηl0 i q))
  have hηl0 : ∀ i q, MvPowerSeries.map (residue B) (ηl0 i q) = η i q := fun i q =>
    MvPowerSeries.ext fun m => by rw [MvPowerSeries.coeff_map]; exact Function.surjInv_eq hsurj _
  have hηlcc : ∀ i q, MvPowerSeries.constantCoeff (ηl i q) = 0 := fun i q => by
    show MvPowerSeries.constantCoeff (ηl0 i q - MvPowerSeries.C (MvPowerSeries.constantCoeff (ηl0 i q))) = 0
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have hηl : ∀ i q, MvPowerSeries.map (residue B) (ηl i q) = η i q := fun i q => by
    show MvPowerSeries.map (residue B) (ηl0 i q - MvPowerSeries.C (MvPowerSeries.constantCoeff (ηl0 i q))) = η i q
    rw [map_sub, hηl0, MvPowerSeries.map_C, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_map, hηl0,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hη0, map_zero, sub_zero]

  obtain ⟨F', Φ, Ψ, hΦ, hΨ, h1, h2, -, hform⟩ :=
    MvFormalGroup.exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero (fun i => ι (b i)) hj2 ηl hηlcc G'.F
  have hF' : F' = G''.F := by
    apply MvFormalGroup.ext
    funext l
    rw [hform l, hGG l]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    apply SWAux.smul_eq_of_map_eq (fun i => ι (b i)) hjm i
    rw [show (∑ q, MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (ηl i q) * MvPowerSeries.pderivLin (Sum.inl q) (G'.F.toPowerSeries l)
          + ∑ q, MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (ηl i q) * MvPowerSeries.pderivLin (Sum.inr q) (G'.F.toPowerSeries l)
          - MvPowerSeries.subst G'.F.toPowerSeries (ηl i l)) = SWAux.bf G'.F (ηl i) l from rfl,
      SWAux.map_bf, hG'F, hdres]
    have : (fun q => MvPowerSeries.map (residue B) (ηl i q)) = η i := funext (hηl i)
    rw [this]
    exact (hηd i l).symm
  subst hF'
  refine ⟨Φ, ⟨Ψ, h1, h2⟩, fun i => ?_⟩
  rw [hΦ i, map_sub, MvPowerSeries.map_X, map_sum, sub_eq_self]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, hjker, map_zero, zero_mul]

end

end S_MvFormalGroup_Deformation_isIso_of_isShiftBy_of_isShiftBy
end P2MW
export P2MW.S_MvFormalGroup_Deformation_isIso_of_isShiftBy_of_isShiftBy (solution)
