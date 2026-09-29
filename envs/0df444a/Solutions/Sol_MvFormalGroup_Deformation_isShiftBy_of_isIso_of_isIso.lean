-- Prove2me | solution 1 for MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/de2e3a0d-61f8-5a69-acbb-120a4bf3edf5

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
import Theorems.Thm_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
import Theorems.Thm_MvFormalGroup_mem_firstOrderCoboundaries_iff
import Theorems.Thm_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add
import Theorems.Thm_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Deformation_isShiftBy_of_isIso_of_isIso
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

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
section Core

variable {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
  (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
  (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
  [Module B V] [IsScalarTower B (ResidueField B) V]
  (ι : V →ₗ[B] B) (hι : Function.Injective ι)
  (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
  {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]

include hI hι hιI in

theorem core (D D' : Deformation (F.map (algebraMap B B₁)) B) (φ : D.F.Hom D'.F)
    (hφ : ∀ i, MvPowerSeries.map (algebraMap B B₁) (φ.toPowerSeries i) = MvPowerSeries.X i) :
    Deformation.IsShiftBy V ι F 0 D D' ∧ Deformation.IsShiftBy V ι F 0 D' D := by
  classical

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
  haveI hFk : (F.map (residue B)).IsComm := isComm_map (residue B) F

  let b := Module.finBasis (ResidueField B) V
  have hjm : ∀ i, ∀ m ∈ maximalIdeal B, m * ι (b i) = 0 := by
    intro i m hm
    rw [← smul_eq_mul, ← LinearMap.map_smul, ← algebraMap_smul (ResidueField B) m (b i),
      show algebraMap B (ResidueField B) m = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hm, zero_smul, map_zero]
  have hjI : ∀ i, ι (b i) ∈ maximalIdeal B := fun i => hI (by
    have h := LinearMap.mem_range_self ι (b i); rw [hιI] at h; exact h)
  have hj2 : ∀ i i', ι (b i) * ι (b i') = 0 := fun i i' => by rw [mul_comm]; exact hjm i _ (hjI i')

  have hΔ : ∀ q n, MvPowerSeries.coeff n (φ.toPowerSeries q - MvPowerSeries.X q) ∈ LinearMap.range ι := by
    intro q n
    rw [hιI]
    show MvPowerSeries.coeff n (φ.toPowerSeries q - MvPowerSeries.X q) ∈ RingHom.ker (algebraMap B B₁)
    rw [RingHom.mem_ker, ← MvPowerSeries.coeff_map, map_sub, hφ, MvPowerSeries.map_X, sub_self, map_zero]
  have hJ := fun q => IsLocalRing.existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range V ι hι b _ (hΔ q)
  choose ηbar hηbar using fun q => (hJ q).1.exists
  choose ηl hηl using fun q => (hJ q).2 (ηbar q)
  have hφq : ∀ q, φ.toPowerSeries q = MvPowerSeries.X q + ∑ i, ι (b i) • ηl q i := fun q =>
    eq_add_of_sub_eq' (hηbar q (ηl q) (hηl q))
  let θl : Fin (Module.finrank (ResidueField B) V) → Fin d → MvPowerSeries (Fin d) B :=
    fun i q => ηl q i - MvPowerSeries.C (MvPowerSeries.constantCoeff (ηl q i))
  have hθcc : ∀ i q, MvPowerSeries.constantCoeff (θl i q) = 0 := fun i q => by
    show MvPowerSeries.constantCoeff (ηl q i - MvPowerSeries.C (MvPowerSeries.constantCoeff (ηl q i))) = 0
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have hφθ : ∀ q, φ.toPowerSeries q = MvPowerSeries.X q + ∑ i, ι (b i) • θl i q := by
    intro q
    have h0 : ∑ i, ι (b i) * MvPowerSeries.constantCoeff (ηl q i) = 0 := by
      have := congrArg MvPowerSeries.constantCoeff (hφq q)
      rw [φ.constantCoeff_eq_zero, map_add, MvPowerSeries.constantCoeff_X, zero_add, map_sum] at this
      simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul] at this ⊢
      exact this.symm
    rw [hφq q]
    congr 1
    show ∑ i, ι (b i) • ηl q i = ∑ i, ι (b i) • (ηl q i - MvPowerSeries.C (MvPowerSeries.constantCoeff (ηl q i)))
    simp only [smul_sub, Finset.sum_sub_distrib, MvPowerSeries.smul_eq_C_mul (MvPowerSeries.C _), ← map_mul, ← map_sum, h0, map_zero, sub_zero]

  let Θ : (Fin d ⊕ Fin d) → Fin (Module.finrank (ResidueField B) V) → MvPowerSeries (Fin d ⊕ Fin d) B :=
    fun s i => Sum.elim (fun q => MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (θl i q)) (fun q => MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (θl i q)) s
  let T : Fin (Module.finrank (ResidueField B) V) → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B :=
    fun i l => MvPowerSeries.subst D.F.toPowerSeries (θl i l) - ∑ s, Θ s i * MvPowerSeries.pderivLin s (D'.F.toPowerSeries l)
  have hD' : ∀ l, D'.F.toPowerSeries l = D.F.toPowerSeries l + ∑ i, ι (b i) • T i l := by
    intro l
    have heq := φ.subst_eq l

    rw [hφθ l, ← MvPowerSeries.coe_substAlgHom D.F.hasSubst_toPowerSeries, map_add, map_sum] at heq
    simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X D.F.hasSubst_toPowerSeries] at heq

    have hfam : (Sum.elim (fun q => MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (φ.toPowerSeries q)) (fun q => MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (φ.toPowerSeries q)) :
          (Fin d ⊕ Fin d) → MvPowerSeries (Fin d ⊕ Fin d) B) = fun s => (MvPowerSeries.X s : MvPowerSeries (Fin d ⊕ Fin d) B) + ∑ i, ι (b i) • Θ s i := by
      funext s
      rcases s with q | q
      · show MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (φ.toPowerSeries q) = _
        rw [hφθ q, ← MvPowerSeries.coe_substAlgHom hasSubst_Xl, map_add, map_sum]
        simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hasSubst_Xl]
        rfl
      · show MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (φ.toPowerSeries q) = _
        rw [hφθ q, ← MvPowerSeries.coe_substAlgHom hasSubst_Xr, map_add, map_sum]
        simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hasSubst_Xr]
        rfl
    rw [hfam, MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv _ hj2 _ _ (fun _ => MvPowerSeries.constantCoeff_X _)] at heq
    have hX : (fun s : (Fin d ⊕ Fin d) => (MvPowerSeries.X s : MvPowerSeries (Fin d ⊕ Fin d) B)) = MvPowerSeries.X := rfl
    simp only [hX, MvPowerSeries.subst_self, id_eq] at heq

    have : ∑ i, ι (b i) • T i l = ∑ i, ι (b i) • MvPowerSeries.subst D.F.toPowerSeries (θl i l)
        - ∑ i, ι (b i) • ∑ s, Θ s i * MvPowerSeries.pderivLin s (D'.F.toPowerSeries l) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => smul_sub _ _ _
    rw [this, add_sub, heq, add_sub_cancel_right]

  have hTres : ∀ i l, MvPowerSeries.map (residue B) (T i l) =
      -bf (F.map (residue B)) (fun q => MvPowerSeries.map (residue B) (θl i q)) l := by
    intro i l
    have hT1 : MvPowerSeries.map (residue B) (T i l) =
        MvPowerSeries.subst (F.map (residue B)).toPowerSeries (MvPowerSeries.map (residue B) (θl i l)) -
          (∑ q, MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))) (MvPowerSeries.map (residue B) (θl i q)) * MvPowerSeries.pderivLin (Sum.inl q) ((F.map (residue B)).toPowerSeries l)
           + ∑ q, MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))) (MvPowerSeries.map (residue B) (θl i q)) * MvPowerSeries.pderivLin (Sum.inr q) ((F.map (residue B)).toPowerSeries l)) := by
      show MvPowerSeries.map (residue B) (MvPowerSeries.subst D.F.toPowerSeries (θl i l) - ∑ s, Θ s i * MvPowerSeries.pderivLin s (D'.F.toPowerSeries l)) = _
      rw [map_sub, map_sum, Fintype.sum_sum_type]
      congr 1
      · rw [MvPowerSeries.map_subst D.F.hasSubst_toPowerSeries]
        congr 1
        funext q; exact hres D q
      · congr 1
        · refine Finset.sum_congr rfl fun q _ => ?_
          show MvPowerSeries.map (residue B) (MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (θl i q) * MvPowerSeries.pderivLin (Sum.inl q) (D'.F.toPowerSeries l)) = _
          rw [map_mul, map_subst_rename (residue B) (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))) (fun _ => MvPowerSeries.map_X _ _) (fun _ => MvPowerSeries.constantCoeff_X _),
            ← pderiv_map, hres D']
        · refine Finset.sum_congr rfl fun q _ => ?_
          show MvPowerSeries.map (residue B) (MvPowerSeries.subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (θl i q) * MvPowerSeries.pderivLin (Sum.inr q) (D'.F.toPowerSeries l)) = _
          rw [map_mul, map_subst_rename (residue B) (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) B)) (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField B))) (fun _ => MvPowerSeries.map_X _ _) (fun _ => MvPowerSeries.constantCoeff_X _),
            ← pderiv_map, hres D']
    rw [hT1, bf]
    abel

  have hBZ : firstOrderCoboundaries (F.map (residue B)) ≤ firstOrderCocycles (F.map (residue B)) :=
    Submodule.span_mono (Set.image_mono fun D hD => hD.1)
  have hmemB : ∀ (θ : Fin d → MvPowerSeries (Fin d) (ResidueField B)), (∀ q, MvPowerSeries.constantCoeff (θ q) = 0) →
      bf (F.map (residue B)) θ ∈ firstOrderCoboundaries (F.map (residue B)) := fun θ hθ =>
    (MvFormalGroup.mem_firstOrderCoboundaries_iff (F.map (residue B)) _).mpr ⟨θ, hθ, fun l => rfl⟩
  have hθres0 : ∀ i q, MvPowerSeries.constantCoeff (MvPowerSeries.map (residue B) (θl i q)) = 0 := fun i q => by
    rw [MvPowerSeries.constantCoeff_map, hθcc, map_zero]
  have hθres0' : ∀ i q, MvPowerSeries.constantCoeff ((-fun q => MvPowerSeries.map (residue B) (θl i q)) q) = 0 := fun i q => by
    rw [Pi.neg_apply, map_neg, hθres0, neg_zero]

  refine ⟨⟨Module.finrank (ResidueField B) V, b,
      fun i => ⟨bf (F.map (residue B)) (-fun q => MvPowerSeries.map (residue B) (θl i q)), hBZ (hmemB _ (hθres0' i))⟩,
      T, fun i l => ?_, fun ξ => ?_, hD'⟩,
    ⟨Module.finrank (ResidueField B) V, b,
      fun i => ⟨bf (F.map (residue B)) (fun q => MvPowerSeries.map (residue B) (θl i q)), hBZ (hmemB _ (hθres0 i))⟩,
      fun i l => -T i l, fun i l => ?_, fun ξ => ?_, fun l => ?_⟩⟩
  · show MvPowerSeries.map (residue B) (T i l) = bf (F.map (residue B)) (-fun q => MvPowerSeries.map (residue B) (θl i q)) l
    rw [hTres, bf_neg]
  · rw [LinearMap.zero_apply]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr (hmemB _ (hθres0' i))), smul_zero]
  · show MvPowerSeries.map (residue B) (-T i l) = bf (F.map (residue B)) (fun q => MvPowerSeries.map (residue B) (θl i q)) l
    rw [map_neg, hTres, neg_neg]
  · rw [LinearMap.zero_apply]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr (hmemB _ (hθres0 i))), smul_zero]
  · rw [hD' l, add_assoc, ← Finset.sum_add_distrib]
    simp only [smul_neg, add_neg_cancel, Finset.sum_const_zero, add_zero]

end Core
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
    (G G' G₂ G₂' : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] [G'.F.IsComm] [G₂.F.IsComm] [G₂'.F.IsComm]
    (h : Deformation.IsShiftBy V ι F w G G') (h₂ : G.IsIso G₂) (h₂' : G'.IsIso G₂') :
    Deformation.IsShiftBy V ι F w G₂ G₂' := by
  obtain ⟨φ, -, hφ⟩ := h₂
  obtain ⟨φ', -, hφ'⟩ := h₂'
  have hA := (SWAux.core hI V ι hι hιI F G G₂ φ hφ).2
  have hC := (SWAux.core hI V ι hι hιI F G' G₂' φ' hφ').1
  have h1 := (MvFormalGroup.Deformation.isShiftBy_zero_and_isShiftBy_add hI V ι hι hιI F 0 w G₂ G G').2 hA h
  have h2 := (MvFormalGroup.Deformation.isShiftBy_zero_and_isShiftBy_add hI V ι hι hιI F (0 + w) 0 G₂ G' G₂').2 h1 hC
  simpa using h2

end

end S_MvFormalGroup_Deformation_isShiftBy_of_isIso_of_isIso
end P2MW
export P2MW.S_MvFormalGroup_Deformation_isShiftBy_of_isIso_of_isIso (solution)
