-- Prove2me | solution 1 for MvFormalGroup.exists_isComm_comp_substAlgHom_of_isUnit_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3d9b9596-cf8c-542f-a1c2-798d22219072

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_isComm_comp_substAlgHom_of_isUnit_matrix

open scoped TensorProduct
open MvPowerSeries

set_option autoImplicit false

universe v

namespace Recoord

section MatVec

variable {R : Type*} [CommRing R] {d : ℕ} {S : Type*} [AddCommMonoid S] [Module R S]

private def mv (M : Matrix (Fin d) (Fin d) R) (u : Fin d → S) : Fin d → S := fun i => ∑ j, M i j • u j

private theorem mv_apply (M : Matrix (Fin d) (Fin d) R) (u : Fin d → S) (i : Fin d) :
    mv M u i = ∑ j, M i j • u j := rfl

private theorem mv_mv (M N : Matrix (Fin d) (Fin d) R) (u : Fin d → S) : mv M (mv N u) = mv (M * N) u := by
  funext i
  simp only [mv_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

private theorem mv_one (u : Fin d → S) : mv (1 : Matrix (Fin d) (Fin d) R) u = u := by
  funext i
  rw [mv_apply, Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, one_smul]

private theorem map_mv {S' : Type*} [AddCommMonoid S'] [Module R S'] {F : Type*} [FunLike F S S']
    [LinearMapClass F R S S'] (f : F) (M : Matrix (Fin d) (Fin d) R) (u : Fin d → S) (i : Fin d) :
    f (mv M u i) = mv M (fun j => f (u j)) i := by
  simp only [mv_apply, map_sum, map_smul]

end MatVec

section LinSubst

variable {R : Type*} [CommRing R] {d : ℕ} {τ : Type*}

private theorem constantCoeff_mv (M : Matrix (Fin d) (Fin d) R) {u : Fin d → MvPowerSeries τ R}
    (hu : ∀ j, (u j).constantCoeff = 0) (i : Fin d) : (mv M u i).constantCoeff = 0 := by
  rw [mv_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_eq_C_mul, map_mul, hu j, mul_zero]

private theorem subst_mv {τ' : Type*} {a : τ → MvPowerSeries τ' R} (ha : HasSubst a)
    (M : Matrix (Fin d) (Fin d) R) (u : Fin d → MvPowerSeries τ R) (i : Fin d) :
    subst a (mv M u i) = mv M (fun j => subst a (u j)) i := by
  rw [← coe_substAlgHom ha]
  exact map_mv (substAlgHom ha).toLinearMap M u i

private theorem coeff_single_mv (M : Matrix (Fin d) (Fin d) R) (u : Fin d → MvPowerSeries τ R) (t : τ) (i : Fin d) :
    coeff (Finsupp.single t 1) (mv M u i) = ∑ j, M i j * coeff (Finsupp.single t 1) (u j) := by
  rw [map_mv]
  rfl

variable (d) in

private noncomputable def lin (M : Matrix (Fin d) (Fin d) R) : Fin d → MvPowerSeries (Fin d) R :=
  mv M fun j => (X j : MvPowerSeries (Fin d) R)

private theorem lin_apply (M : Matrix (Fin d) (Fin d) R) (i : Fin d) :
    lin d M i = ∑ j, M i j • (X j : MvPowerSeries (Fin d) R) := rfl

private theorem constantCoeff_lin (M : Matrix (Fin d) (Fin d) R) (i : Fin d) : (lin d M i).constantCoeff = 0 :=
  constantCoeff_mv M (fun j => constantCoeff_X j) i

private theorem hasSubst_lin (M : Matrix (Fin d) (Fin d) R) : HasSubst (lin d M) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_lin M)

private theorem subst_lin_apply {a : Fin d → MvPowerSeries τ R} (ha : HasSubst a) (M : Matrix (Fin d) (Fin d) R)
    (i : Fin d) : subst a (lin d M i) = mv M a i := by
  rw [lin, subst_mv ha]
  congr 1
  funext j
  exact subst_X ha j

private theorem subst_lin_lin (M N : Matrix (Fin d) (Fin d) R) (i : Fin d) :
    subst (lin d N) (lin d M i) = lin d (M * N) i := by
  rw [subst_lin_apply (hasSubst_lin N), lin, lin, mv_mv]

variable {P Q : Matrix (Fin d) (Fin d) R}

private theorem subst_lin_lin_of_mul_eq_one (h : P * Q = 1) (i : Fin d) :
    subst (lin d Q) (lin d P i) = X i := by
  rw [subst_lin_lin, h, lin, mv_one]

private theorem subst_lin_subst_lin (h : P * Q = 1) (F : MvPowerSeries (Fin d) R) :
    subst (lin d Q) (subst (lin d P) F) = F := by
  rw [subst_comp_subst_apply (hasSubst_lin P) (hasSubst_lin Q)]
  have : (fun s => subst (lin d Q) (lin d P s)) = fun s => (X s : MvPowerSeries (Fin d) R) :=
    funext fun s => subst_lin_lin_of_mul_eq_one h s
  rw [this, subst_self]
  rfl

private noncomputable def linEquiv (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    MvPowerSeries (Fin d) R ≃ₐ[R] MvPowerSeries (Fin d) R :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_lin P)) (substAlgHom (hasSubst_lin Q))
    (AlgHom.ext fun F => by
      rw [AlgHom.comp_apply, coe_substAlgHom, coe_substAlgHom, subst_lin_subst_lin hQP]; rfl)
    (AlgHom.ext fun F => by
      rw [AlgHom.comp_apply, coe_substAlgHom, coe_substAlgHom, subst_lin_subst_lin hPQ]; rfl)

private theorem linEquiv_apply (hPQ : P * Q = 1) (hQP : Q * P = 1) (F : MvPowerSeries (Fin d) R) :
    linEquiv hPQ hQP F = subst (lin d P) F := by
  rw [linEquiv, AlgEquiv.ofAlgHom_apply, coe_substAlgHom]

private theorem linEquiv_symm_apply (hPQ : P * Q = 1) (hQP : Q * P = 1) (F : MvPowerSeries (Fin d) R) :
    (linEquiv hPQ hQP).symm F = subst (lin d Q) F := by
  rw [linEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply, coe_substAlgHom]

private theorem span_range_mv (hQP : Q * P = 1) (f : Fin d → MvPowerSeries τ R) :
    Ideal.span (Set.range (mv P f)) = Ideal.span (Set.range f) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mv_apply]
    exact Ideal.sum_mem _ fun j _ => by
      rw [smul_eq_C_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hf : f j = mv Q (mv P f) j := by rw [mv_mv, hQP, mv_one]
    rw [SetLike.mem_coe, hf, mv_apply]
    exact Ideal.sum_mem _ fun i _ => by
      rw [smul_eq_C_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end LinSubst

section Law

variable {R : Type*} [CommRing R] {d : ℕ} {τ : Type*}

private noncomputable def ev (Φ : MvFormalGroup d R) (u w : Fin d → MvPowerSeries τ R) : Fin d → MvPowerSeries τ R :=
  fun i => subst (Sum.elim u w) (Φ.toPowerSeries i)

private theorem constantCoeff_ev (Φ : MvFormalGroup d R) {u w : Fin d → MvPowerSeries τ R}
    (hu : ∀ j, (u j).constantCoeff = 0) (hw : ∀ j, (w j).constantCoeff = 0) (i : Fin d) :
    (ev Φ u w i).constantCoeff = 0 :=
  MvFormalGroup.constantCoeff_subst_elim Φ hu hw i

private theorem subst_ev {τ' : Type*} {a : τ → MvPowerSeries τ' R} (ha : HasSubst a) (Φ : MvFormalGroup d R)
    {u w : Fin d → MvPowerSeries τ R} (hu : ∀ j, (u j).constantCoeff = 0) (hw : ∀ j, (w j).constantCoeff = 0)
    (i : Fin d) :
    subst a (ev Φ u w i) = ev Φ (fun j => subst a (u j)) (fun j => subst a (w j)) i := by
  rw [ev, ev, subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hu hw) ha]
  congr 1
  funext s
  rcases s with j | j <;> rfl

private theorem ev_X (Φ : MvFormalGroup d R) (i : Fin d) :
    ev Φ (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inr j)) i =
      Φ.toPowerSeries i := by
  have : (Sum.elim (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) R)) fun j => X (Sum.inr j)) =
      fun s => X s := by
    funext s; rcases s with j | j <;> rfl
  rw [ev, this, subst_self]
  rfl

variable (P Q : Matrix (Fin d) (Fin d) R) (Φ : MvFormalGroup d R)

private noncomputable def lawSeries : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R :=
  mv P (ev Φ (mv Q fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) R))
    (mv Q fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)))

private theorem constantCoeff_mv_X_inl (j : Fin d) :
    (mv Q (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) j).constantCoeff = 0 :=
  constantCoeff_mv Q (fun _ => constantCoeff_X _) j

private theorem constantCoeff_mv_X_inr (j : Fin d) :
    (mv Q (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) j).constantCoeff = 0 :=
  constantCoeff_mv Q (fun _ => constantCoeff_X _) j

private theorem constantCoeff_lawSeries (i : Fin d) : (lawSeries P Q Φ i).constantCoeff = 0 :=
  constantCoeff_mv P (constantCoeff_ev Φ (constantCoeff_mv_X_inl Q) (constantCoeff_mv_X_inr Q)) i

variable {P Q Φ}

private theorem subst_elim_lawSeries {u w : Fin d → MvPowerSeries τ R}
    (hu : ∀ j, (u j).constantCoeff = 0) (hw : ∀ j, (w j).constantCoeff = 0) (i : Fin d) :
    subst (Sum.elim u w) (lawSeries P Q Φ i) = mv P (ev Φ (mv Q u) (mv Q w)) i := by
  have h := MvFormalGroup.hasSubst_elim hu hw
  rw [lawSeries, subst_mv h]
  have hfam : (fun j => subst (Sum.elim u w)
      (ev Φ (mv Q fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (mv Q fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) j)) =
      ev Φ (mv Q u) (mv Q w) := by
    funext j
    rw [subst_ev h Φ (constantCoeff_mv_X_inl Q) (constantCoeff_mv_X_inr Q)]
    have h1 : (fun l => subst (Sum.elim u w) (mv Q (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) l)) =
        mv Q u := by
      funext l
      rw [subst_mv h]
      congr 1
      funext m
      exact subst_X h (Sum.inl m)
    have h2 : (fun l => subst (Sum.elim u w) (mv Q (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) R)) l)) =
        mv Q w := by
      funext l
      rw [subst_mv h]
      congr 1
      funext m
      exact subst_X h (Sum.inr m)
    rw [h1, h2]
  rw [hfam]

variable (P Q Φ)

private theorem coeff_single_inl_X_inl (j l : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R) =
      if l = j then 1 else 0 := by
  rw [coeff_X]
  by_cases hlj : l = j
  · subst hlj; simp
  · rw [if_neg (fun h => hlj (Sum.inl_injective (Finsupp.single_left_injective one_ne_zero h)).symm), if_neg hlj]

private theorem coeff_single_inr_X_inr (j l : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R) =
      if l = j then 1 else 0 := by
  rw [coeff_X]
  by_cases hlj : l = j
  · subst hlj; simp
  · rw [if_neg (fun h => hlj (Sum.inr_injective (Finsupp.single_left_injective one_ne_zero h)).symm), if_neg hlj]

private theorem coeff_single_inl_X_inr (j l : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 := by
  rw [coeff_X, if_neg]
  intro h
  exact Sum.inl_ne_inr (Finsupp.single_left_injective one_ne_zero h)

private theorem coeff_single_inr_X_inl (j l : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 := by
  rw [coeff_X, if_neg]
  intro h
  exact Sum.inr_ne_inl (Finsupp.single_left_injective one_ne_zero h)

private theorem coeff_single_inl_ev (m j : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1)
      (ev Φ (mv Q fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (mv Q fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) m) = Q m j := by
  classical
  have hc0 : ∀ s, (Sum.elim (mv Q fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (mv Q fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) s).constantCoeff = 0 := by
    rintro (s | s)
    · exact constantCoeff_mv_X_inl Q s
    · exact constantCoeff_mv_X_inr Q s
  rw [ev, MvFormalGroup.coeff_single_subst hc0, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Φ.coeff_single_inl, Φ.coeff_single_inr, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, coeff_single_mv, coeff_single_inl_X_inl, coeff_single_inl_X_inr,
    mul_ite, mul_one, mul_zero, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq']

private theorem coeff_single_inr_ev (m j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1)
      (ev Φ (mv Q fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (mv Q fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) m) = Q m j := by
  classical
  have hc0 : ∀ s, (Sum.elim (mv Q fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (mv Q fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) s).constantCoeff = 0 := by
    rintro (s | s)
    · exact constantCoeff_mv_X_inl Q s
    · exact constantCoeff_mv_X_inr Q s
  rw [ev, MvFormalGroup.coeff_single_subst hc0, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Φ.coeff_single_inl, Φ.coeff_single_inr, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, coeff_single_mv, coeff_single_inr_X_inr, coeff_single_inr_X_inl,
    mul_ite, mul_one, mul_zero, Finset.sum_const_zero, zero_add, Finset.sum_ite_eq']

variable {P Q}

private noncomputable def law (hPQ : P * Q = 1) (hQP : Q * P = 1) : MvFormalGroup d R where
  toPowerSeries := lawSeries P Q Φ
  constantCoeff_eq_zero := constantCoeff_lawSeries P Q Φ
  coeff_single_inl := fun i j => by
    change coeff _ (lawSeries P Q Φ i) = _
    rw [lawSeries, coeff_single_mv]
    simp_rw [coeff_single_inl_ev Q Φ, ← Matrix.mul_apply, hPQ, Matrix.one_apply]
  coeff_single_inr := fun i j => by
    change coeff _ (lawSeries P Q Φ i) = _
    rw [lawSeries, coeff_single_mv]
    simp_rw [coeff_single_inr_ev Q Φ, ← Matrix.mul_apply, hPQ, Matrix.one_apply]
  assoc := fun i => by

    have hA0 : ∀ j, (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R).constantCoeff = 0 :=
      fun j => constantCoeff_X _
    have hB0 : ∀ j, (X (Sum.inr (Sum.inl j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R).constantCoeff = 0 :=
      fun j => constantCoeff_X _
    have hC0 : ∀ j, (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R).constantCoeff = 0 :=
      fun j => constantCoeff_X _
    have hAB0 : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        fun l => X (Sum.inr (Sum.inl l))) (lawSeries P Q Φ j)).constantCoeff = 0 := fun j =>
      constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hA0 hB0)
        (by rintro (s | s) <;> exact constantCoeff_X _) (constantCoeff_lawSeries P Q Φ j)
    have hBC0 : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        fun l => X (Sum.inr (Sum.inr l))) (lawSeries P Q Φ j)).constantCoeff = 0 := fun j =>
      constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hB0 hC0)
        (by rintro (s | s) <;> exact constantCoeff_X _) (constantCoeff_lawSeries P Q Φ j)
    change subst (Sum.elim (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        (fun l => X (Sum.inr (Sum.inl l)))) (lawSeries P Q Φ j)) (fun j => X (Sum.inr (Sum.inr j))))
        (lawSeries P Q Φ i) =
      subst (Sum.elim (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        (fun j => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
          (fun l => X (Sum.inr (Sum.inr l)))) (lawSeries P Q Φ j))) (lawSeries P Q Φ i)
    rw [subst_elim_lawSeries hAB0 hC0, subst_elim_lawSeries hA0 hBC0]
    have hL : (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        fun l => X (Sum.inr (Sum.inl l))) (lawSeries P Q Φ j)) =
        mv P (ev Φ (mv Q fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
          (mv Q fun l => X (Sum.inr (Sum.inl l)))) := funext fun j => subst_elim_lawSeries hA0 hB0 j
    have hR : (fun j => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
        fun l => X (Sum.inr (Sum.inr l))) (lawSeries P Q Φ j)) =
        mv P (ev Φ (mv Q fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
          (mv Q fun l => X (Sum.inr (Sum.inr l)))) := funext fun j => subst_elim_lawSeries hB0 hC0 j
    rw [hL, hR, mv_mv, mv_mv, hQP, mv_one, mv_one]
    exact congrArg (fun f => mv P f i) (funext fun m =>
      MvFormalGroup.subst_elim_assoc Φ (constantCoeff_mv Q hA0) (constantCoeff_mv Q hB0) (constantCoeff_mv Q hC0) m)

private theorem law_toPowerSeries (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (law Φ hPQ hQP).toPowerSeries = lawSeries P Q Φ := rfl

private theorem law_isComm [Φ.IsComm] (hPQ : P * Q = 1) (hQP : Q * P = 1) : (law Φ hPQ hQP).IsComm := by
  refine ⟨fun i => ?_⟩
  change subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) fun j => X (Sum.inl j))
      (lawSeries P Q Φ i) = lawSeries P Q Φ i
  rw [subst_elim_lawSeries (fun j => constantCoeff_X _) (fun j => constantCoeff_X _)]
  exact congrArg (fun f => mv P f i) (funext fun m =>
    MvFormalGroup.subst_elim_comm Φ (constantCoeff_mv_X_inr Q) (constantCoeff_mv_X_inl Q) m)

private noncomputable def linHom (hPQ : P * Q = 1) (hQP : Q * P = 1) : MvFormalGroup.Hom Φ (law Φ hPQ hQP) where
  toPowerSeries := lin d P
  constantCoeff_eq_zero := constantCoeff_lin P
  subst_eq := fun i => by
    have hl : HasSubst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hr : HasSubst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    change subst Φ.toPowerSeries (lin d P i) =
      subst (Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (lin d P j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (lin d P j)))
        (lawSeries P Q Φ i)
    rw [subst_lin_apply Φ.hasSubst_toPowerSeries]
    have h1 : (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (lin d P j)) =
        mv P fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R) := funext fun j => subst_lin_apply hl P j
    have h2 : (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (lin d P j)) =
        mv P fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R) := funext fun j => subst_lin_apply hr P j
    rw [h1, h2, subst_elim_lawSeries (constantCoeff_mv P fun l => constantCoeff_X _)
      (constantCoeff_mv P fun l => constantCoeff_X _), mv_mv, mv_mv, hQP, mv_one, mv_one]
    exact congrArg (fun f => mv P f i) (funext fun m => (ev_X Φ m).symm)

private theorem linHom_toPowerSeries (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (linHom Φ hPQ hQP).toPowerSeries = lin d P := rfl

end Law

section NthSeries

variable {R : Type*} [CommRing R] {d : ℕ} {P Q : Matrix (Fin d) (Fin d) R} (Φ : MvFormalGroup d R)

private theorem nthSeries_law (hPQ : P * Q = 1) (hQP : Q * P = 1) (n : ℕ) :
    (law Φ hPQ hQP).nthSeries n = fun i => subst (lin d Q) (mv P (Φ.nthSeries n) i) := by
  induction n with
  | zero =>
    funext i
    rw [MvFormalGroup.nthSeries_zero, MvFormalGroup.nthSeries_zero]
    have : mv P (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) i = 0 := by
      rw [mv_apply]; exact Finset.sum_eq_zero fun j _ => smul_zero _
    rw [this, ← coe_substAlgHom (hasSubst_lin Q), map_zero]
  | succ n ih =>
    funext i
    have hu : ∀ j, (subst (lin d Q) (mv P (Φ.nthSeries n) j)).constantCoeff = 0 := fun j =>
      constantCoeff_subst_eq_zero (hasSubst_lin Q) (constantCoeff_lin Q)
        (constantCoeff_mv P (MvFormalGroup.constantCoeff_nthSeries Φ n) j)
    rw [MvFormalGroup.nthSeries_succ, ih, law_toPowerSeries]
    dsimp only
    rw [subst_elim_lawSeries hu (fun j => constantCoeff_X j)]
    have h1 : mv Q (fun j => subst (lin d Q) (mv P (Φ.nthSeries n) j)) = fun j => subst (lin d Q) (Φ.nthSeries n j) := by
      have : (fun j => subst (lin d Q) (mv P (Φ.nthSeries n) j)) =
          mv P (fun m => subst (lin d Q) (Φ.nthSeries n m)) := funext fun j => subst_mv (hasSubst_lin Q) P _ j
      rw [this, mv_mv, hQP, mv_one]
    have h2 : mv Q (fun j => (X j : MvPowerSeries (Fin d) R)) = lin d Q := rfl
    have h3 : (fun j => subst (lin d Q) (X j : MvPowerSeries (Fin d) R)) = lin d Q :=
      funext fun j => subst_X (hasSubst_lin Q) j
    rw [h1, h2, MvFormalGroup.nthSeries_succ, subst_mv (hasSubst_lin Q)]
    refine congrArg (fun f => mv P f i) (funext fun m => ?_)
    change ev Φ (fun j => subst (lin d Q) (Φ.nthSeries n j)) (lin d Q) m =
      subst (lin d Q) (ev Φ (Φ.nthSeries n) (fun j => X j) m)
    rw [subst_ev (hasSubst_lin Q) Φ (MvFormalGroup.constantCoeff_nthSeries Φ n) (fun j => constantCoeff_X j), h3]

private theorem span_nthSeries_law (hPQ : P * Q = 1) (hQP : Q * P = 1) (n : ℕ) :
    Ideal.span (Set.range ((law Φ hPQ hQP).nthSeries n)) =
      (Ideal.span (Set.range (Φ.nthSeries n))).map (substAlgHom (hasSubst_lin Q) :
        MvPowerSeries (Fin d) R →ₐ[R] MvPowerSeries (Fin d) R) := by
  rw [nthSeries_law Φ hPQ hQP, ← span_range_mv hQP (Φ.nthSeries n) (P := P), Ideal.map_span, ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext fun i => by rw [Function.comp_apply, coe_substAlgHom])

private theorem comap_substAlgHom_lin (hPQ : P * Q = 1) (hQP : Q * P = 1) (I : Ideal (MvPowerSeries (Fin d) R)) :
    I.comap (substAlgHom (hasSubst_lin P) : MvPowerSeries (Fin d) R →ₐ[R] MvPowerSeries (Fin d) R) =
      I.map (substAlgHom (hasSubst_lin Q) : MvPowerSeries (Fin d) R →ₐ[R] MvPowerSeries (Fin d) R) := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap, coe_substAlgHom] at hx
    have : x = substAlgHom (hasSubst_lin Q) (subst (lin d P) x) := by
      rw [coe_substAlgHom, subst_lin_subst_lin hPQ]
    rw [this]
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_comap, coe_substAlgHom, coe_substAlgHom, subst_lin_subst_lin hQP]
    exact hy

end NthSeries

section Fibre

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {P Q : Matrix (Fin d) (Fin d) (ZMod p)}

private theorem map_mem_radical {𝓞 : Type*} [CommRing 𝓞] (q : ℕ) {B C : Type*} [CommRing B] [Algebra 𝓞 B]
    [CommRing C] [Algebra 𝓞 C] (f : B →ₐ[𝓞] C) {b : B} (hb : b ∈ (Ideal.span {(q : B)}).radical) :
    f b ∈ (Ideal.span {(q : C)}).radical := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [← map_pow, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B]

private theorem mv_mem_radical {x : Fin d → B} (J : Ideal B) (hx : ∀ j, x j ∈ J.radical) (M : Matrix (Fin d) (Fin d) (ZMod p))
    (i : Fin d) : mv M x i ∈ J.radical := by
  rw [mv_apply]
  exact Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hx j)

private theorem comul_mv (Φ : MvFormalGroup d (ZMod p)) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    [IsAdicComplete (Ideal.span {(p : B ⊗[ZMod p] B)}) (B ⊗[ZMod p] B)]
    (x : Fin d → B) (hx : ∀ i, x i ∈ (Ideal.span {(p : B)}).radical)
    (hΔ : ∀ i, Coalgebra.comul (R := ZMod p) (x i) =
      MvFormalGroup.adicEval (Ideal.span {(p : B ⊗[ZMod p] B)})
        (Sum.elim (fun j => x j ⊗ₜ[ZMod p] (1 : B)) (fun j => (1 : B) ⊗ₜ[ZMod p] x j)) (Φ.toPowerSeries i))
    (i : Fin d) :
    Coalgebra.comul (R := ZMod p) (mv P x i) =
      MvFormalGroup.adicEval (Ideal.span {(p : B ⊗[ZMod p] B)})
        (Sum.elim (fun j => mv P x j ⊗ₜ[ZMod p] (1 : B)) (fun j => (1 : B) ⊗ₜ[ZMod p] mv P x j))
        ((law Φ hPQ hQP).toPowerSeries i) := by
  set J₂ : Ideal (B ⊗[ZMod p] B) := Ideal.span {(p : B ⊗[ZMod p] B)} with hJ₂
  set b₀ : Fin d ⊕ Fin d → B ⊗[ZMod p] B := Sum.elim (fun j => x j ⊗ₜ[ZMod p] (1 : B)) (fun j => (1 : B) ⊗ₜ[ZMod p] x j)
    with hb₀
  set b' : Fin d ⊕ Fin d → B ⊗[ZMod p] B :=
    Sum.elim (fun j => mv P x j ⊗ₜ[ZMod p] (1 : B)) (fun j => (1 : B) ⊗ₜ[ZMod p] mv P x j) with hb'
  have hb'rad : ∀ s, b' s ∈ J₂.radical := by
    rintro (j | j)
    · rw [hb', Sum.elim_inl]
      exact map_mem_radical p (Algebra.TensorProduct.includeLeft : B →ₐ[ZMod p] B ⊗[ZMod p] B)
        (mv_mem_radical _ hx P j)
    · rw [hb', Sum.elim_inr]
      exact map_mem_radical p (Algebra.TensorProduct.includeRight : B →ₐ[ZMod p] B ⊗[ZMod p] B)
        (mv_mem_radical _ hx P j)

  rw [map_mv (Coalgebra.comul (R := ZMod p) (A := B)) P x i]
  simp_rw [hΔ]

  rw [law_toPowerSeries, lawSeries, ← MvFormalGroup.coe_adicEvalAlgHom J₂ hb'rad,
    map_mv (MvFormalGroup.adicEvalAlgHom (R := ZMod p) J₂ hb'rad)]
  refine congrArg (fun f => mv P f i) (funext fun m => ?_)
  rw [MvFormalGroup.coe_adicEvalAlgHom, ev,
    MvFormalGroup.adicEval_subst J₂ hb'rad (MvFormalGroup.hasSubst_elim (constantCoeff_mv_X_inl Q)
      (constantCoeff_mv_X_inr Q))]
  congr 1
  funext s
  rcases s with j | j
  · rw [Sum.elim_inl, hb₀, Sum.elim_inl, ← MvFormalGroup.coe_adicEvalAlgHom J₂ hb'rad, map_mv,
      MvFormalGroup.coe_adicEvalAlgHom]
    have h1 : (fun l => MvFormalGroup.adicEval J₂ b' (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) (ZMod p))) =
        fun l => mv P x l ⊗ₜ[ZMod p] (1 : B) := by
      funext l; rw [MvFormalGroup.adicEval_X, hb', Sum.elim_inl]
    rw [h1, mv_apply]
    simp_rw [TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul]
    congr 1
    have := congrFun (mv_mv Q P x) j
    rw [hQP, mv_one] at this
    rw [← this, mv_apply]
  · rw [Sum.elim_inr, hb₀, Sum.elim_inr, ← MvFormalGroup.coe_adicEvalAlgHom J₂ hb'rad, map_mv,
      MvFormalGroup.coe_adicEvalAlgHom]
    have h1 : (fun l => MvFormalGroup.adicEval J₂ b' (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) (ZMod p))) =
        fun l => (1 : B) ⊗ₜ[ZMod p] mv P x l := by
      funext l; rw [MvFormalGroup.adicEval_X, hb', Sum.elim_inr]
    rw [h1, mv_apply]
    simp_rw [← TensorProduct.tmul_smul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    have := congrFun (mv_mv Q P x) j
    rw [hQP, mv_one] at this
    rw [← this, mv_apply]

end Fibre

end Recoord

open Recoord in
theorem solution
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (Φ : MvFormalGroup d (ZMod p)) [Φ.IsComm]
    (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v)
    (hκsurj : ∀ v, Function.Surjective (κ v))
    (hκker : ∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v))))
    (hκs : ∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ (v + 1)) = κ v)
    (hκε : ∀ v i, Coalgebra.counit (R := ZMod p) (κ v (X i)) = 0)
    (hκrad : ∀ v i, κ v (X i) ∈ (Ideal.span {(p : G v)}).radical)
    (hκeval : ∀ v F, κ v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ v (X i)) F)
    (hκΔ : ∀ v i, Coalgebra.comul (R := ZMod p) (κ v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
        (Sum.elim (fun j => κ v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ v (X j)))
        (Φ.toPowerSeries i))
    (P : Matrix (Fin d) (Fin d) (ZMod p)) (hP : IsUnit P) :
    ∃ (Φ' : MvFormalGroup d (ZMod p)) (_ : Φ'.IsComm) (ℓ : MvFormalGroup.Hom Φ Φ')
      (κ' : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v),
      (ℓ.toPowerSeries = fun i => ∑ j, P i j • (X j : MvPowerSeries (Fin d) (ZMod p))) ∧
      (∀ v F, κ' v F = κ v (MvPowerSeries.subst ℓ.toPowerSeries F)) ∧
      (∀ v, Function.Surjective (κ' v)) ∧
      (∀ v, RingHom.ker (κ' v) = Ideal.span (Set.range (Φ'.nthSeries (p ^ v)))) ∧
      (∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ' (v + 1)) = κ' v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (κ' v (X i)) = 0) ∧
      (∀ v i, κ' v (X i) ∈ (Ideal.span {(p : G v)}).radical) ∧
      (∀ v F, κ' v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ' v (X i)) F) ∧
      (∀ v i, Coalgebra.comul (R := ZMod p) (κ' v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
          (Sum.elim (fun j => κ' v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ' v (X j)))
          (Φ'.toPowerSeries i)) ∧
      Module.finrank (ZMod p) (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ'.nthSeries p))) =
        Module.finrank (ZMod p) (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) := by
  classical

  set Q : Matrix (Fin d) (Fin d) (ZMod p) := ↑(hP.unit⁻¹) with hQ
  have hPQ : P * Q = 1 := hP.mul_val_inv
  have hQP : Q * P = 1 := hP.val_inv_mul

  have hp0 : ∀ v, (p : G v) = 0 := fun v => by
    rw [← map_natCast (algebraMap (ZMod p) (G v)) p, ZMod.natCast_self, map_zero]
  have hp0' : ∀ v, (p : G v ⊗[ZMod p] G v) = 0 := fun v => by
    rw [← map_natCast (algebraMap (ZMod p) (G v ⊗[ZMod p] G v)) p, ZMod.natCast_self, map_zero]
  haveI : ∀ v, IsAdicComplete (Ideal.span {(p : G v)}) (G v) := fun v => by
    rw [Ideal.span_singleton_eq_bot.2 (hp0 v)]; infer_instance
  haveI : ∀ v, IsAdicComplete (Ideal.span {(p : G v ⊗[ZMod p] G v)}) (G v ⊗[ZMod p] G v) := fun v => by
    rw [Ideal.span_singleton_eq_bot.2 (hp0' v)]; infer_instance

  haveI : (law Φ hPQ hQP).IsComm := law_isComm Φ hPQ hQP
  let κ' : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v := fun v => (κ v).comp (substAlgHom (hasSubst_lin P))
  have hκ' : ∀ v F, κ' v F = κ v (MvPowerSeries.subst (lin d P) F) := fun v F => by
    change κ v (substAlgHom (hasSubst_lin P) F) = _
    rw [coe_substAlgHom]
  have hy : ∀ v j, κ' v (X j) = mv P (fun l => κ v (X l)) j := fun v j => by
    rw [hκ', subst_X (hasSubst_lin P), lin, map_mv]
  have hrad' : ∀ v i, κ' v (X i) ∈ (Ideal.span {(p : G v)}).radical := fun v i => by
    rw [hy]; exact mv_mem_radical _ (hκrad v) P i
  refine ⟨law Φ hPQ hQP, inferInstance, linHom Φ hPQ hQP, κ', rfl, hκ', fun v => ?_, fun v => ?_, fun v => ?_,
    fun v i => ?_, hrad', fun v F => ?_, fun v i => ?_, ?_⟩
  ·
    intro b
    obtain ⟨F, rfl⟩ := hκsurj v b
    exact ⟨subst (lin d Q) F, by rw [hκ', subst_lin_subst_lin hQP]⟩
  ·
    have h1 : RingHom.ker (κ' v) = (RingHom.ker (κ v)).comap (substAlgHom (hasSubst_lin P) :
        MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] MvPowerSeries (Fin d) (ZMod p)) := by
      ext F
      rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
      rfl
    rw [h1, hκker v, comap_substAlgHom_lin hPQ hQP, span_nthSeries_law Φ hPQ hQP]
  ·
    change (s v : G (v + 1) →ₐ[ZMod p] G v).comp ((κ (v + 1)).comp (substAlgHom (hasSubst_lin P))) =
      (κ v).comp (substAlgHom (hasSubst_lin P))
    rw [← AlgHom.comp_assoc, hκs v]
  ·
    rw [hy, map_mv (Coalgebra.counit (R := ZMod p) (A := G v)), mv_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [hκε, smul_zero]
  ·
    rw [hκ', hκeval v, MvFormalGroup.adicEval_subst (Ideal.span {(p : G v)}) (hκrad v) (hasSubst_lin P)]
    congr 1
    funext i
    rw [hκ', subst_X (hasSubst_lin P), ← hκeval v]
  ·
    simp only [hy]
    exact comul_mv Φ hPQ hQP (fun l => κ v (X l)) (hκrad v) (hκΔ v) i
  ·
    have hIJ : Ideal.span (Set.range ((law Φ hPQ hQP).nthSeries p)) =
        (Ideal.span (Set.range (Φ.nthSeries p))).map
          ((linEquiv hQP hPQ : MvPowerSeries (Fin d) (ZMod p) ≃ₐ[ZMod p] MvPowerSeries (Fin d) (ZMod p)) :
            MvPowerSeries (Fin d) (ZMod p) →+* MvPowerSeries (Fin d) (ZMod p)) := by
      rw [span_nthSeries_law Φ hPQ hQP p]
      rfl
    exact (Ideal.quotientEquivAlg _ _ (linEquiv hQP hPQ) hIJ).toLinearEquiv.finrank_eq.symm

end S_MvFormalGroup_exists_isComm_comp_substAlgHom_of_isUnit_matrix
end P2MW
export P2MW.S_MvFormalGroup_exists_isComm_comp_substAlgHom_of_isUnit_matrix (solution)
