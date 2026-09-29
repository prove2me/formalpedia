-- Prove2me | solution 1 for LT.LatticeTree.fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/13010b11-bf0f-5141-94bc-62ed9a6532de

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul

set_option autoImplicit false

open LT.LatticeTree
open scoped Matrix

namespace VAN3

section General

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem mul_self_eq (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem mulVec_mulVec_self (M : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → K) :
    M *ᵥ (M *ᵥ x) = M.trace • (M *ᵥ x) - M.det • x := by
  rw [Matrix.mulVec_mulVec, mul_self_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem algebraMap_smul_mem (L : Submodule R (Fin 2 → K)) {x : Fin 2 → K} (hx : x ∈ L) (r : R) :
    algebraMap R K r • x ∈ L := by
  rw [algebraMap_smul]; exact L.smul_mem r hx

def T (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) : Matrix (Fin 2) (Fin 2) K :=
  algebraMap R K ϖ ^ i • Y.map (algebraMap R K)

theorem T_eq_map (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) :
    T (K := K) ϖ Y i = (ϖ ^ i • Y).map (algebraMap R K) := by
  ext a b; simp [T, Matrix.map_apply, Matrix.smul_apply, map_mul, map_pow]

theorem trace_T (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) :
    (T (K := K) ϖ Y i).trace = algebraMap R K (ϖ ^ i * Y.trace) := by
  simp only [T, Matrix.trace_fin_two, Matrix.smul_apply, Matrix.map_apply, map_add, map_mul, map_pow, smul_eq_mul]
  ring

theorem det_T (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) :
    (T (K := K) ϖ Y i).det = algebraMap R K (ϖ ^ (2 * i) * Y.det) := by
  simp only [T, Matrix.det_fin_two, Matrix.smul_apply, Matrix.map_apply, map_sub, map_mul, map_pow, smul_eq_mul]
  ring

theorem T_succ (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) :
    T (K := K) ϖ Y (i + 1) = algebraMap R K ϖ • T ϖ Y i := by
  simp only [T, pow_succ, smul_smul, mul_comm]

def dOne (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) : R := 1 + ϖ ^ i * Y.trace + ϖ ^ (2 * i) * Y.det

theorem det_one_add_T (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) :
    (1 + T (K := K) ϖ Y i).det = algebraMap R K (dOne ϖ Y i) := by
  simp only [T, dOne, Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    Matrix.trace_fin_two, map_add, map_mul, map_pow, map_sub, map_one, smul_eq_mul]
  ring

theorem T_mulVec_T_mulVec_mem (ϖ : R) (Y : Matrix (Fin 2) (Fin 2) R) (i : ℕ) (L : Submodule R (Fin 2 → K))
    {x : Fin 2 → K} (hx : x ∈ L) (hTx : T ϖ Y i *ᵥ x ∈ L) : T ϖ Y i *ᵥ (T (K := K) ϖ Y i *ᵥ x) ∈ L := by
  rw [mulVec_mulVec_self, trace_T, det_T]
  exact L.sub_mem (algebraMap_smul_mem L hTx _) (algebraMap_smul_mem L hx _)

end General

section DVR

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem isUnit_dOne {ϖ : R} (hϖ : Irreducible ϖ) (Y : Matrix (Fin 2) (Fin 2) R) {i : ℕ} (hi : 1 ≤ i) :
    IsUnit (dOne ϖ Y i) := by
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hϖ.not_isUnit
  have h1 : ϖ ^ i * Y.trace + ϖ ^ (2 * i) * Y.det ∈ IsLocalRing.maximalIdeal R := by
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hmem _ hi))
      (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hmem _ (by omega)))
  have h2 := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(ϖ ^ i * Y.trace + ϖ ^ (2 * i) * Y.det))
    (by rw [← IsLocalRing.mem_maximalIdeal]; exact (IsLocalRing.maximalIdeal R).neg_mem h1)
  have : dOne ϖ Y i = 1 - -(ϖ ^ i * Y.trace + ϖ ^ (2 * i) * Y.det) := by rw [dOne]; ring
  rwa [this]

omit [IsFractionRing R K] in

theorem latticeMap_eq_of_stable {ϖ : R} (hϖ : Irreducible ϖ) (Y : Matrix (Fin 2) (Fin 2) R) {i : ℕ} (hi : 1 ≤ i)
    (h : Matrix.GeneralLinearGroup (Fin 2) K) (hh : (h : Matrix (Fin 2) (Fin 2) K) = 1 + T ϖ Y i)
    (L : Submodule R (Fin 2 → K)) (hT : ∀ x ∈ L, T (K := K) ϖ Y i *ᵥ x ∈ L) : latticeMap h L = L := by
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
    rw [hh, Matrix.add_mulVec, Matrix.one_mulVec]
    exact L.add_mem hw (hT w hw)
  · intro x hx
    obtain ⟨u, hu⟩ := isUnit_dOne hϖ Y hi

    set y₀ : Fin 2 → K := algebraMap R K (1 + ϖ ^ i * Y.trace) • x - T ϖ Y i *ᵥ x with hy₀
    have hy₀L : y₀ ∈ L := L.sub_mem (algebraMap_smul_mem L hx _) (hT x hx)
    have hHy₀ : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ y₀ = algebraMap R K (dOne ϖ Y i) • x := by
      rw [hy₀, hh, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, mulVec_mulVec_self,
        trace_T, det_T]
      simp only [dOne, map_add, map_mul, map_pow, map_one]
      module
    refine mem_latticeMap.mpr ⟨algebraMap R K ((u⁻¹ : Rˣ) : R) • y₀, algebraMap_smul_mem L hy₀L _, ?_⟩
    rw [Matrix.mulVec_smul, hHy₀, smul_smul, ← map_mul, ← hu, Units.inv_mul, map_one, one_smul]

theorem latticeMap_eq_of_homothetic {h : Matrix.GeneralLinearGroup (Fin 2) K} {d : R} (hd : IsUnit d)
    (hdet : (h : Matrix (Fin 2) (Fin 2) K).det = algebraMap R K d)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (hhom : Homothetic (latticeMap h L) L) :
    latticeMap h L = L := by
  obtain ⟨c, hc⟩ := hhom

  obtain ⟨P, hP⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K (Vertex.mk R K L hL)
  rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff] at hP
  obtain ⟨c₀, hc₀⟩ := hP
  rw [← latticeMap_mul] at hc₀
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix.GeneralLinearGroup (Fin 2) K, latticeMap Q (stdLattice R K) = L := ⟨_, hc₀⟩

  have hfix : latticeMap (Q⁻¹ * (scalarGL c * h) * Q) (stdLattice R K) = stdLattice R K := by
    rw [latticeMap_mul, latticeMap_mul, hQ, latticeMap_mul, hc, ← hQ, latticeMap_inv_latticeMap]
  obtain ⟨M, hM⟩ := (latticeMap_stdLattice_eq_iff_mem_range _).mp hfix

  have hdetM : algebraMap R K ((Matrix.GeneralLinearGroup.det M : Rˣ) : R) = (c : K) ^ 2 * algebraMap R K d := by
    have hQQ : ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        (Q : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
        Matrix.det_one]
    have h1 : ((Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) M : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).det = (c : K) ^ 2 * algebraMap R K d := by
      rw [hM, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, scalarGL_coe, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
        hdet, mul_one]
      calc _ = ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
            (Q : Matrix (Fin 2) (Fin 2) K).det * ((c : K) ^ 2 * algebraMap R K d) := by ring
        _ = (c : K) ^ 2 * algebraMap R K d := by rw [hQQ, one_mul]
    rw [← h1]
    show algebraMap R K (M : Matrix (Fin 2) (Fin 2) R).det = _
    rw [RingHom.map_det]; rfl

  obtain ⟨ud, hud⟩ := hd
  have hc2 : (c : K) ^ 2 = algebraMap R K ((Matrix.GeneralLinearGroup.det M : Rˣ) * ud⁻¹ : Rˣ) := by
    rw [Units.val_mul, map_mul, hdetM, ← hud, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (x := (c : K)) (n := 2)
    two_pos (by rw [hc2]; exact isIntegral_algebraMap)
  have hru : IsUnit r := by
    have : r ^ 2 = ((Matrix.GeneralLinearGroup.det M : Rˣ) * ud⁻¹ : Rˣ) :=
      IsFractionRing.injective R K (by rw [map_pow, hr, hc2])
    exact isUnit_of_mul_isUnit_left (by rw [← pow_two, this]; exact Units.isUnit _)
  have hcL : latticeMap (scalarGL c) (latticeMap h L) = latticeMap h L :=
    latticeMap_scalarGL_eq_self_of_isUnit hru hr.symm _
  rw [← hcL, hc]

end DVR

end VAN3

namespace VAN3

section Main

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem stable_of_isFixedVertex {ϖ : R} (hϖ : Irreducible ϖ) (Y : Matrix (Fin 2) (Fin 2) R) {i : ℕ} (hi : 1 ≤ i)
    (h : Matrix.GeneralLinearGroup (Fin 2) K) (hh : (h : Matrix (Fin 2) (Fin 2) K) = 1 + T ϖ Y i)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (hfix : IsFixedVertex h (Vertex.mk R K L hL)) :
    ∀ x ∈ L, T (K := K) ϖ Y i *ᵥ x ∈ L := by
  have heq : latticeMap h L = L :=
    latticeMap_eq_of_homothetic (isUnit_dOne hϖ Y hi) (by rw [hh, det_one_add_T]) hL (isFixedVertex_mk_iff.mp hfix)
  intro x hx
  have hx' : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ x ∈ L := by
    rw [← heq]; exact mem_latticeMap.mpr ⟨x, hx, rfl⟩
  rw [hh, Matrix.add_mulVec, Matrix.one_mulVec] at hx'
  simpa using L.sub_mem hx' hx

end Main

end VAN3

open VAN3 in
theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Y : Matrix (Fin 2) (Fin 2) R) (j : ℕ) (hj : 1 ≤ j)
    (g g' : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = 1 + algebraMap R K ϖ ^ j • Y.map (algebraMap R K))
    (hg' : (g' : Matrix (Fin 2) (Fin 2) K) = 1 + algebraMap R K ϖ ^ (j + 1) • Y.map (algebraMap R K)) :
    LT.LatticeTree.fixedVertexSet (R := R) g' =
      {x | ∃ y ∈ LT.LatticeTree.fixedVertexSet (R := R) g,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 y x} := by
  have hgT : (g : Matrix (Fin 2) (Fin 2) K) = 1 + T ϖ Y j := hg
  have hg'T : (g' : Matrix (Fin 2) (Fin 2) K) = 1 + T ϖ Y (j + 1) := hg'

  let Tl : (Fin 2 → K) →ₗ[R] (Fin 2 → K) := (Matrix.mulVecLin (T (K := K) ϖ Y j)).restrictScalars R
  have hTl : ∀ x, Tl x = T (K := K) ϖ Y j *ᵥ x := fun x => rfl
  ext v
  obtain ⟨⟨M₀, hM₀⟩, rfl⟩ := Quotient.exists_rep v
  change IsFixedVertex g' (Vertex.mk R K M₀ hM₀) ↔
    ∃ y ∈ fixedVertexSet (R := R) g, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 y (Vertex.mk R K M₀ hM₀)
  constructor
  · intro hv
    have hst := stable_of_isFixedVertex hϖ Y (by omega) g' hg'T hM₀ hv

    have hL'full : IsFullLattice (M₀ ⊔ M₀.map Tl) := by
      refine ⟨hM₀.1.sup (hM₀.1.map _), ?_⟩
      rw [eq_top_iff, ← hM₀.2]
      exact Submodule.span_mono fun x hx => Submodule.mem_sup_left hx
    have hL'T : ∀ x ∈ M₀ ⊔ M₀.map Tl, T (K := K) ϖ Y j *ᵥ x ∈ M₀ ⊔ M₀.map Tl := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hb
      rw [Matrix.mulVec_add, hTl]
      exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨a, ha, rfl⟩))
        (T_mulVec_T_mulVec_mem ϖ Y j _ (Submodule.mem_sup_left hm)
          (Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨m, hm, rfl⟩)))
    refine ⟨Vertex.mk R K (M₀ ⊔ M₀.map Tl) hL'full, ?_, ?_⟩
    · exact isFixedVertex_mk_of_latticeMap_eq (latticeMap_eq_of_stable hϖ Y hj g hgT _ hL'T)
    · refine ⟨M₀ ⊔ M₀.map Tl, M₀, hL'full, hM₀, rfl, rfl, ?_, le_sup_left⟩
      intro v hv
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hb
      rw [pow_one, unitOfNeZero_coe, smul_add, hTl, ← Matrix.smul_mulVec, ← T_succ]
      exact M₀.add_mem (algebraMap_smul_mem M₀ ha ϖ) (hst m hm)
  · rintro ⟨y, hy, L₁, M₁, hL₁, hM₁, rfl, hM₁eq, hlow, hup⟩
    rw [← hM₁eq]
    have hst := stable_of_isFixedVertex hϖ Y hj g hgT hL₁ hy
    refine isFixedVertex_mk_of_latticeMap_eq (latticeMap_eq_of_stable hϖ Y (by omega) g' hg'T M₁ ?_)
    intro m hm
    rw [T_succ, Matrix.smul_mulVec]
    apply hlow
    rw [pow_one]
    exact mem_latticeMap_scalarGL.mpr ⟨_, hst m (hup hm), by rw [unitOfNeZero_coe]⟩

end S_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul
end P2MW
export P2MW.S_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul (solution)
