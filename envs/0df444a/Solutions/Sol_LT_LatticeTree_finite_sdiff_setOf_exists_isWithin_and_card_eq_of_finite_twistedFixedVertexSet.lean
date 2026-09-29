-- Prove2me | solution 1 for LT.LatticeTree.finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3c35e1e0-771e-56f1-81dc-49ecfb613d99

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_finite_setOf_isWithin_and_card_eq
import Theorems.Thm_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet

set_option autoImplicit false

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.IntegralAut LatticeTree.twistedFixedVertexSet LatticeTree.exists_act_stdVertex_eq"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin Vertex.isWithin_zero_iff Vertex.isWithin_comm latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff stdLattice latticeMap mem_latticeMap latticeMap_mul latticeMap_mono isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_mul_comm Homothetic Homothetic.refl Homothetic.symm Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_one Vertex.act_mul unitOfNeZero unitOfNeZero_coe IntegralAut IntegralAut.unitMap_coe latticeGal latticeGal_symm_latticeGal Vertex.galAct latticeMap_scalarGL_eq_self_of_isUnit Vertex.twistedAct twistedFixedVertexSet mem_twistedFixedVertexSet finite_setOf_isWithin_and_card_eq Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin Vertex.isWithin_add_of_isWithin_of_isWithin exists_act_stdVertex_eq"
p2m_open "LT.LatticeTree LT"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem latticeMap_scalarGL_unitOfNeZero_le [IsFractionRing R K] {ϖ : R} (hϖ : ϖ ≠ 0)
    (L : Submodule R (Fin 2 → K)) : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) L ≤ L := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hx
  rw [scalarGL_mulVec, unitOfNeZero_coe, algebraMap_smul K ϖ w]
  exact L.smul_mem ϖ hw

private theorem IsWithin.succ [IsFractionRing R K] {ϖ : R} (hϖ : ϖ ≠ 0) {n : ℕ} {v w : Vertex R K}
    (h : Vertex.IsWithin (unitOfNeZero (K := K) hϖ) n v w) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ) (n + 1) v w :=
  h.mono (latticeMap_scalarGL_unitOfNeZero_le hϖ) (Nat.le_succ n)

private theorem setOf_isWithin_subset_succ [IsFractionRing R K] {ϖ : R} (hϖ : ϖ ≠ 0) (n : ℕ) (v : Vertex R K) :
    {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) n v w} ⊆
      {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) (n + 1) v w} :=
  fun _ hw => IsWithin.succ hϖ hw

private theorem finite_sdiff_and_natCard_sdiff_eq {α : Type*} {s t : Set α} (hst : s ⊆ t) (ht : t.Finite) :
    (t \ s).Finite ∧ Nat.card ↥(t \ s) = Nat.card ↥t - Nat.card ↥s :=
  ⟨ht.diff, by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_diff hst (ht.subset hst)]⟩

private theorem finite_sdiff_setOf_isWithin_and_natCard_eq [IsFractionRing R K] {ϖ : R} (hϖ : ϖ ≠ 0)
    (hball : ∀ (v : Vertex R K) (d : ℕ),
      {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) d v w}.Finite ∧
        Nat.card ↥{w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) d v w} =
          1 + ∑ i ∈ Finset.range d,
            (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ i)
    (v : Vertex R K) (r : ℕ) :
    ({w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) (r + 1) v w} \
        {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) r v w}).Finite ∧
      Nat.card ↥({w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) (r + 1) v w} \
          {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ) r v w}) =
        (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  obtain ⟨hfin, hcard⟩ :=
    finite_sdiff_and_natCard_sdiff_eq (setOf_isWithin_subset_succ hϖ r v) (hball v (r + 1)).1
  refine ⟨hfin, ?_⟩
  rw [hcard, (hball v (r + 1)).2, (hball v r).2, Finset.sum_range_succ, Nat.add_sub_add_left,
    Nat.add_sub_cancel_left]

end LT.LatticeTree

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.IntegralAut LatticeTree.twistedFixedVertexSet LatticeTree.exists_act_stdVertex_eq"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin Vertex.isWithin_zero_iff Vertex.isWithin_comm latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff stdLattice latticeMap mem_latticeMap latticeMap_mul latticeMap_mono isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_mul_comm Homothetic Homothetic.refl Homothetic.symm Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_one Vertex.act_mul unitOfNeZero unitOfNeZero_coe IntegralAut IntegralAut.unitMap_coe latticeGal latticeGal_symm_latticeGal Vertex.galAct latticeMap_scalarGL_eq_self_of_isUnit Vertex.twistedAct twistedFixedVertexSet mem_twistedFixedVertexSet finite_setOf_isWithin_and_card_eq Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin Vertex.isWithin_add_of_isWithin_of_isWithin exists_act_stdVertex_eq"
p2m_open "LT.LatticeTree LT"

p2m_open "LT.LatticeTree P2MW.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet.LT.LatticeTree"

section DistanceFacts

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

private theorem act_transitive (v : Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = v :=
  LT.LatticeTree.exists_act_stdVertex_eq R K v

end DistanceFacts

section Acts

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

private theorem act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g v) = v := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

private theorem act_act_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g (Vertex.act g⁻¹ v) = v := by
  rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

end Acts

section Invariance

p2m_open "LT.LatticeTree P2MW.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet.LT.LatticeTree"

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

namespace IsWithin

private theorem _root_.LT.LatticeTree.IsWithin.act {c : Kˣ} {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin 2) K) {v w : Vertex R K}
    (h : Vertex.IsWithin c n v w) : Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeMap g L, latticeMap g M, hL.map g, hM.map g, rfl, rfl,
    (latticeWithin_latticeMap_iff c n g L M).2 hLM⟩

end IsWithin
p2m_export "LT.LatticeTree" "IsWithin.act"

private theorem isWithin_act_iff (c : Kˣ) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (v w : Vertex R K) :
    Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) ↔ Vertex.IsWithin c n v w :=
  ⟨fun h => by simpa only [act_inv_act] using IsWithin.act g⁻¹ h, fun h => IsWithin.act g h⟩

namespace IsWithin

private theorem _root_.LT.LatticeTree.IsWithin.galAct {c : Kˣ} {n : ℕ} (σ : IntegralAut R K) {v w : Vertex R K}
    (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin (σ.unitMap c) n (Vertex.galAct σ v) (Vertex.galAct σ w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeGal σ L, latticeGal σ M, hL.gal σ, hM.gal σ, rfl, rfl,
    (latticeWithin_latticeGal_iff σ c n L M).2 hLM⟩

end IsWithin
p2m_export "LT.LatticeTree" "IsWithin.galAct"
private theorem galAct_symm_galAct (σ : IntegralAut R K) (v : Vertex R K) :
    Vertex.galAct σ.symm (Vertex.galAct σ v) = v := by
  induction v using Quotient.inductionOn with
  | h L =>
    change Vertex.mk R K (latticeGal σ.symm (latticeGal σ L.1)) _ = Vertex.mk R K L.1 L.2
    rw [Vertex.mk_eq_mk_iff, latticeGal_symm_latticeGal]
    exact Homothetic.refl L.1

private theorem latticeWithin_mul_iff (c : Kˣ) {e : Kˣ} {u : R} (hu : IsUnit u) (heu : (e : K) = algebraMap R K u)
    (n : ℕ) (L M : Submodule R (Fin 2 → K)) : LatticeWithin (c * e) n L M ↔ LatticeWithin c n L M := by
  have he : latticeMap (scalarGL (e ^ n)) L = L :=
    latticeMap_scalarGL_eq_self_of_isUnit (hu.pow n) (by rw [Units.val_pow_eq_pow_val, heu, map_pow]) L
  unfold LatticeWithin
  rw [mul_pow, scalarGL_mul, latticeMap_mul, he]

private theorem isWithin_congr_of_coe_eq_mul {c c' : Kˣ} {u : R} (hu : IsUnit u)
    (h : (c' : K) = (c : K) * algebraMap R K u) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin c' n v w ↔ Vertex.IsWithin c n v w := by
  have hc' : c' = c * (c⁻¹ * c') := by rw [mul_inv_cancel_left]
  have he : ((c⁻¹ * c' : Kˣ) : K) = algebraMap R K u := by
    rw [Units.val_mul, h, Units.val_inv_eq_inv_val, inv_mul_cancel_left₀ c.ne_zero]
  rw [hc']
  constructor
  · rintro ⟨L, M, hL, hM, rfl, rfl, hLM⟩
    exact ⟨L, M, hL, hM, rfl, rfl, (latticeWithin_mul_iff c hu he n L M).1 hLM⟩
  · rintro ⟨L, M, hL, hM, rfl, rfl, hLM⟩
    exact ⟨L, M, hL, hM, rfl, rfl, (latticeWithin_mul_iff c hu he n L M).2 hLM⟩

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

private theorem unitMap_unitOfNeZero_coe_eq (τ : IntegralAut R K) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ u : R, IsUnit u ∧
      ((τ.unitMap (unitOfNeZero (K := K) hϖ.ne_zero) : Kˣ) : K) =
        ((unitOfNeZero (K := K) hϖ.ne_zero : Kˣ) : K) * algebraMap R K u := by
  have hirr : Irreducible (τ.toBase ϖ) := (MulEquiv.irreducible_iff τ.toBase).2 hϖ
  have hass : Associated ϖ (τ.toBase ϖ) := IsDiscreteValuationRing.associated_of_irreducible R hϖ hirr
  obtain ⟨u, hu⟩ := hass
  refine ⟨u, u.isUnit, ?_⟩
  rw [IntegralAut.unitMap_coe, unitOfNeZero_coe, τ.commutes, ← hu, map_mul]

private theorem isWithin_unitMap_iff (τ : IntegralAut R K) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin (τ.unitMap (unitOfNeZero (K := K) hϖ.ne_zero)) n v w ↔
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w := by
  obtain ⟨u, hu, h⟩ := unitMap_unitOfNeZero_coe_eq τ hϖ
  exact isWithin_congr_of_coe_eq_mul hu h n v w

private theorem isWithin_galAct_iff {ϖ : R} (hϖ : Irreducible ϖ) (σ : IntegralAut R K) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (Vertex.galAct σ v) (Vertex.galAct σ w) ↔
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w := by
  constructor
  · intro h
    have h' := IsWithin.galAct σ.symm h
    rw [galAct_symm_galAct, galAct_symm_galAct, isWithin_unitMap_iff σ.symm hϖ] at h'
    exact h'
  · intro h
    exact (isWithin_unitMap_iff σ hϖ n _ _).1 (IsWithin.galAct σ h)

private theorem isWithin_twistedAct_iff {ϖ : R} (hϖ : Irreducible ϖ) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (Vertex.twistedAct δ σ v) (Vertex.twistedAct δ σ w) ↔
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w := by
  unfold Vertex.twistedAct
  rw [isWithin_act_iff, isWithin_galAct_iff hϖ]

end Invariance

section Exactness

p2m_open "LT.LatticeTree P2MW.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet.LT.LatticeTree"

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

private theorem isInteger_pow_mul_of_le {ϖ : R} {x : K} {k l : ℕ} (hkl : k ≤ l)
    (h : IsLocalization.IsInteger R (algebraMap R K ϖ ^ k * x)) :
    IsLocalization.IsInteger R (algebraMap R K ϖ ^ l * x) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [pow_add, mul_comm (algebraMap R K ϖ ^ k), mul_assoc]
  exact IsLocalization.isInteger_mul ⟨ϖ ^ j, map_pow _ _ _⟩ h

variable [IsFractionRing R K]

private theorem exact_unique {ϖ : R} (hϖ : ϖ ≠ 0) {m n : ℕ} {v w : Vertex R K}
    (hm : Vertex.IsWithin (unitOfNeZero (K := K) hϖ) m v w)
    (hm' : ∀ l < m, ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ) l v w)
    (hn : Vertex.IsWithin (unitOfNeZero (K := K) hϖ) n v w)
    (hn' : ∀ l < n, ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ) l v w) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact absurd hm (hn' m h)
  · exact h
  · exact absurd hn (hm' n h)

private theorem isWithin_iff_exists_le {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w ↔
      ∃ m ≤ n, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) m v w ∧
        ∀ l < m, ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) l v w := by
  classical
  constructor
  · intro h
    have hex : ∃ m : ℕ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) m v w := ⟨n, h⟩
    refine ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun l hl => Nat.find_min hex hl⟩
  · rintro ⟨m, hmn, hm, -⟩
    exact hm.mono (latticeMap_scalarGL_unitOfNeZero_le hϖ.ne_zero) hmn

variable [IsDomain R] [IsDiscreteValuationRing R]

private theorem exists_pow_mul_isInteger {ϖ : R} (hϖ : Irreducible ϖ) (x : K) :
    ∃ k : ℕ, IsLocalization.IsInteger R (algebraMap R K ϖ ^ k * x) := by
  obtain ⟨b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) x
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
  refine ⟨k, ?_⟩
  have h1 : algebraMap R K ϖ ^ k * x = ((u⁻¹ : Rˣ) : R) • ((b : R) • x) := by
    rw [smul_smul, hu, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow]
  rw [h1]
  exact IsLocalization.isInteger_smul hb

private theorem exists_pow_smul_isInteger {ϖ : R} (hϖ : Irreducible ϖ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ∃ k : ℕ, ∀ i j, IsLocalization.IsInteger R
      (((scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ k) * g : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) i j) := by
  have h : ∀ i j : Fin 2, ∃ k : ℕ, IsLocalization.IsInteger R
      (algebraMap R K ϖ ^ k * (g : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => exists_pow_mul_isInteger hϖ _
  choose f hf using h
  refine ⟨f 0 0 + f 0 1 + f 1 0 + f 1 1, fun i j => ?_⟩
  have hentry : ((scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (f 0 0 + f 0 1 + f 1 0 + f 1 1)) * g :
      Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
        algebraMap R K ϖ ^ (f 0 0 + f 0 1 + f 1 0 + f 1 1) * (g : Matrix (Fin 2) (Fin 2) K) i j := by
    rw [Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul,
      Units.val_pow_eq_pow_val, unitOfNeZero_coe]
  rw [hentry]
  refine isInteger_pow_mul_of_le ?_ (hf i j)
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;> omega

private theorem exists_latticeMap_scalarGL_pow_mul_le {ϖ : R} (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ∃ k : ℕ, latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ k)) (latticeMap g (stdLattice R K)) ≤
      stdLattice R K := by
  obtain ⟨k, hk⟩ := exists_pow_smul_isInteger hϖ g
  exact ⟨k, by simpa only [latticeMap_mul] using latticeMap_le_stdLattice_of_isInteger hk⟩

private theorem exists_isWithin_stdVertex_act {ϖ : R} (hϖ : Irreducible ϖ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ∃ n : ℕ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (stdVertex R K)
      (Vertex.act g (stdVertex R K)) := by
  obtain ⟨k, hk⟩ := exists_latticeMap_scalarGL_pow_mul_le hϖ g
  obtain ⟨j, hj⟩ := exists_latticeMap_scalarGL_pow_mul_le hϖ g⁻¹

  have hj' : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ j)) (stdLattice R K) ≤
      latticeMap g (stdLattice R K) := by
    have := latticeMap_mono g hj
    rwa [← latticeMap_mul, ← latticeMap_mul, ← scalarGL_mul_comm, mul_assoc, mul_inv_cancel, mul_one] at this
  refine ⟨k + j, stdLattice R K,
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ k)) (latticeMap g (stdLattice R K)),
    isFullLattice_stdLattice, ((isFullLattice_stdLattice).map g).map _, rfl, ?_, ?_, hk⟩
  · exact Vertex.mk_eq_mk_iff.2 (Homothetic.symm ⟨_, rfl⟩)
  · rw [pow_add, scalarGL_mul, latticeMap_mul]
    exact latticeMap_mono _ hj'

private theorem exists_isWithin {ϖ : R} (hϖ : Irreducible ϖ) (v w : Vertex R K) :
    ∃ n : ℕ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w := by
  obtain ⟨g, rfl⟩ := act_transitive v
  obtain ⟨h, hh⟩ := act_transitive (Vertex.act g⁻¹ w)
  obtain ⟨n, hn⟩ := exists_isWithin_stdVertex_act hϖ h
  refine ⟨n, ?_⟩
  have := IsWithin.act g hn
  rwa [hh, act_act_inv] at this

private theorem exists_exact {ϖ : R} (hϖ : Irreducible ϖ) (v w : Vertex R K) :
    ∃ n : ℕ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w ∧
      ∀ l < n, ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) l v w := by
  classical
  have hex := exists_isWithin hϖ v w
  exact ⟨Nat.find hex, Nat.find_spec hex, fun l hl => Nat.find_min hex hl⟩

end Exactness

end LT.LatticeTree

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.IntegralAut LatticeTree.twistedFixedVertexSet LatticeTree.exists_act_stdVertex_eq"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin Vertex.isWithin_zero_iff Vertex.isWithin_comm latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff stdLattice latticeMap mem_latticeMap latticeMap_mul latticeMap_mono isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_mul_comm Homothetic Homothetic.refl Homothetic.symm Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_one Vertex.act_mul unitOfNeZero unitOfNeZero_coe IntegralAut IntegralAut.unitMap_coe latticeGal latticeGal_symm_latticeGal Vertex.galAct latticeMap_scalarGL_eq_self_of_isUnit Vertex.twistedAct twistedFixedVertexSet mem_twistedFixedVertexSet finite_setOf_isWithin_and_card_eq Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin Vertex.isWithin_add_of_isWithin_of_isWithin exists_act_stdVertex_eq"
p2m_open "LT.LatticeTree LT"

private structure RegularTreeMetric {V : Type*} (d : V → V → ℕ) (q : ℕ) : Prop where
  symm : ∀ x y : V, d x y = d y x
  eq_zero_iff : ∀ x y : V, d x y = 0 ↔ x = y
  triangle : ∀ x y z : V, d x z ≤ d x y + d y z
  finite_adjacent : ∀ x : V, {y : V | d x y = 1}.Finite
  natCard_adjacent : ∀ x : V, Nat.card ↥{y : V | d x y = 1} = q + 1
  step_exists : ∀ {v w : V} {n : ℕ}, d v w = n + 1 → ∃ s : V, d w s = 1 ∧ d v s = n
  step_unique : ∀ {v w : V} {n : ℕ}, d v w = n + 1 →
    ∀ {s t : V}, d w s = 1 → d v s = n → d w t = 1 → d v t = n → s = t
  parity : ∀ {v w s : V} {n : ℕ}, d v w = n + 1 → d w s = 1 → d v s = n ∨ d v s = n + 2

variable {V : Type*} {d : V → V → ℕ} {q : ℕ}

private theorem RegularTreeMetric.d_self (h : RegularTreeMetric d q) (x : V) : d x x = 0 :=
  (h.eq_zero_iff x x).2 rfl

private theorem RegularTreeMetric.ne_of_d_eq_succ (h : RegularTreeMetric d q) {x y : V} {n : ℕ}
    (hxy : d x y = n + 1) : x ≠ y := fun hx => by
  rw [hx, h.d_self] at hxy
  exact Nat.succ_ne_zero n hxy.symm

private theorem RegularTreeMetric.d_le_succ_of_adjacent (h : RegularTreeMetric d q) {w s : V} (hws : d w s = 1)
    (v : V) : d v s ≤ d v w + 1 := by
  have := h.triangle v w s
  rwa [hws] at this

private theorem RegularTreeMetric.le_succ_d_of_adjacent (h : RegularTreeMetric d q) {w s : V} (hws : d w s = 1)
    (v : V) : d v w ≤ d v s + 1 := by
  have := h.triangle v s w
  rwa [h.symm s w, hws] at this

private theorem RegularTreeMetric.exists_step_far_side (h : RegularTreeMetric d q) {ℓ s x : V} {n : ℕ}
    (hℓs : d ℓ s = 1) (hx : d ℓ x = n + 1) (hsx : d s x = n + 2) :
    ∃ y : V, d x y = 1 ∧ d ℓ y = n ∧ d s y = n + 1 := by
  obtain ⟨y, hxy, hℓy⟩ := h.step_exists hx
  refine ⟨y, hxy, hℓy, ?_⟩
  rcases h.parity hsx hxy with hsy | hsy
  · exact hsy
  · exfalso
    have hle : d s y ≤ n + 1 := by
      have := h.triangle s ℓ y
      rw [h.symm s ℓ, hℓs, hℓy] at this
      omega
    omega

private theorem RegularTreeMetric.d_eq_add_of_far_side (h : RegularTreeMetric d q) {ℓ s f : V} (hℓs : d ℓ s = 1)
    (hfs : d f s + 1 = d f ℓ) :
    ∀ (n : ℕ) (x : V), d ℓ x = n → d s x = n + 1 → d f x = d f ℓ + n := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih x hx hsx
  cases n with
  | zero =>
    rw [h.eq_zero_iff] at hx
    rw [← hx, Nat.add_zero]
  | succ n =>
    obtain ⟨y, hxy, hℓy, hsy⟩ := h.exists_step_far_side hℓs hx hsx
    have hfy : d f y = d f ℓ + n := ih n (Nat.lt_succ_self n) y hℓy hsy
    have hyx : d y x = 1 := by rw [h.symm]; exact hxy
    have hfy' : d f y = (d f s + n) + 1 := by omega
    rcases h.parity hfy' hyx with hfx | hfx
    · exfalso

      cases n with
      | zero =>
        have hyℓ : y = ℓ := ((h.eq_zero_iff ℓ y).1 hℓy).symm
        subst hyℓ
        have hsx' : s = x := h.step_unique hfy' hℓs (by omega) hyx hfx
        subst hsx'
        rw [h.d_self] at hsx
        omega
      | succ m =>
        obtain ⟨z, hyz, hℓz, hsz⟩ := h.exists_step_far_side hℓs hℓy hsy
        have hfz : d f z = d f ℓ + m := ih m (by omega) z hℓz hsz
        have hzx : z = x := h.step_unique hfy' hyz (by omega) hyx hfx
        subst hzx
        omega
    · omega

private def farShell (d : V → V → ℕ) (ℓ s : V) (n : ℕ) : Set V := {x : V | d ℓ x = n ∧ d s x = n + 1}

private def farFibre (d : V → V → ℕ) (s y : V) (n : ℕ) : Set V := {z : V | d y z = 1 ∧ d s z = n + 2}

private theorem mem_farShell {ℓ s x : V} {n : ℕ} : x ∈ farShell d ℓ s n ↔ d ℓ x = n ∧ d s x = n + 1 := Iff.rfl

private theorem mem_farFibre {s y z : V} {n : ℕ} : z ∈ farFibre d s y n ↔ d y z = 1 ∧ d s z = n + 2 := Iff.rfl

private theorem RegularTreeMetric.farShell_zero (h : RegularTreeMetric d q) {ℓ s : V} (hℓs : d ℓ s = 1) :
    farShell d ℓ s 0 = {ℓ} := by
  ext x
  rw [mem_farShell, Set.mem_singleton_iff, h.eq_zero_iff]
  constructor
  · rintro ⟨hx, -⟩
    exact hx.symm
  · rintro rfl
    exact ⟨rfl, by rw [h.symm]; exact hℓs⟩

private theorem RegularTreeMetric.exists_farFibre_eq_diff (h : RegularTreeMetric d q) {s y : V} {n : ℕ}
    (hsy : d s y = n + 1) :
    ∃ t : V, t ∈ {z : V | d y z = 1} ∧ farFibre d s y n = {z : V | d y z = 1} \ {t} := by
  obtain ⟨t, hyt, hst⟩ := h.step_exists hsy
  refine ⟨t, hyt, ?_⟩
  ext z
  rw [mem_farFibre, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyz, hsz⟩
    refine ⟨hyz, fun hzt => ?_⟩
    rw [hzt, hst] at hsz
    omega
  · rintro ⟨hyz, hzt⟩
    refine ⟨hyz, ?_⟩
    rcases h.parity hsy hyz with hsz | hsz
    · exact absurd (h.step_unique hsy hyz hsz hyt hst) hzt
    · exact hsz

private theorem RegularTreeMetric.finite_farFibre_and_ncard_eq (h : RegularTreeMetric d q) {s y : V} {n : ℕ}
    (hsy : d s y = n + 1) : (farFibre d s y n).Finite ∧ (farFibre d s y n).ncard = q := by
  obtain ⟨t, ht, hfib⟩ := h.exists_farFibre_eq_diff hsy
  rw [hfib]
  refine ⟨(h.finite_adjacent y).diff, ?_⟩
  rw [Set.ncard_diff_singleton_of_mem ht, ← Nat.card_coe_set_eq, h.natCard_adjacent y, Nat.add_sub_cancel]

private theorem RegularTreeMetric.farShell_succ_eq (h : RegularTreeMetric d q) {ℓ s : V} (hℓs : d ℓ s = 1)
    (n : ℕ) : farShell d ℓ s (n + 1) = ⋃ y ∈ farShell d ℓ s n, farFibre d s y n := by
  ext x
  rw [Set.mem_iUnion₂]
  constructor
  · intro hx
    obtain ⟨hℓx, hsx⟩ := mem_farShell.1 hx
    obtain ⟨y, hxy, hℓy, hsy⟩ := h.exists_step_far_side hℓs hℓx hsx
    exact ⟨y, mem_farShell.2 ⟨hℓy, hsy⟩, mem_farFibre.2 ⟨by rw [h.symm]; exact hxy, hsx⟩⟩
  · rintro ⟨y, hy, hx⟩
    obtain ⟨hℓy, -⟩ := mem_farShell.1 hy
    obtain ⟨hyx, hsx⟩ := mem_farFibre.1 hx
    refine mem_farShell.2 ⟨?_, hsx⟩
    have h₁ := h.d_le_succ_of_adjacent hyx ℓ
    have h₂ := h.triangle s ℓ x
    rw [h.symm s ℓ, hℓs] at h₂
    omega

private theorem RegularTreeMetric.eq_of_mem_farFibre_of_mem_farFibre (h : RegularTreeMetric d q) {ℓ s : V}
    (hℓs : d ℓ s = 1) {n : ℕ} {y y' z : V} (hy : y ∈ farShell d ℓ s n) (hy' : y' ∈ farShell d ℓ s n)
    (hz : z ∈ farFibre d s y n) (hz' : z ∈ farFibre d s y' n) : y = y' := by
  obtain ⟨hℓy, -⟩ := mem_farShell.1 hy
  obtain ⟨hℓy', -⟩ := mem_farShell.1 hy'
  obtain ⟨hyz, hsz⟩ := mem_farFibre.1 hz
  obtain ⟨hy'z, -⟩ := mem_farFibre.1 hz'
  have hℓz : d ℓ z = n + 1 := by
    have h₁ := h.d_le_succ_of_adjacent hyz ℓ
    have h₂ := h.triangle s ℓ z
    rw [h.symm s ℓ, hℓs] at h₂
    omega
  exact h.step_unique hℓz (by rw [h.symm]; exact hyz) hℓy (by rw [h.symm]; exact hy'z) hℓy'

private theorem RegularTreeMetric.finite_farShell_and_ncard_eq (h : RegularTreeMetric d q) {ℓ s : V}
    (hℓs : d ℓ s = 1) (n : ℕ) : (farShell d ℓ s n).Finite ∧ (farShell d ℓ s n).ncard = q ^ n := by
  induction n with
  | zero =>
    rw [h.farShell_zero hℓs, pow_zero, Set.ncard_singleton]
    exact ⟨Set.finite_singleton ℓ, rfl⟩
  | succ n ih =>
    classical
    obtain ⟨hfin, hcard⟩ := ih
    have hfib : ∀ y : V, (farFibre d s y n).Finite := fun y =>
      (h.finite_adjacent y).subset fun _ hz => (mem_farFibre.1 hz).1
    have hunion : farShell d ℓ s (n + 1) = ↑(hfin.toFinset.biUnion fun y => (hfib y).toFinset) := by
      rw [h.farShell_succ_eq hℓs n, Finset.coe_biUnion]
      simp only [Set.Finite.coe_toFinset]
    have hdisj : (↑hfin.toFinset : Set V).PairwiseDisjoint fun y => (hfib y).toFinset := by
      intro y hy y' hy' hne
      refine Finset.disjoint_left.2 fun z hz hz' => hne ?_
      exact h.eq_of_mem_farFibre_of_mem_farFibre hℓs (hfin.mem_toFinset.1 (Finset.mem_coe.1 hy))
        (hfin.mem_toFinset.1 (Finset.mem_coe.1 hy')) ((hfib y).mem_toFinset.1 hz) ((hfib y').mem_toFinset.1 hz')
    have hconst : ∀ y ∈ hfin.toFinset, ((hfib y).toFinset).card = q := by
      intro y hy
      rw [← Set.ncard_eq_toFinset_card _ (hfib y)]
      exact (h.finite_farFibre_and_ncard_eq (mem_farShell.1 (hfin.mem_toFinset.1 hy)).2).2
    rw [hunion]
    refine ⟨Finset.finite_toSet _, ?_⟩
    rw [Set.ncard_coe_finset, Finset.card_biUnion hdisj, Finset.sum_const_nat hconst,
      ← Set.ncard_eq_toFinset_card _ hfin, hcard, pow_succ]

private def tube (d : V → V → ℕ) (F : Set V) (n : ℕ) : Set V := {x : V | ∃ f ∈ F, d f x ≤ n}

private theorem mem_tube {F : Set V} {n : ℕ} {x : V} : x ∈ tube d F n ↔ ∃ f ∈ F, d f x ≤ n := Iff.rfl

private def StepClosed (d : V → V → ℕ) (F : Set V) : Prop :=
  ∀ f ∈ F, ∀ g ∈ F, ∀ {n : ℕ}, d f g = n + 1 → ∀ {s : V}, d g s = 1 → d f s = n → s ∈ F

private theorem tube_singleton_subset (f₀ : V) (n : ℕ) : tube d {f₀} n ⊆ {x : V | d f₀ x ≤ n} := by
  intro x hx
  obtain ⟨f, hf, hfx⟩ := mem_tube.1 hx
  rw [Set.mem_singleton_iff] at hf
  rw [Set.mem_setOf_eq, ← hf]
  exact hfx

private theorem RegularTreeMetric.eq_of_mem_of_adjacent_of_forall_le (h : RegularTreeMetric d q) {F : Set V}
    {f₀ ℓ s₀ : V} {m : ℕ} (hmax : ∀ g ∈ F, d f₀ g ≤ d f₀ ℓ) (hℓ : d f₀ ℓ = m + 1) (hℓs₀ : d ℓ s₀ = 1)
    (hs₀ : d f₀ s₀ = m) {u : V} (hu : u ∈ F) (hℓu : d ℓ u = 1) : u = s₀ := by
  rcases h.parity hℓ hℓu with hfu | hfu
  · exact h.step_unique hℓ hℓu hfu hℓs₀ hs₀
  · have := hmax u hu
    omega

private theorem RegularTreeMetric.d_add_one_eq_of_mem_of_ne (h : RegularTreeMetric d q) {F : Set V}
    (hF : StepClosed d F) {f₀ ℓ s₀ : V} {m : ℕ} (hmax : ∀ g ∈ F, d f₀ g ≤ d f₀ ℓ) (hℓ : d f₀ ℓ = m + 1)
    (hℓF : ℓ ∈ F) (hℓs₀ : d ℓ s₀ = 1) (hs₀ : d f₀ s₀ = m) {f : V} (hf : f ∈ F) (hfℓ : f ≠ ℓ) :
    d f s₀ + 1 = d f ℓ := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, d f ℓ = j + 1 := by
    have hne : d f ℓ ≠ 0 := fun h0 => hfℓ ((h.eq_zero_iff f ℓ).1 h0)
    exact ⟨d f ℓ - 1, by omega⟩
  obtain ⟨t, hℓt, hft⟩ := h.step_exists hj
  have htF : t ∈ F := hF f hf ℓ hℓF hj hℓt hft
  have hts₀ : t = s₀ := h.eq_of_mem_of_adjacent_of_forall_le hmax hℓ hℓs₀ hs₀ htF hℓt
  rw [← hts₀, hft, hj]

private theorem RegularTreeMetric.stepClosed_diff_singleton (h : RegularTreeMetric d q) {F : Set V}
    (hF : StepClosed d F) {f₀ ℓ s₀ : V} {m : ℕ} (hmax : ∀ g ∈ F, d f₀ g ≤ d f₀ ℓ) (hℓ : d f₀ ℓ = m + 1)
    (hℓF : ℓ ∈ F) (hℓs₀ : d ℓ s₀ = 1) (hs₀ : d f₀ s₀ = m) : StepClosed d (F \ {ℓ}) := by
  intro f hf g hg n hfg s hgs hfs
  obtain ⟨hfF, hfℓ⟩ := (Set.mem_diff f).1 hf
  obtain ⟨hgF, -⟩ := (Set.mem_diff g).1 hg
  have hsF : s ∈ F := hF f hfF g hgF hfg hgs hfs
  refine (Set.mem_diff s).2 ⟨hsF, fun hsℓ => ?_⟩
  rw [Set.mem_singleton_iff] at hsℓ hfℓ
  rw [hsℓ] at hgs hfs
  have hgs₀ : g = s₀ :=
    h.eq_of_mem_of_adjacent_of_forall_le hmax hℓ hℓs₀ hs₀ hgF (by rw [h.symm]; exact hgs)
  have hstep := h.d_add_one_eq_of_mem_of_ne hF hmax hℓ hℓF hℓs₀ hs₀ hfF hfℓ
  rw [← hgs₀] at hstep
  omega

private theorem RegularTreeMetric.tube_eq_union_farShell (h : RegularTreeMetric d q) {F : Set V} {ℓ s₀ : V}
    (hℓF : ℓ ∈ F) (hℓs₀ : d ℓ s₀ = 1) (hs₀F : s₀ ∈ F) (n : ℕ) :
    tube d F n = tube d (F \ {ℓ}) n ∪ farShell d ℓ s₀ n := by
  have hs₀ℓ : s₀ ∉ ({ℓ} : Set V) := fun hs => h.ne_of_d_eq_succ (n := 0) hℓs₀ (Set.mem_singleton_iff.1 hs).symm
  ext x
  rw [Set.mem_union, mem_tube, mem_tube, mem_farShell]
  constructor
  · rintro ⟨f, hf, hfx⟩
    by_cases hfℓ : f = ℓ
    · rw [hfℓ] at hfx
      by_cases hsx : d s₀ x ≤ n
      · exact Or.inl ⟨s₀, (Set.mem_diff s₀).2 ⟨hs₀F, hs₀ℓ⟩, hsx⟩
      · right
        have h₁ := h.triangle s₀ ℓ x
        rw [h.symm s₀ ℓ, hℓs₀] at h₁
        exact ⟨by omega, by omega⟩
    · exact Or.inl ⟨f, (Set.mem_diff f).2 ⟨hf, fun hfl => hfℓ (Set.mem_singleton_iff.1 hfl)⟩, hfx⟩
  · rintro (⟨f, hf, hfx⟩ | ⟨hℓx, -⟩)
    · exact ⟨f, ((Set.mem_diff f).1 hf).1, hfx⟩
    · exact ⟨ℓ, hℓF, hℓx.le⟩

private theorem RegularTreeMetric.disjoint_tube_farShell (h : RegularTreeMetric d q) {F : Set V} (hF : StepClosed d F)
    {f₀ ℓ s₀ : V} {m : ℕ} (hmax : ∀ g ∈ F, d f₀ g ≤ d f₀ ℓ) (hℓ : d f₀ ℓ = m + 1) (hℓF : ℓ ∈ F) (hℓs₀ : d ℓ s₀ = 1)
    (hs₀ : d f₀ s₀ = m) (n : ℕ) : Disjoint (tube d (F \ {ℓ}) n) (farShell d ℓ s₀ n) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨f, hf, hfx⟩ := mem_tube.1 hx
  obtain ⟨hfF, hfℓ⟩ := (Set.mem_diff f).1 hf
  rw [Set.mem_singleton_iff] at hfℓ
  obtain ⟨hℓx, hs₀x⟩ := mem_farShell.1 hx'
  have hstep := h.d_add_one_eq_of_mem_of_ne hF hmax hℓ hℓF hℓs₀ hs₀ hfF hfℓ
  have hdiv := h.d_eq_add_of_far_side hℓs₀ hstep n x hℓx hs₀x
  omega

private theorem RegularTreeMetric.finite_tube_and_ncard_eq (h : RegularTreeMetric d q)
    (hball : ∀ (v : V) (n : ℕ), {x : V | d v x ≤ n}.Finite) (k : ℕ) :
    ∀ F : Set V, StepClosed d F → F.Finite → F.ncard = k + 1 → ∀ f₀ ∈ F, ∀ n : ℕ,
      (tube d F n).Finite ∧ (tube d F n).ncard = (tube d {f₀} n).ncard + k * q ^ n := by
  induction k with
  | zero =>
    intro F _ _ hcard f₀ hf₀ n
    obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 hcard
    rw [Set.mem_singleton_iff] at hf₀
    rw [hf₀, Nat.zero_mul, Nat.add_zero]
    exact ⟨(hball a n).subset (tube_singleton_subset a n), rfl⟩
  | succ k ih =>
    intro F hF hfin hcard f₀ hf₀ n
    obtain ⟨ℓ, hℓF, hmax⟩ := Set.exists_max_image F (d f₀) hfin ⟨f₀, hf₀⟩
    obtain ⟨m, hℓ⟩ : ∃ m : ℕ, d f₀ ℓ = m + 1 := by
      have h2 : 1 < F.ncard := by omega
      obtain ⟨g, hgF, hgf₀⟩ := Set.exists_ne_of_one_lt_ncard h2 f₀
      have hg : d f₀ g ≠ 0 := fun h0 => hgf₀ ((h.eq_zero_iff f₀ g).1 h0).symm
      have := hmax g hgF
      exact ⟨d f₀ ℓ - 1, by omega⟩
    obtain ⟨s₀, hℓs₀, hs₀⟩ := h.step_exists hℓ
    have hs₀F : s₀ ∈ F := hF f₀ hf₀ ℓ hℓF hℓ hℓs₀ hs₀
    have hf₀' : f₀ ∈ F \ {ℓ} :=
      (Set.mem_diff f₀).2 ⟨hf₀, fun hx => h.ne_of_d_eq_succ hℓ (Set.mem_singleton_iff.1 hx)⟩
    have hcard' : (F \ {ℓ}).ncard = k + 1 := by
      rw [Set.ncard_diff_singleton_of_mem hℓF, hcard, Nat.add_sub_cancel]
    obtain ⟨hfin', hcount'⟩ :=
      ih (F \ {ℓ}) (h.stepClosed_diff_singleton hF hmax hℓ hℓF hℓs₀ hs₀) hfin.diff hcard' f₀ hf₀' n
    obtain ⟨hlfin, hlcount⟩ := h.finite_farShell_and_ncard_eq hℓs₀ n
    rw [h.tube_eq_union_farShell hℓF hℓs₀ hs₀F n]
    refine ⟨hfin'.union hlfin, ?_⟩
    rw [Set.ncard_union_eq (h.disjoint_tube_farShell hF hmax hℓ hℓF hℓs₀ hs₀ n) hfin' hlfin, hcount', hlcount]
    ring

end LT.LatticeTree

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.IntegralAut LatticeTree.twistedFixedVertexSet LatticeTree.exists_act_stdVertex_eq"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin Vertex.isWithin_zero_iff Vertex.isWithin_comm latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff stdLattice latticeMap mem_latticeMap latticeMap_mul latticeMap_mono isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_mul_comm Homothetic Homothetic.refl Homothetic.symm Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_one Vertex.act_mul unitOfNeZero unitOfNeZero_coe IntegralAut IntegralAut.unitMap_coe latticeGal latticeGal_symm_latticeGal Vertex.galAct latticeMap_scalarGL_eq_self_of_isUnit Vertex.twistedAct twistedFixedVertexSet mem_twistedFixedVertexSet finite_setOf_isWithin_and_card_eq Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin Vertex.isWithin_add_of_isWithin_of_isWithin exists_act_stdVertex_eq"
p2m_open "LT.LatticeTree LT"

section DepthOnVertices

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]

private noncomputable def depth {ϖ : R} (hϖ : Irreducible ϖ) (v w : Vertex R K) : ℕ :=
  Classical.choose (exists_exact (K := K) hϖ v w)

private theorem depth_spec {ϖ : R} (hϖ : Irreducible ϖ) (v w : Vertex R K) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (depth hϖ v w) v w ∧
      ∀ l < depth hϖ v w, ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) l v w :=
  Classical.choose_spec (exists_exact (K := K) hϖ v w)

private theorem isWithin_iff_depth_le {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w ↔ depth hϖ v w ≤ n := by
  constructor
  · intro hn
    obtain ⟨m, hmn, hm, hm'⟩ := (isWithin_iff_exists_le hϖ n v w).1 hn
    rw [exact_unique hϖ.ne_zero (depth_spec hϖ v w).1 (depth_spec hϖ v w).2 hm hm']
    exact hmn
  · intro hle
    exact (depth_spec hϖ v w).1.mono (latticeMap_scalarGL_unitOfNeZero_le hϖ.ne_zero) hle

private theorem depth_comm {ϖ : R} (hϖ : Irreducible ϖ) (v w : Vertex R K) : depth hϖ v w = depth hϖ w v :=
  le_antisymm
    ((isWithin_iff_depth_le hϖ _ v w).1 ((Vertex.isWithin_comm _ _ w v).1 (depth_spec hϖ w v).1))
    ((isWithin_iff_depth_le hϖ _ w v).1 ((Vertex.isWithin_comm _ _ v w).1 (depth_spec hϖ v w).1))

private theorem depth_eq_zero_iff {ϖ : R} (hϖ : Irreducible ϖ) (v w : Vertex R K) : depth hϖ v w = 0 ↔ v = w := by
  rw [← Nat.le_zero, ← isWithin_iff_depth_le hϖ 0 v w, Vertex.isWithin_zero_iff]

private theorem depth_triangle {ϖ : R} (hϖ : Irreducible ϖ) (x y z : Vertex R K) :
    depth hϖ x z ≤ depth hϖ x y + depth hϖ y z :=
  (isWithin_iff_depth_le hϖ _ x z).1
    (Vertex.isWithin_add_of_isWithin_of_isWithin R K ϖ hϖ x y z _ _ (depth_spec hϖ x y).1 (depth_spec hϖ y z).1)

private theorem depth_twistedAct {ϖ : R} (hϖ : Irreducible ϖ) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (v w : Vertex R K) :
    depth hϖ (Vertex.twistedAct δ σ v) (Vertex.twistedAct δ σ w) = depth hϖ v w :=
  le_antisymm
    ((isWithin_iff_depth_le hϖ _ _ _).1 ((isWithin_twistedAct_iff hϖ δ σ _ v w).2 (depth_spec hϖ v w).1))
    ((isWithin_iff_depth_le hϖ _ v w).1 ((isWithin_twistedAct_iff hϖ δ σ _ v w).1 (depth_spec hϖ _ _).1))

private theorem exists_depth_eq_one_and_depth_eq_of_depth_eq_succ {ϖ : R} (hϖ : Irreducible ϖ) {v w : Vertex R K}
    {n : ℕ} (hvw : depth hϖ v w = n + 1) :
    ∃ y : Vertex R K, depth hϖ w y = 1 ∧ depth hϖ v y = n ∧
      ∀ z : Vertex R K, depth hϖ w z = 1 → z ≠ y → depth hϖ v z = n + 2 := by
  have h₁ : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v w :=
    (isWithin_iff_depth_le hϖ (n + 1) v w).2 hvw.le
  have h₂ : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w := fun h => by
    have := (isWithin_iff_depth_le hϖ n v w).1 h
    omega
  obtain ⟨y, hwy, hvy, hz⟩ :=
    Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
      R K ϖ hϖ v w n h₁ h₂
  have hwy' : depth hϖ w y ≤ 1 := (isWithin_iff_depth_le hϖ 1 w y).1 hwy
  have hvy' : depth hϖ v y ≤ n := (isWithin_iff_depth_le hϖ n v y).1 hvy
  have hvy_eq : depth hϖ v y = n := by
    have := depth_triangle hϖ v y w
    rw [depth_comm hϖ y w] at this
    omega
  have hwy_eq : depth hϖ w y = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hwy' with h0 | h1
    · rw [depth_eq_zero_iff] at h0
      rw [← h0] at hvy_eq
      omega
    · exact h1
  refine ⟨y, hwy_eq, hvy_eq, fun z hwz hzy => ?_⟩
  have hzw : z ≠ w := fun hzw => by
    rw [hzw, (depth_eq_zero_iff hϖ w w).2 rfl] at hwz
    omega
  have hnot := hz z ((isWithin_iff_depth_le hϖ 1 w z).2 hwz.le) hzw hzy
  have hge : ¬ depth hϖ v z ≤ n + 1 := fun hle => hnot ((isWithin_iff_depth_le hϖ (n + 1) v z).2 hle)
  have hle : depth hϖ v z ≤ n + 2 := by
    have := depth_triangle hϖ v w z
    omega
  omega

private theorem regularTreeMetric_depth {ϖ : R} (hϖ : Irreducible ϖ)
    (hball : ∀ (v : Vertex R K) (d : ℕ),
      {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d v w}.Finite ∧
        Nat.card ↥{w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d v w} =
          1 + ∑ i ∈ Finset.range d,
            (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ i) :
    RegularTreeMetric (depth (K := K) hϖ) (Nat.card (R ⧸ Ideal.span {ϖ})) := by
  have hadj : ∀ x : Vertex R K,
      {y : Vertex R K | depth hϖ x y = 1} =
        {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (0 + 1) x w} \
          {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 0 x w} := by
    intro x
    ext y
    rw [Set.mem_setOf_eq, Set.mem_diff, Set.mem_setOf_eq, Set.mem_setOf_eq, isWithin_iff_depth_le hϖ,
      isWithin_iff_depth_le hϖ]
    constructor
    · intro h
      omega
    · intro h
      omega
  exact
    { symm := depth_comm hϖ
      eq_zero_iff := depth_eq_zero_iff hϖ
      triangle := depth_triangle hϖ
      finite_adjacent := fun x => by
        rw [hadj x]
        exact (finite_sdiff_setOf_isWithin_and_natCard_eq hϖ.ne_zero hball x 0).1
      natCard_adjacent := fun x => by
        rw [hadj x, (finite_sdiff_setOf_isWithin_and_natCard_eq hϖ.ne_zero hball x 0).2, pow_zero, mul_one]
      step_exists := by
        intro v w n hvw
        obtain ⟨y, hwy, hvy, -⟩ := exists_depth_eq_one_and_depth_eq_of_depth_eq_succ hϖ hvw
        exact ⟨y, hwy, hvy⟩
      step_unique := by
        intro v w n hvw s t hws hvs hwt hvt
        obtain ⟨y, -, -, hz⟩ := exists_depth_eq_one_and_depth_eq_of_depth_eq_succ hϖ hvw
        have hs : s = y := by
          by_contra hsy
          have := hz s hws hsy
          omega
        have ht : t = y := by
          by_contra hty
          have := hz t hwt hty
          omega
        rw [hs, ht]
      parity := by
        intro v w s n hvw hws
        obtain ⟨y, -, hvy, hz⟩ := exists_depth_eq_one_and_depth_eq_of_depth_eq_succ hϖ hvw
        by_cases hsy : s = y
        · rw [hsy]
          exact Or.inl hvy
        · exact Or.inr (hz s hws hsy) }

private theorem stepClosed_twistedFixedVertexSet {ϖ : R} (hϖ : Irreducible ϖ) {q : ℕ}
    (hm : RegularTreeMetric (depth (K := K) hϖ) q) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : StepClosed (depth (K := K) hϖ) (twistedFixedVertexSet δ σ) := by
  intro f hf g hg n hfg s hgs hfs
  rw [mem_twistedFixedVertexSet] at hf hg ⊢
  have h₁ : depth hϖ g (Vertex.twistedAct δ σ s) = 1 := by
    have := depth_twistedAct hϖ δ σ g s
    rw [hg] at this
    rw [this]
    exact hgs
  have h₂ : depth hϖ f (Vertex.twistedAct δ σ s) = n := by
    have := depth_twistedAct hϖ δ σ f s
    rw [hf] at this
    rw [this]
    exact hfs
  exact hm.step_unique hfg h₁ h₂ hgs hfs

private theorem setOf_exists_isWithin_eq_tube {ϖ : R} (hϖ : Irreducible ϖ) (F : Set (Vertex R K)) (n : ℕ) :
    {x : Vertex R K | ∃ f ∈ F, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n f x} = tube (depth hϖ) F n := by
  ext x
  rw [Set.mem_setOf_eq, mem_tube]
  exact exists_congr fun f => and_congr_right fun _ => isWithin_iff_depth_le hϖ n f x

private theorem tube_singleton_eq {ϖ : R} (hϖ : Irreducible ϖ) (f₀ : Vertex R K) (n : ℕ) :
    tube (depth hϖ) {f₀} n = {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n f₀ w} := by
  ext x
  rw [mem_tube, Set.mem_setOf_eq, isWithin_iff_depth_le hϖ]
  constructor
  · rintro ⟨f, hf, hfx⟩
    rw [Set.mem_singleton_iff] at hf
    rw [← hf]
    exact hfx
  · intro hx
    exact ⟨f₀, Set.mem_singleton f₀, hx⟩

end DepthOnVertices

private theorem tube_subset_succ {V : Type*} (d : V → V → ℕ) (F : Set V) (n : ℕ) : tube d F n ⊆ tube d F (n + 1) :=
  fun _ hx =>
    let ⟨f, hf, hfx⟩ := mem_tube.1 hx
    mem_tube.2 ⟨f, hf, hfx.trans (Nat.le_succ n)⟩

private theorem tube_count_sub_eq (b p q k : ℕ) (hq : 1 ≤ q) :
    b + (q + 1) * p + k * (p * q) - (b + k * p) = ((k + 1) * (q - 1) + 2) * p := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

end LT.LatticeTree

open _root_.LT.LatticeTree _root_.P2MW.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet.LT.LatticeTree in

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.twistedFixedVertexSet δ σ).Finite)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) (r : ℕ) :
    ({x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (r + 1) f x} \
        {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r f x}).Finite ∧
    Nat.card ↥({x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (r + 1) f x} \
        {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r f x}) =
      (Nat.card ↥(LT.LatticeTree.twistedFixedVertexSet δ σ) * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
        Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  have hball := fun (v : Vertex R K) (d : ℕ) => finite_setOf_isWithin_and_card_eq R K ϖ hϖ v d
  have hm := regularTreeMetric_depth hϖ hball
  have hballs : ∀ (v : Vertex R K) (n : ℕ), {x : Vertex R K | depth hϖ v x ≤ n}.Finite := by
    intro v n
    have hset : {x : Vertex R K | depth hϖ v x ≤ n} =
        {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w} := by
      ext x
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, isWithin_iff_depth_le]
    rw [hset]
    exact (hball v n).1
  obtain ⟨f₀, hf₀⟩ := hne
  have hpos : 0 < (twistedFixedVertexSet δ σ).ncard := (Set.ncard_pos hfin).2 ⟨f₀, hf₀⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (twistedFixedVertexSet δ σ).ncard = k + 1 :=
    ⟨(twistedFixedVertexSet δ σ).ncard - 1, by omega⟩
  have hsc := stepClosed_twistedFixedVertexSet hϖ hm δ σ
  obtain ⟨hfin₁, hc₁⟩ := hm.finite_tube_and_ncard_eq hballs k _ hsc hfin hk f₀ hf₀ (r + 1)
  obtain ⟨-, hc₀⟩ := hm.finite_tube_and_ncard_eq hballs k _ hsc hfin hk f₀ hf₀ r
  have hb : {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (r + 1) f₀ w}.ncard =
      {w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) r f₀ w}.ncard +
        (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, (hball f₀ (r + 1)).2, (hball f₀ r).2, Finset.sum_range_succ]
    ring
  have hq : 1 ≤ Nat.card (R ⧸ Ideal.span {ϖ}) := Nat.card_pos
  rw [setOf_exists_isWithin_eq_tube hϖ, setOf_exists_isWithin_eq_tube hϖ]
  obtain ⟨hdfin, hdcard⟩ := finite_sdiff_and_natCard_sdiff_eq (tube_subset_succ (depth (K := K) hϖ) _ r) hfin₁
  refine ⟨hdfin, ?_⟩
  rw [hdcard, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hc₁, hc₀, tube_singleton_eq, tube_singleton_eq, hb,
    Nat.card_coe_set_eq, hk, pow_succ]
  exact tube_count_sub_eq _ _ _ k hq

end S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
end P2MW
export P2MW.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet (solution)
