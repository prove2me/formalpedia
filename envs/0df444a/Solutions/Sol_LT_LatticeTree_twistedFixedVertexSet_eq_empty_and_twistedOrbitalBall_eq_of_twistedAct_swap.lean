-- Prove2me | solution 1 for LT.LatticeTree.twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1e04ef40-50c2-5eb4-bb4b-71c55cb81201

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin
import Theorems.Thm_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap

set_option autoImplicit false

namespace TreeMetric

open LT.LatticeTree

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

open LT.LatticeTree

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

namespace IsWithin

private theorem _root_.TreeMetric.IsWithin.act {c : Kˣ} {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin 2) K) {v w : Vertex R K}
    (h : Vertex.IsWithin c n v w) : Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeMap g L, latticeMap g M, hL.map g, hM.map g, rfl, rfl,
    (latticeWithin_latticeMap_iff c n g L M).2 hLM⟩

end IsWithin
p2m_export "TreeMetric" "IsWithin.act"

private theorem isWithin_act_iff (c : Kˣ) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (v w : Vertex R K) :
    Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) ↔ Vertex.IsWithin c n v w :=
  ⟨fun h => by simpa only [act_inv_act] using IsWithin.act g⁻¹ h, fun h => IsWithin.act g h⟩

namespace IsWithin

private theorem _root_.TreeMetric.IsWithin.galAct {c : Kˣ} {n : ℕ} (σ : IntegralAut R K) {v w : Vertex R K}
    (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin (σ.unitMap c) n (Vertex.galAct σ v) (Vertex.galAct σ w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeGal σ L, latticeGal σ M, hL.gal σ, hM.gal σ, rfl, rfl,
    (latticeWithin_latticeGal_iff σ c n L M).2 hLM⟩

end IsWithin
p2m_export "TreeMetric" "IsWithin.galAct"
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

open LT.LatticeTree

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

private theorem isInteger_pow_mul_of_le {ϖ : R} {x : K} {k l : ℕ} (hkl : k ≤ l)
    (h : IsLocalization.IsInteger R (algebraMap R K ϖ ^ k * x)) :
    IsLocalization.IsInteger R (algebraMap R K ϖ ^ l * x) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [pow_add, mul_comm (algebraMap R K ϖ ^ k), mul_assoc]
  exact IsLocalization.isInteger_mul ⟨ϖ ^ j, map_pow _ _ _⟩ h

variable [IsFractionRing R K]

private theorem latticeMap_scalarGL_unitOfNeZero_le {ϖ : R} (hϖ : ϖ ≠ 0) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) L ≤ L := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.1 hx
  rw [unitOfNeZero_coe, algebraMap_smul]
  exact L.smul_mem ϖ hw

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

end TreeMetric

section EdgeDisplacement

private def Ex
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) (v w : LT.LatticeTree.Vertex R K) : Prop :=
  LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w ∧
    ∀ m < n, ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m v w

private theorem isWithin_mono'
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {m n : ℕ} (hmn : m ≤ n) {v w : LT.LatticeTree.Vertex R K}
    (h : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m v w) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w :=
  h.mono (TreeMetric.latticeMap_scalarGL_unitOfNeZero_le hϖ.ne_zero) hmn

private theorem isWithin_trans'
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {n m : ℕ} {v w x : LT.LatticeTree.Vertex R K}
    (h₁ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w)
    (h₂ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m w x) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + m) v x :=
  LT.LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin R K ϖ hϖ v w x n m h₁ h₂

open LT.LatticeTree.Vertex in

private theorem exists_step
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {v x : LT.LatticeTree.Vertex R K} {n : ℕ}
    (h : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v x)
    (h' : ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v x) :
    ∃ y : LT.LatticeTree.Vertex R K,
      LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x y ∧
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v y ∧
          ∀ z : LT.LatticeTree.Vertex R K,
            LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x z → z ≠ x → z ≠ y →
              ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v z :=
  exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin R K ϖ hϖ v x n h h'

private theorem Ex.unique
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {m n : ℕ} {v w : LT.LatticeTree.Vertex R K} (hm : Ex hϖ m v w) (hn : Ex hϖ n v w) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact (hn.2 m h hm.1).elim
  · exact h
  · exact (hm.2 n h hn.1).elim

private theorem Ex.zero_iff
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {v w : LT.LatticeTree.Vertex R K} : Ex hϖ 0 v w ↔ v = w := by
  constructor
  · intro h
    exact (LT.LatticeTree.Vertex.isWithin_zero_iff _ v w).1 h.1
  · intro h
    exact ⟨(LT.LatticeTree.Vertex.isWithin_zero_iff _ v w).2 h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

private theorem Ex.twistedAct
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : LT.LatticeTree.IntegralAut R K) {n : ℕ}
    {v w : LT.LatticeTree.Vertex R K}
    (h : Ex hϖ n v w) :
    Ex hϖ n (LT.LatticeTree.Vertex.twistedAct δ σ v) (LT.LatticeTree.Vertex.twistedAct δ σ w) :=
  ⟨(TreeMetric.isWithin_twistedAct_iff hϖ δ σ n v w).2 h.1,
    fun m hm hvw => h.2 m hm ((TreeMetric.isWithin_twistedAct_iff hϖ δ σ m v w).1 hvw)⟩

private theorem exists_ex
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    (v w : LT.LatticeTree.Vertex R K) : ∃ n : ℕ, Ex hϖ n v w :=
  TreeMetric.exists_exact hϖ v w

private theorem isWithin_iff_exists_ex
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) (v w : LT.LatticeTree.Vertex R K) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w ↔ ∃ k ≤ n, Ex hϖ k v w :=
  TreeMetric.isWithin_iff_exists_le hϖ n v w

private theorem ex_of_step
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {n : ℕ} {p w y : LT.LatticeTree.Vertex R K} (hw : Ex hϖ (n + 1) p w)
    (hwy : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 w y)
    (hy : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n p y) : Ex hϖ n p y :=
  ⟨hy, fun i hi hiy => hw.2 (i + 1) (by omega) (isWithin_trans' hϖ hiy hwy.symm)⟩

private theorem exists_step_of_side
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {x₀ x₁ : LT.LatticeTree.Vertex R K}
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    {j : ℕ} {w : LT.LatticeTree.Vertex R K} (hw₀ : Ex hϖ (j + 1) x₀ w)
    (hw₁ : Ex hϖ (j + 1 + 1) x₁ w) :
    ∃ y : LT.LatticeTree.Vertex R K,
      LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 w y ∧
        Ex hϖ j x₀ y ∧ Ex hϖ (j + 1) x₁ y := by
  obtain ⟨y, hwy, hy, -⟩ := exists_step hϖ hw₀.1 (hw₀.2 j (Nat.lt_succ_self j))
  refine ⟨y, hwy, ex_of_step hϖ hw₀ hwy hy, ex_of_step hϖ hw₁ hwy ?_⟩
  have h := isWithin_trans' hϖ hadj.symm hy
  rwa [Nat.add_comm] at h

private theorem ex_add_one_of_sides
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {x₀ x₁ : LT.LatticeTree.Vertex R K}
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁) (j : ℕ) :
    ∀ (w u : LT.LatticeTree.Vertex R K) (k : ℕ), Ex hϖ j x₀ w → Ex hϖ (j + 1) x₁ w → Ex hϖ k x₁ u →
      Ex hϖ (k + 1) x₀ u → Ex hϖ (j + k + 1) w u := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases j with _ | j
  · intro w u k hw₀ _ _ hu₀
    obtain rfl : x₀ = w := (Ex.zero_iff hϖ).1 hw₀
    have e : 0 + k + 1 = k + 1 := by omega
    rw [e]
    exact hu₀
  · intro w u k hw₀ hw₁ hu₁ hu₀
    obtain ⟨y, hwy, hy₀, hy₁⟩ := exists_step_of_side hϖ hadj hw₀ hw₁
    have hyu : Ex hϖ (j + k + 1) y u := ih j (Nat.lt_succ_self j) y u k hy₀ hy₁ hu₁ hu₀

    have hexists : ∃ y₂ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 y y₂ ∧ y₂ ≠ w ∧
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (j + k) u y₂ := by
      rcases j with _ | j
      · obtain rfl : x₀ = y := (Ex.zero_iff hϖ).1 hy₀
        refine ⟨x₁, hadj, ?_, ?_⟩
        · rintro rfl
          have := Ex.unique hϖ hw₁ ((Ex.zero_iff hϖ).2 rfl)
          omega
        · have h := hu₁.1.symm
          rwa [Nat.zero_add]
      · obtain ⟨y₂, hyy₂, hy₂₀, hy₂₁⟩ := exists_step_of_side hϖ hadj hy₀ hy₁
        have hy₂u : Ex hϖ (j + k + 1) y₂ u := ih j (by omega) y₂ u k hy₂₀ hy₂₁ hu₁ hu₀
        refine ⟨y₂, hyy₂, ?_, ?_⟩
        · rintro rfl
          have := Ex.unique hϖ hw₀ hy₂₀
          omega
        · have h := hy₂u.1.symm
          have e : j + k + 1 = j + 1 + k := by omega
          rw [e] at h
          exact h
    obtain ⟨y₂, hyy₂, hy₂w, hy₂u⟩ := hexists
    obtain ⟨ys, -, -, hother⟩ :=
      exists_step hϖ hyu.1.symm (fun h => hyu.2 (j + k) (Nat.lt_succ_self _) h.symm)
    have hy₂s : y₂ = ys := by
      by_contra hne
      have hy₂y : y₂ ≠ y := by
        rintro rfl
        exact hyu.2 (j + k) (Nat.lt_succ_self _) hy₂u.symm
      exact hother y₂ hyy₂ hy₂y hne (isWithin_mono' hϖ (Nat.le_succ _) hy₂u)
    subst hy₂s
    have hwy' : w ≠ y := by
      rintro rfl
      have := Ex.unique hϖ hw₀ hy₀
      omega
    have hnot := hother w hwy.symm hwy' (Ne.symm hy₂w)
    refine ⟨?_, fun i hi hiw => hnot (isWithin_mono' hϖ (by omega) hiw.symm)⟩
    have h := isWithin_trans' hϖ hwy hyu.1
    have e : 1 + (j + k + 1) = j + 1 + k + 1 := by omega
    rw [e] at h
    exact h

private theorem not_ex_both
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {x₀ x₁ : LT.LatticeTree.Vertex R K}
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (n : ℕ) :
    ∀ w : LT.LatticeTree.Vertex R K,
      Ex hϖ n x₀ w → Ex hϖ n x₁ w → False := by
  induction n with
  | zero =>
    intro w h₀ h₁
    exact hne (((Ex.zero_iff hϖ).1 h₀).trans ((Ex.zero_iff hϖ).1 h₁).symm)
  | succ n ih =>
    intro w h₀ h₁
    obtain ⟨y, hwy, hy₀, -⟩ := exists_step hϖ h₀.1 (h₀.2 n (Nat.lt_succ_self n))
    obtain ⟨y', -, hy₁', hother⟩ := exists_step hϖ h₁.1 (h₁.2 n (Nat.lt_succ_self n))
    have hy₁ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) x₁ y := by
      have h := isWithin_trans' hϖ hadj.symm hy₀
      rwa [Nat.add_comm] at h
    have hyw : y ≠ w := by
      rintro rfl
      exact h₀.2 n (Nat.lt_succ_self n) hy₀
    have hyy' : y = y' := by
      by_contra h
      exact hother y hwy hyw h hy₁
    subst hyy'
    exact ih y (ex_of_step hϖ h₀ hwy hy₀) (ex_of_step hϖ h₁ hwy hy₁')

private theorem exists_side
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    {x₀ x₁ : LT.LatticeTree.Vertex R K}
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (w : LT.LatticeTree.Vertex R K) :
    (∃ j : ℕ, Ex hϖ j x₀ w ∧ Ex hϖ (j + 1) x₁ w) ∨
      ∃ j : ℕ, Ex hϖ j x₁ w ∧ Ex hϖ (j + 1) x₀ w := by
  obtain ⟨d₀, hd₀⟩ := exists_ex hϖ x₀ w
  obtain ⟨d₁, hd₁⟩ := exists_ex hϖ x₁ w
  have h₁le : d₁ ≤ 1 + d₀ := by
    obtain ⟨k, hk, hkw⟩ := (isWithin_iff_exists_ex hϖ _ _ _).1 (isWithin_trans' hϖ hadj.symm hd₀.1)
    have := Ex.unique hϖ hkw hd₁
    omega
  have h₀le : d₀ ≤ 1 + d₁ := by
    obtain ⟨k, hk, hkw⟩ := (isWithin_iff_exists_ex hϖ _ _ _).1 (isWithin_trans' hϖ hadj hd₁.1)
    have := Ex.unique hϖ hkw hd₀
    omega
  have hd : d₀ ≠ d₁ := by
    rintro rfl
    exact not_ex_both hϖ hadj hne d₀ w hd₀ hd₁
  rcases Nat.lt_or_gt_of_ne hd with hlt | hgt
  · obtain rfl : d₁ = d₀ + 1 := by omega
    exact Or.inl ⟨d₀, hd₀, hd₁⟩
  · obtain rfl : d₀ = d₁ + 1 := by omega
    exact Or.inr ⟨d₁, hd₁, hd₀⟩

private theorem ex_twistedAct_of_side
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : LT.LatticeTree.IntegralAut R K) {x₀ x₁ : LT.LatticeTree.Vertex R K}
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (h₀ : LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁) (h₁ : LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀) (j : ℕ)
    (w : LT.LatticeTree.Vertex R K)
    (hw₀ : Ex hϖ j x₀ w) (hw₁ : Ex hϖ (j + 1) x₁ w) :
    Ex hϖ (2 * j + 1) w (LT.LatticeTree.Vertex.twistedAct δ σ w) := by
  have hfw₁ : Ex hϖ j x₁ (LT.LatticeTree.Vertex.twistedAct δ σ w) := by
    have h := Ex.twistedAct hϖ δ σ hw₀
    rwa [h₀] at h
  have hfw₀ : Ex hϖ (j + 1) x₀ (LT.LatticeTree.Vertex.twistedAct δ σ w) := by
    have h := Ex.twistedAct hϖ δ σ hw₁
    rwa [h₁] at h
  have h := ex_add_one_of_sides hϖ hadj j w (LT.LatticeTree.Vertex.twistedAct δ σ w) j hw₀ hw₁ hfw₁ hfw₀
  have e : j + j + 1 = 2 * j + 1 := by omega
  rw [e] at h
  exact h

end EdgeDisplacement

open LT.LatticeTree in

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (h₀ : LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁)
    (h₁ : LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀) (m : ℕ) :
    LT.LatticeTree.twistedFixedVertexSet δ σ = ∅ ∧
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m + 2) δ σ =
      LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
          (2 * m + 1) δ σ ∧
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m + 1) δ σ =
      {x : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m x₀ x ∨
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m x₁ x} := by

  have key : ∀ x : Vertex R K, ∃ j : ℕ, Ex hϖ (2 * j + 1) x (Vertex.twistedAct δ σ x) ∧
      ∀ n : ℕ, (Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n x₀ x ∨
        Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n x₁ x) ↔ j ≤ n := by
    intro x
    rcases exists_side hϖ hadj hne x with ⟨j, hj₀, hj₁⟩ | ⟨j, hj₁, hj₀⟩
    · refine ⟨j, ex_twistedAct_of_side hϖ δ σ hadj h₀ h₁ j x hj₀ hj₁, fun n => ?_⟩
      rw [isWithin_iff_exists_ex hϖ n x₀ x, isWithin_iff_exists_ex hϖ n x₁ x]
      constructor
      · rintro (⟨k, hk, hkx⟩ | ⟨k, hk, hkx⟩)
        · have := Ex.unique hϖ hkx hj₀
          omega
        · have := Ex.unique hϖ hkx hj₁
          omega
      · intro hjn
        exact Or.inl ⟨j, hjn, hj₀⟩
    · refine ⟨j, ex_twistedAct_of_side hϖ δ σ hadj.symm h₁ h₀ j x hj₁ hj₀, fun n => ?_⟩
      rw [isWithin_iff_exists_ex hϖ n x₀ x, isWithin_iff_exists_ex hϖ n x₁ x]
      constructor
      · rintro (⟨k, hk, hkx⟩ | ⟨k, hk, hkx⟩)
        · have := Ex.unique hϖ hkx hj₀
          omega
        · have := Ex.unique hϖ hkx hj₁
          omega
      · intro hjn
        exact Or.inr ⟨j, hjn, hj₁⟩
  refine ⟨?_, ?_, ?_⟩
  · refine Set.subset_empty_iff.1 fun x hx => ?_
    rw [mem_twistedFixedVertexSet] at hx
    obtain ⟨j, hj, -⟩ := key x
    rw [hx] at hj
    have := Ex.unique hϖ hj ((Ex.zero_iff hϖ).2 rfl)
    omega
  · ext x
    obtain ⟨j, hj, -⟩ := key x
    rw [mem_twistedOrbitalBall, mem_twistedOrbitalBall, isWithin_iff_exists_ex hϖ, isWithin_iff_exists_ex hϖ]
    constructor
    · rintro ⟨k, hk, hkx⟩
      have := Ex.unique hϖ hkx hj
      exact ⟨k, by omega, hkx⟩
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, by omega, hkx⟩
  · ext x
    obtain ⟨j, hj, hcover⟩ := key x
    rw [mem_twistedOrbitalBall, Set.mem_setOf_eq, hcover m, isWithin_iff_exists_ex hϖ]
    constructor
    · rintro ⟨k, hk, hkx⟩
      have := Ex.unique hϖ hkx hj
      omega
    · intro hjm
      exact ⟨2 * j + 1, by omega, hj⟩

end S_LT_LatticeTree_twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap
end P2MW
export P2MW.S_LT_LatticeTree_twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap (solution)
