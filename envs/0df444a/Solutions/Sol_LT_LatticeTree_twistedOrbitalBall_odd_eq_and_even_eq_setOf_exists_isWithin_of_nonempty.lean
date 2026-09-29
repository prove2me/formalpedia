-- Prove2me | solution 1 for LT.LatticeTree.twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/65a6ebae-99be-5ef1-b0d3-d5018d15d635

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin
import Theorems.Thm_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty

set_option autoImplicit false

namespace Fixed

open LT.LatticeTree

section DistanceFacts

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
variable [IsFractionRing R K]

private theorem isWithin_trans {ϖ : R} (hϖ : Irreducible ϖ) {m n : ℕ} {u v w : Vertex R K}
    (huv : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) m u v)
    (hvw : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (m + n) u w :=
  LT.LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin R K ϖ hϖ u v w m n huv hvw

variable [IsDomain R] [IsDiscreteValuationRing R]

private theorem act_transitive (v : Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = v :=
  LT.LatticeTree.exists_act_stdVertex_eq R K v

private theorem exists_step {ϖ : R} (hϖ : Irreducible ϖ) (p w : Vertex R K) (n : ℕ)
    (hw : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) p w)
    (hw' : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n p w) :
    ∃ a : Vertex R K, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 p a ∧ a ≠ p ∧
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n a w ∧
      ∀ b : Vertex R K, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 p b → b ≠ p → b ≠ a →
        ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) b w := by
  obtain ⟨y, hpy, hwy, hother⟩ :=
   LT.LatticeTree.Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
      R K ϖ hϖ w p n hw.symm (fun h => hw' h.symm)
  refine ⟨y, hpy, fun h => hw' (h ▸ hwy).symm, hwy.symm, fun b hpb hbp hby hbw => hother b hpb hbp hby hbw.symm⟩

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

private theorem _root_.Fixed.IsWithin.act {c : Kˣ} {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin 2) K) {v w : Vertex R K}
    (h : Vertex.IsWithin c n v w) : Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeMap g L, latticeMap g M, hL.map g, hM.map g, rfl, rfl,
    (latticeWithin_latticeMap_iff c n g L M).2 hLM⟩

end IsWithin
p2m_export "Fixed" "IsWithin.act"

private theorem isWithin_act_iff (c : Kˣ) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (v w : Vertex R K) :
    Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) ↔ Vertex.IsWithin c n v w :=
  ⟨fun h => by simpa only [act_inv_act] using IsWithin.act g⁻¹ h, fun h => IsWithin.act g h⟩

namespace IsWithin

private theorem _root_.Fixed.IsWithin.galAct {c : Kˣ} {n : ℕ} (σ : IntegralAut R K) {v w : Vertex R K}
    (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin (σ.unitMap c) n (Vertex.galAct σ v) (Vertex.galAct σ w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeGal σ L, latticeGal σ M, hL.gal σ, hM.gal σ, rfl, rfl,
    (latticeWithin_latticeGal_iff σ c n L M).2 hLM⟩

end IsWithin
p2m_export "Fixed" "IsWithin.galAct"
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

section More

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
variable [IsFractionRing R K]

private theorem IsWithin.mono' {ϖ : R} (hϖ : Irreducible ϖ) {m n : ℕ} (hmn : m ≤ n) {v w : Vertex R K}
    (h : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) m v w) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w :=
  h.mono (latticeMap_scalarGL_unitOfNeZero_le hϖ.ne_zero) hmn

variable [IsDomain R] [IsDiscreteValuationRing R]

private theorem twistedAct_injective {ϖ : R} (hϖ : Irreducible ϖ) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) {v w : Vertex R K} (h : Vertex.twistedAct δ σ v = Vertex.twistedAct δ σ w) : v = w := by
  have h0 : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 0 (Vertex.twistedAct δ σ v)
      (Vertex.twistedAct δ σ w) := (Vertex.isWithin_zero_iff _ _ _).2 h
  exact (Vertex.isWithin_zero_iff _ _ _).1 ((isWithin_twistedAct_iff hϖ δ σ 0 v w).1 h0)

end More

section Displacement

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} (hϖ : Irreducible ϖ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)

private theorem exists_nearest (hne : (twistedFixedVertexSet δ σ).Nonempty) (x : Vertex R K) :
    ∃ k : ℕ, (∃ f ∈ twistedFixedVertexSet δ σ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k f x) ∧
      ∀ j < k, ¬ ∃ f ∈ twistedFixedVertexSet δ σ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) j f x := by
  classical
  obtain ⟨f₀, hf₀⟩ := hne
  obtain ⟨n₀, hn₀⟩ := exists_isWithin hϖ f₀ x
  have hex : ∃ k : ℕ, ∃ f ∈ twistedFixedVertexSet δ σ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k f x :=
    ⟨n₀, f₀, hf₀, hn₀⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

private theorem isWithin_twistedAct_of_isWithin_fixed {k : ℕ} {f x : Vertex R K} (hf : f ∈ twistedFixedVertexSet δ σ)
    (hfx : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k f x) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * k) x (Vertex.twistedAct δ σ x) := by
  have h2 : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k f (Vertex.twistedAct δ σ x) := by
    have := (isWithin_twistedAct_iff hϖ δ σ k f x).2 hfx
    rwa [mem_twistedFixedVertexSet.1 hf] at this
  rw [two_mul]
  exact isWithin_trans hϖ hfx.symm h2

private theorem displacement_of_dist (n : ℕ) :
    ∀ (x f : Vertex R K), f ∈ twistedFixedVertexSet δ σ →
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) f x →
      (∀ f' ∈ twistedFixedVertexSet δ σ, ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n f' x) →
      ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * n + 1) x (Vertex.twistedAct δ σ x) := by
  induction n with
  | zero =>
    intro x f hf hfx hmin hx

    obtain ⟨a, -, -, ha0, hother⟩ := exists_step hϖ f x 0 hfx (hmin f hf)
    obtain rfl : a = x := (Vertex.isWithin_zero_iff _ _ _).1 ha0
    have hgx_nb : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 f (Vertex.twistedAct δ σ a) := by
      have := (isWithin_twistedAct_iff hϖ δ σ 1 f a).2 hfx
      rwa [mem_twistedFixedVertexSet.1 hf] at this
    have hane : a ≠ f := fun h => hmin f hf (h ▸ (Vertex.isWithin_zero_iff _ _ _).2 rfl)
    have hgx_ne_f : Vertex.twistedAct δ σ a ≠ f := fun h =>
      hane (twistedAct_injective hϖ δ σ (h.trans (mem_twistedFixedVertexSet.1 hf).symm))
    by_cases hga : Vertex.twistedAct δ σ a = a
    · exact hmin a hga ((Vertex.isWithin_zero_iff _ _ _).2 rfl)
    · exact (hother _ hgx_nb hgx_ne_f hga) (by simpa using hx.symm)
  | succ n ih =>
    intro x f hf hfx hmin hx

    obtain ⟨x', hxx', hx'x, hx'f, -⟩ :=
      exists_step hϖ x f (n + 1) hfx.symm (fun h => hmin f hf h.symm)
    have hmin' : ∀ f' ∈ twistedFixedVertexSet δ σ,
        ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n f' x' := fun f' hf' h =>
      hmin f' hf' (by simpa [add_comm] using isWithin_trans hϖ h hxx'.symm)
    have hfx' : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) f x' := hx'f.symm
    have hndisp := ih x' f hf hfx' hmin'
    have hdisp : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * n + 2) x' (Vertex.twistedAct δ σ x') :=
      isWithin_twistedAct_of_isWithin_fixed hϖ δ σ hf hfx' |> fun h => by simpa [Nat.mul_succ] using h

    obtain ⟨x₃, hx'x₃, hx₃x', hx₃f, -⟩ := exists_step hϖ x' f n hx'f (fun h => hmin' f hf h.symm)
    have hx_ne_x₃ : x ≠ x₃ := fun h => hmin f hf (h ▸ (IsWithin.mono' hϖ (Nat.le_succ n) hx₃f).symm)
    have hf_gx' : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) f (Vertex.twistedAct δ σ x') := by
      have := (isWithin_twistedAct_iff hϖ δ σ (n + 1) f x').2 hfx'
      rwa [mem_twistedFixedVertexSet.1 hf] at this

    have hx_gx' : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * n + 2) x (Vertex.twistedAct δ σ x') := by
      obtain ⟨y, -, -, -, hyother⟩ := exists_step hϖ x' (Vertex.twistedAct δ σ x') (2 * n + 1)
        (by simpa using hdisp) (by simpa using hndisp)

      have hx₃_near : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * n + 1)
          x₃ (Vertex.twistedAct δ σ x') := by
        have := isWithin_trans hϖ hx₃f hf_gx'
        simpa [two_mul, add_assoc] using this
      have hx₃y : x₃ = y := by
        by_contra hne
        exact (hyother x₃ hx'x₃ hx₃x' hne) (IsWithin.mono' hϖ (by omega) hx₃_near)
      intro hbad
      exact (hyother x hxx'.symm hx'x.symm (fun h => hx_ne_x₃ (h.trans hx₃y.symm))) hbad
    have hx_gx'_le : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * n + 2 + 1)
        x (Vertex.twistedAct δ σ x') := by
      have := isWithin_trans hϖ hxx' hdisp
      simpa [add_comm, add_left_comm, add_assoc] using this

    obtain ⟨z, -, -, -, hzother⟩ := exists_step hϖ (Vertex.twistedAct δ σ x') x (2 * n + 2) hx_gx'_le.symm
      (fun h => hx_gx' h.symm)
    have hgx₃_nb : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 (Vertex.twistedAct δ σ x')
        (Vertex.twistedAct δ σ x₃) := (isWithin_twistedAct_iff hϖ δ σ 1 x' x₃).2 hx'x₃
    have hgx₃_ne : Vertex.twistedAct δ σ x₃ ≠ Vertex.twistedAct δ σ x' := fun h =>
      hx₃x' (twistedAct_injective hϖ δ σ h)
    have hgx₃_near : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * n + 2) (Vertex.twistedAct δ σ x₃) x := by
      have h1 : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (Vertex.twistedAct δ σ x₃) f := by
        have := (isWithin_twistedAct_iff hϖ δ σ n x₃ f).2 hx₃f
        rwa [mem_twistedFixedVertexSet.1 hf] at this
      have := isWithin_trans hϖ h1 hfx
      simpa [two_mul, add_assoc] using this
    have hgx₃z : Vertex.twistedAct δ σ x₃ = z := by
      by_contra hne
      exact (hzother _ hgx₃_nb hgx₃_ne hne) (IsWithin.mono' hϖ (by omega) hgx₃_near)
    have hgx_nb : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 (Vertex.twistedAct δ σ x')
        (Vertex.twistedAct δ σ x) := (isWithin_twistedAct_iff hϖ δ σ 1 x' x).2 hxx'.symm
    have hgx_ne : Vertex.twistedAct δ σ x ≠ Vertex.twistedAct δ σ x' := fun h =>
      hx'x (twistedAct_injective hϖ δ σ h).symm
    have hgx_ne_z : Vertex.twistedAct δ σ x ≠ z := fun h =>
      hx_ne_x₃ (twistedAct_injective hϖ δ σ (h.trans hgx₃z.symm))
    exact (hzother _ hgx_nb hgx_ne hgx_ne_z) (by simpa [Nat.mul_succ, add_assoc] using hx.symm)

private theorem isWithin_twistedAct_iff_exists (hne : (twistedFixedVertexSet δ σ).Nonempty) (m : ℕ) (x : Vertex R K) :
    (Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * m + 1) x (Vertex.twistedAct δ σ x) ↔
      ∃ f ∈ twistedFixedVertexSet δ σ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) m f x) ∧
    (Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * m) x (Vertex.twistedAct δ σ x) ↔
      ∃ f ∈ twistedFixedVertexSet δ σ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) m f x) := by
  obtain ⟨k, ⟨f, hf, hfx⟩, hkmin⟩ := exists_nearest hϖ δ σ hne x

  have hup : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (2 * k) x (Vertex.twistedAct δ σ x) :=
    isWithin_twistedAct_of_isWithin_fixed hϖ δ σ hf hfx
  have hlow : ∀ j, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) j x (Vertex.twistedAct δ σ x) → 2 * k ≤ j := by
    intro j hj
    by_contra hlt
    push Not at hlt
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hmin : ∀ f' ∈ twistedFixedVertexSet δ σ, ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n f' x :=
      fun f' hf' h => hkmin n (Nat.lt_succ_self n) ⟨f', hf', h⟩
    exact displacement_of_dist hϖ δ σ n x f hf hfx hmin (IsWithin.mono' hϖ (by omega) hj)
  have hdist : ∀ j, (∃ f' ∈ twistedFixedVertexSet δ σ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) j f' x) ↔
      k ≤ j := by
    intro j
    constructor
    · intro hj
      by_contra hlt
      exact hkmin j (by omega) hj
    · intro hkj
      exact ⟨f, hf, (IsWithin.mono' hϖ hkj hfx)⟩
  refine ⟨⟨fun h => (hdist m).2 (by have := hlow _ h; omega), fun h => ?_⟩,
    ⟨fun h => (hdist m).2 (by have := hlow _ h; omega), fun h => ?_⟩⟩
  · exact IsWithin.mono' hϖ (by have := (hdist m).1 h; omega) hup
  · exact IsWithin.mono' hϖ (by have := (hdist m).1 h; omega) hup

end Displacement

end Fixed

open LT LT.LatticeTree in

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) (m : ℕ) :
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m + 1) δ σ =
      LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
          (2 * m) δ σ ∧
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m) δ σ =
      {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m f x} := by
  refine ⟨?_, ?_⟩
  · ext x
    rw [mem_twistedOrbitalBall, mem_twistedOrbitalBall,
      (Fixed.isWithin_twistedAct_iff_exists hϖ δ σ hne m x).1, (Fixed.isWithin_twistedAct_iff_exists hϖ δ σ hne m x).2]
  · ext x
    rw [mem_twistedOrbitalBall, Set.mem_setOf_eq, (Fixed.isWithin_twistedAct_iff_exists hϖ δ σ hne m x).2]

end S_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
end P2MW
export P2MW.S_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty (solution)
