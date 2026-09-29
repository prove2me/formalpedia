-- Prove2me | solution 1 for Matrix.finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c9ab75db-ad5b-52d5-bddd-fc77b9388bbe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Module

namespace MoritaLine

section

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev E (k : Type*) [Field k] {ι : Type*} [DecidableEq ι] (i j : ι) : Matrix ι ι k :=
  Matrix.single i j (1 : k)

theorem E_mul_E_same (i j l : ι) : E k i j * E k j l = E k i l := by
  simp [E]

theorem E_mul_E_of_ne (i j j' l : ι) (h : j ≠ j') : E k i j * E k j' l = 0 := by
  simp [E, Matrix.single_mul_single_of_ne, h]

theorem sum_E_diag : ∑ i : ι, E k i i = 1 := Matrix.sum_single_one

variable {V : Type*} [AddCommGroup V] [Module k V] [Module (Matrix ι ι k) V] [IsScalarTower k (Matrix ι ι k) V]
variable {W : Type*} [AddCommGroup W] [Module k W] [Module (Matrix ι ι k) W] [IsScalarTower k (Matrix ι ι k) W]

theorem smul_comm_k (a : Matrix ι ι k) (c : k) (v : V) : a • c • v = c • a • v :=
  smul_comm a c v

theorem E_smul_E_smul_same (i j l : ι) (v : V) : E k i j • E k j l • v = E k i l • v := by
  rw [← mul_smul, E_mul_E_same]

theorem E_smul_E_smul_of_ne (i j j' l : ι) (h : j ≠ j') (v : V) : E k i j • E k j' l • v = 0 := by
  rw [← mul_smul, E_mul_E_of_ne _ _ _ _ h, zero_smul]

variable (k V) in

def sm (a : Matrix ι ι k) : V →ₗ[k] V where
  toFun v := a • v
  map_add' x y := smul_add a x y
  map_smul' c v := smul_comm_k a c v

@[scoped simp] theorem sm_apply (a : Matrix ι ι k) (v : V) : sm k V a v = a • v := rfl

variable (k V) in

def corner (i₀ : ι) : Submodule k V :=
  LinearMap.range (sm k V (E k i₀ i₀))

theorem mem_corner_iff {i₀ : ι} {v : V} : v ∈ corner k V i₀ ↔ E k i₀ i₀ • v = v := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [sm_apply, E_smul_E_smul_same]
  · intro h
    exact ⟨v, h⟩

theorem E_smul_mem_corner (i₀ i : ι) (v : V) : E k i₀ i • v ∈ corner k V i₀ := by
  rw [mem_corner_iff, E_smul_E_smul_same]

theorem corner_smul_self {i₀ : ι} (v : corner k V i₀) : E k i₀ i₀ • (v : V) = v :=
  mem_corner_iff.1 v.2

variable (k V) in

def toPi (i₀ : ι) : V →ₗ[k] (ι → corner k V i₀) where
  toFun v i := ⟨E k i₀ i • v, E_smul_mem_corner i₀ i v⟩
  map_add' x y := by ext i; simp
  map_smul' c v := by ext i; simp [smul_comm_k]

variable (k V) in

def ofPi (i₀ : ι) : (ι → corner k V i₀) →ₗ[k] V where
  toFun m := ∑ i, E k i i₀ • (m i : V)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c m := by simp [Finset.smul_sum, smul_comm_k]

theorem ofPi_toPi (i₀ : ι) (v : V) : ofPi k V i₀ (toPi k V i₀ v) = v := by
  simp only [ofPi, toPi, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [E_smul_E_smul_same]
  rw [← Finset.sum_smul, sum_E_diag, one_smul]

theorem toPi_ofPi (i₀ : ι) (m : ι → corner k V i₀) : toPi k V i₀ (ofPi k V i₀ m) = m := by
  ext i
  simp only [ofPi, toPi, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum]
  rw [Finset.sum_eq_single i]
  · rw [E_smul_E_smul_same, corner_smul_self]
  · intro b _ hb
    rw [E_smul_E_smul_of_ne _ _ _ _ hb.symm]
  · intro h; exact absurd (Finset.mem_univ i) h

variable (k V) in

def equivPi (i₀ : ι) : V ≃ₗ[k] (ι → corner k V i₀) :=
  LinearEquiv.ofLinear (toPi k V i₀) (ofPi k V i₀)
    (LinearMap.ext (toPi_ofPi i₀)) (LinearMap.ext (ofPi_toPi i₀))

theorem finrank_eq_card_mul_finrank_corner [FiniteDimensional k V] (i₀ : ι) :
    finrank k V = Fintype.card ι * finrank k (corner k V i₀) := by
  rw [(equivPi k V i₀).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, smul_eq_mul,
    Finset.card_univ]

theorem map_smul_k (f : V →ₗ[Matrix ι ι k] W) (c : k) (v : V) : f (c • v) = c • f v := by
  rw [← algebraMap_smul (A := Matrix ι ι k) c v, map_smul, algebraMap_smul]

variable (k V W) in

def restr (i₀ : ι) : (V →ₗ[Matrix ι ι k] W) →ₗ[k] (corner k V i₀ →ₗ[k] corner k W i₀) where
  toFun f :=
    { toFun := fun v => ⟨f v, by
        rw [mem_corner_iff, ← map_smul, corner_smul_self]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by
        ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        exact map_smul_k f c x }
  map_add' f g := by ext; rfl
  map_smul' c f := by ext; rfl

@[scoped simp] theorem restr_apply_coe (i₀ : ι) (f : V →ₗ[Matrix ι ι k] W) (v : corner k V i₀) :
    ((restr k V W i₀ f) v : W) = f v := rfl

def extFun (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (v : V) : W :=
  ∑ i, E k i i₀ • (g ⟨E k i₀ i • v, E_smul_mem_corner i₀ i v⟩ : W)

theorem extFun_add (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (x y : V) :
    extFun i₀ g (x + y) = extFun i₀ g x + extFun i₀ g y := by
  simp only [extFun, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← Submodule.coe_add, ← map_add]
  congr 2
  ext; simp

theorem extFun_smul_k (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (c : k) (v : V) :
    extFun i₀ g (c • v) = c • extFun i₀ g v := by
  simp only [extFun, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_comm_k (E k i i₀) c, ← Submodule.coe_smul, ← map_smul]
  congr 3
  ext; simp [smul_comm_k]

def extLin (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) : V →ₗ[k] W where
  toFun := extFun i₀ g
  map_add' := extFun_add i₀ g
  map_smul' := extFun_smul_k i₀ g

@[scoped simp] theorem extLin_apply (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (v : V) :
    extLin i₀ g v = extFun i₀ g v := rfl

theorem extFun_E_smul (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (p q : ι) (v : V) :
    extFun i₀ g (E k p q • v) = E k p i₀ • (g ⟨E k i₀ q • v, E_smul_mem_corner i₀ q v⟩ : W) := by
  simp only [extFun]
  rw [Finset.sum_eq_single p]
  · congr 3
    ext
    simp only [E_smul_E_smul_same]
  · intro b _ hb
    have : (⟨E k i₀ b • E k p q • v, E_smul_mem_corner i₀ b _⟩ : corner k V i₀) = 0 := by
      ext; simp only [E_smul_E_smul_of_ne _ _ _ _ hb, Submodule.coe_zero]
    rw [this, map_zero, Submodule.coe_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem E_smul_extFun (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (p q : ι) (v : V) :
    E k p q • extFun i₀ g v = E k p i₀ • (g ⟨E k i₀ q • v, E_smul_mem_corner i₀ q v⟩ : W) := by
  simp only [extFun, Finset.smul_sum]
  rw [Finset.sum_eq_single q]
  · rw [E_smul_E_smul_same]
  · intro b _ hb
    rw [E_smul_E_smul_of_ne _ _ _ _ hb.symm]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem extFun_smul (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (a : Matrix ι ι k) (v : V) :
    extFun i₀ g (a • v) = a • extFun i₀ g v := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single a]
  conv_rhs => rw [Matrix.matrix_eq_sum_single a]
  simp only [Finset.sum_smul]
  rw [← extLin_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hE : Matrix.single p q (a p q) = (a p q) • E k p q := by
    simp [E, Matrix.smul_single]
  rw [hE, smul_assoc, smul_assoc, extLin_apply, extFun_smul_k, extFun_E_smul, E_smul_extFun]

variable (k V W) in

private def _root_.MoritaLine.ext (i₀ : ι) : (corner k V i₀ →ₗ[k] corner k W i₀) →ₗ[k] (V →ₗ[Matrix ι ι k] W) where
  toFun g :=
    { toFun := extFun i₀ g
      map_add' := extFun_add i₀ g
      map_smul' := extFun_smul i₀ g }
  map_add' g g' := by
    refine LinearMap.ext fun v => ?_
    simp only [extFun, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Submodule.coe_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' c g := by
    refine LinearMap.ext fun v => ?_
    simp only [extFun, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Submodule.coe_smul,
      RingHom.id_apply, Finset.smul_sum, smul_comm_k]

p2m_export "MoritaLine" "ext"
@[scoped simp] theorem ext_apply (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) (v : V) :
    ext k V W i₀ g v = extFun i₀ g v := rfl

theorem restr_ext (i₀ : ι) (g : corner k V i₀ →ₗ[k] corner k W i₀) :
    restr k V W i₀ (ext k V W i₀ g) = g := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [restr_apply_coe, ext_apply]
  have hv : (v : V) = E k i₀ i₀ • (v : V) := (corner_smul_self v).symm
  conv_lhs => rw [hv]
  rw [extFun_E_smul]
  have : (⟨E k i₀ i₀ • (v : V), E_smul_mem_corner i₀ i₀ _⟩ : corner k V i₀) = v := by
    ext; exact corner_smul_self v
  rw [this, corner_smul_self]

theorem ext_restr (i₀ : ι) (f : V →ₗ[Matrix ι ι k] W) : ext k V W i₀ (restr k V W i₀ f) = f := by
  refine LinearMap.ext fun v => ?_
  rw [ext_apply]
  simp only [extFun, restr_apply_coe]
  simp_rw [← map_smul, E_smul_E_smul_same]
  rw [← map_sum, ← Finset.sum_smul, sum_E_diag, one_smul]

variable (k V W) in

def homEquiv (i₀ : ι) : (V →ₗ[Matrix ι ι k] W) ≃ₗ[k] (corner k V i₀ →ₗ[k] corner k W i₀) :=
  LinearEquiv.ofLinear (restr k V W i₀) (ext k V W i₀)
    (LinearMap.ext (restr_ext i₀)) (LinearMap.ext (ext_restr i₀))

theorem main [FiniteDimensional k V] [FiniteDimensional k W] :
    finrank k (V →ₗ[Matrix ι ι k] W) * Fintype.card ι ^ 2 = finrank k V * finrank k W := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · haveI : Subsingleton (Matrix ι ι k) := inferInstance
    haveI : Subsingleton V := Module.subsingleton (Matrix ι ι k) V
    simp [Module.finrank_zero_of_subsingleton]
  · rw [(homEquiv k V W i₀).finrank_eq, Module.finrank_linearMap,
      finrank_eq_card_mul_finrank_corner (V := V) i₀, finrank_eq_card_mul_finrank_corner (V := W) i₀]
    ring

end

end MoritaLine
p2m_reactivate "P2MW.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank.MoritaLine"

universe u v w w'

theorem solution
    (k : Type u) [Field k] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (V : Type w) (W : Type w') [AddCommGroup V] [Module k V] [Module (Matrix ι ι k) V]
    [IsScalarTower k (Matrix ι ι k) V]
    [AddCommGroup W] [Module k W] [Module (Matrix ι ι k) W] [IsScalarTower k (Matrix ι ι k) W]
    [FiniteDimensional k V] [FiniteDimensional k W] :
    Module.finrank k (V →ₗ[Matrix ι ι k] W) * Fintype.card ι ^ 2 =
      Module.finrank k V * Module.finrank k W :=
  MoritaLine.main

end S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
end P2MW
export P2MW.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank (solution)
