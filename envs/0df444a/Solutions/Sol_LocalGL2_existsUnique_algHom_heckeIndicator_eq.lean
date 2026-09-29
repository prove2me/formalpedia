-- Prove2me | solution 1 for LocalGL2.existsUnique_algHom_heckeIndicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/91a70adf-2063-51c8-82c4-0af6547ed202

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_CartanDecomposition
import Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
import Theorems.Thm_LocalGL2_cartanDiag_cartanRel_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq

set_option autoImplicit false

open scoped Pointwise

namespace HeckePair
p2m_export "HeckePair" "HeckeAlgebra apply_left_mul apply_mul_right finite_cosets ext coe_apply_add coe_apply_smul convTerm_mk support_convTerm_subset mul_apply one_mul mul_one mul_zero add_mul mul_add smul_mul mul_smul_comm mul_assoc doubleCoset mem_doubleCoset_iff self_mem_doubleCoset mul_mem_doubleCoset doubleCoset_mul_mem image_mk_doubleCoset heckeIndicator heckeIndicator_apply_of_mem heckeIndicator_apply_of_notMem heckeIndicator_of_mem"
p2m_open "HeckePair"

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

theorem image_mk_mul_singleton_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) :
    (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)) = {QuotientGroup.mk z} := by
  ext c
  constructor
  · rintro ⟨_, ⟨u, hu, w, hw, rfl⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hw ⊢
    show (QuotientGroup.mk (u * w) : G ⧸ U) = QuotientGroup.mk z
    rw [hw, (Subgroup.mem_center_iff.mp hz) u]
    exact QuotientGroup.mk_mul_of_mem z hu
  · rintro rfl
    exact ⟨z, ⟨1, one_mem U, z, rfl, one_mul z⟩, rfl⟩

theorem finite_image_mk_mul_singleton_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) :
    (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite := by
  rw [image_mk_mul_singleton_of_mem_center hz]
  exact Set.finite_singleton _

theorem mem_doubleCoset_iff_of_mem_center {z x : G} (hz : z ∈ Subgroup.center G) :
    x ∈ doubleCoset U z ↔ z⁻¹ * x ∈ U := by
  rw [mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [(Subgroup.mem_center_iff.mp hz) u, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hu hv
  · intro h
    exact ⟨1, one_mem U, z⁻¹ * x, h, by group⟩

theorem heckeIndicator_mul_apply_of_mem_center {z : G} (hz : z ∈ Subgroup.center G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite)
    (f : HeckeAlgebra U R₀) (x : G) :
    ((heckeIndicator R₀ z hfin * f : HeckeAlgebra U R₀) : G → R₀) x
      = (f : G → R₀) (z⁻¹ * x) := by
  classical
  rw [mul_apply]
  have hsupp : QuotientGroup.mk '' (Function.support
      ((heckeIndicator R₀ z hfin : HeckeAlgebra U R₀) : G → R₀))
        ⊆ (({QuotientGroup.mk z} : Finset (G ⧸ U)) : Set (G ⧸ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Finset.coe_singleton, Set.mem_singleton_iff]
    have hyD : y ∈ doubleCoset U z := by
      by_contra hyD
      exact hy (heckeIndicator_apply_of_notMem hfin hyD)
    have hzy : z⁻¹ * y ∈ U := (mem_doubleCoset_iff_of_mem_center hz).mp hyD
    have hyz : y⁻¹ * z ∈ U := by
      have := inv_mem hzy
      rwa [mul_inv_rev, inv_inv] at this
    exact QuotientGroup.eq.mpr hyz
  rw [finsum_eq_sum_of_support_subset _ ((support_convTerm_subset _ f x).trans hsupp),
    Finset.sum_singleton, convTerm_mk,
    heckeIndicator_apply_of_mem hfin (self_mem_doubleCoset z), one_mul]

theorem mul_heckeIndicator_apply_of_mem_center {z : G} (hz : z ∈ Subgroup.center G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite)
    (f : HeckeAlgebra U R₀) (x : G) :
    ((f * heckeIndicator R₀ z hfin : HeckeAlgebra U R₀) : G → R₀) x
      = (f : G → R₀) (z⁻¹ * x) := by
  classical
  rw [mul_apply]
  have hzc : ∀ g : G, g * z = z * g := Subgroup.mem_center_iff.mp hz

  refine (finsum_eq_single _ (QuotientGroup.mk (z⁻¹ * x)) fun c hc => ?_).trans ?_
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    rw [convTerm_mk]
    have hnot : y⁻¹ * x ∉ doubleCoset U z := by
      intro hmem
      apply hc
      have h1 : z⁻¹ * (y⁻¹ * x) ∈ U := (mem_doubleCoset_iff_of_mem_center hz).mp hmem
      refine QuotientGroup.eq.mpr ?_
      have : y⁻¹ * (z⁻¹ * x) = z⁻¹ * (y⁻¹ * x) := by
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        have := hzc y⁻¹

        calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by rw [mul_inv_rev]
          _ = (y * z)⁻¹ := by rw [hzc y]
          _ = z⁻¹ * y⁻¹ := by rw [mul_inv_rev]
      rw [this]
      exact h1
    rw [heckeIndicator_apply_of_notMem hfin hnot, mul_zero]
  · rw [convTerm_mk]
    have hrep : (z⁻¹ * x)⁻¹ * x = z := by
      rw [mul_inv_rev, inv_inv, mul_assoc, ← hzc x, inv_mul_cancel_left]
    rw [hrep, heckeIndicator_apply_of_mem hfin (self_mem_doubleCoset z), mul_one]

theorem heckeIndicator_mul_comm_of_mem_center {z : G} (hz : z ∈ Subgroup.center G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite)
    (f : HeckeAlgebra U R₀) :
    heckeIndicator R₀ z hfin * f = f * heckeIndicator R₀ z hfin := by
  ext x
  rw [heckeIndicator_mul_apply_of_mem_center hz, mul_heckeIndicator_apply_of_mem_center hz]

theorem heckeIndicator_center_mul_heckeIndicator {z : G} (hz : z ∈ Subgroup.center G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite)
    (g : G) (hg : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite)
    (hzg : (QuotientGroup.mk '' ((U : Set G) * {z * g}) : Set (G ⧸ U)).Finite) :
    heckeIndicator R₀ z hfin * heckeIndicator R₀ g hg
      = (heckeIndicator R₀ (z * g) hzg : HeckeAlgebra U R₀) := by
  ext x
  rw [heckeIndicator_mul_apply_of_mem_center hz]
  have hzc : ∀ g : G, g * z = z * g := Subgroup.mem_center_iff.mp hz
  have key : z⁻¹ * x ∈ doubleCoset U g ↔ x ∈ doubleCoset U (z * g) := by
    rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
    constructor
    · rintro ⟨u, hu, v, hv, h⟩
      refine ⟨u, hu, v, hv, ?_⟩
      rw [← mul_assoc, hzc u, mul_assoc z u g, mul_assoc z (u * g) v, h, mul_inv_cancel_left]
    · rintro ⟨u, hu, v, hv, rfl⟩
      refine ⟨u, hu, v, hv, ?_⟩
      rw [← mul_assoc u z g, hzc u]
      group
  by_cases hx : x ∈ doubleCoset U (z * g)
  · rw [heckeIndicator_apply_of_mem hg (key.mpr hx), heckeIndicator_apply_of_mem hzg hx]
  · rw [heckeIndicator_apply_of_notMem hg (fun h => hx (key.mp h)),
      heckeIndicator_apply_of_notMem hzg hx]

theorem heckeIndicator_center_mul_inv {z : G} (hz : z ∈ Subgroup.center G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite)
    (hfin' : (QuotientGroup.mk '' ((U : Set G) * {z⁻¹}) : Set (G ⧸ U)).Finite) :
    heckeIndicator R₀ z hfin * heckeIndicator R₀ z⁻¹ hfin' = (1 : HeckeAlgebra U R₀) := by
  have h1 : (QuotientGroup.mk '' ((U : Set G) * {z * z⁻¹}) : Set (G ⧸ U)).Finite := by
    rw [mul_inv_cancel]
    exact finite_image_mk_mul_singleton_of_mem_center (Subgroup.one_mem _)
  rw [heckeIndicator_center_mul_heckeIndicator hz hfin z⁻¹ hfin' h1]
  have : ∀ (h : (QuotientGroup.mk '' ((U : Set G) * {z * z⁻¹}) : Set (G ⧸ U)).Finite),
      heckeIndicator R₀ (z * z⁻¹) h = (1 : HeckeAlgebra U R₀) := by
    rw [mul_inv_cancel]
    intro h
    exact heckeIndicator_of_mem (one_mem U) h
  exact this h1

theorem heckeIndicator_inv_mul_center {z : G} (hz : z ∈ Subgroup.center G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite)
    (hfin' : (QuotientGroup.mk '' ((U : Set G) * {z⁻¹}) : Set (G ⧸ U)).Finite) :
    heckeIndicator R₀ z⁻¹ hfin' * heckeIndicator R₀ z hfin = (1 : HeckeAlgebra U R₀) := by
  have hz' : z⁻¹ ∈ Subgroup.center G := inv_mem hz
  have := heckeIndicator_center_mul_inv (U := U) (R₀ := R₀) hz' hfin' (by rw [inv_inv]; exact hfin)
  simpa only [inv_inv] using this

theorem isUnit_heckeIndicator_of_mem_center {z : G} (hz : z ∈ Subgroup.center G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {z}) : Set (G ⧸ U)).Finite) :
    IsUnit (heckeIndicator R₀ z hfin : HeckeAlgebra U R₀) :=
  isUnit_iff_exists.mpr ⟨heckeIndicator R₀ z⁻¹
      (finite_image_mk_mul_singleton_of_mem_center (inv_mem hz)),
    heckeIndicator_center_mul_inv hz hfin _, heckeIndicator_inv_mul_center hz hfin _⟩

end

end HeckePair

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem coe_diagPi_mul_coe_localRepInf :
    (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagPi_mul_localRepInf_mem_center :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  simp only [Units.val_mul]
  rw [coe_diagPi_mul_coe_localRepInf, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem finite_image_mul_diagPi_mul_localRepInf :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite :=
  HeckePair.finite_image_mk_mul_singleton_of_mem_center
    (diagPi_mul_localRepInf_mem_center ϖ hϖ0)

theorem heckeIndicator_diagPi_mul_localRepInf_central_isUnit_impl
    {R₀ : Type*} [CommRing R₀]
    (hfin : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    (∀ f : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀,
        HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin * f
          = f * HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin) ∧
      IsUnit (HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin :
        HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) :=
  ⟨fun f => HeckePair.heckeIndicator_mul_comm_of_mem_center
      (diagPi_mul_localRepInf_mem_center ϖ hϖ0) hfin f,
    HeckePair.isUnit_heckeIndicator_of_mem_center
      (diagPi_mul_localRepInf_mem_center ϖ hϖ0) hfin⟩

end

end LocalGL2

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace HeckePair
p2m_export "HeckePair" "HeckeAlgebra apply_left_mul apply_mul_right finite_cosets ext coe_apply_add coe_apply_smul convTerm_mk support_convTerm_subset mul_apply one_mul mul_one mul_zero add_mul mul_add smul_mul mul_smul_comm mul_assoc doubleCoset mem_doubleCoset_iff self_mem_doubleCoset mul_mem_doubleCoset doubleCoset_mul_mem image_mk_doubleCoset heckeIndicator heckeIndicator_apply_of_mem heckeIndicator_apply_of_notMem heckeIndicator_of_mem"
p2m_open "HeckePair"

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

theorem apply_eq_of_mem_doubleCoset' (f : HeckeAlgebra U R₀) {g x : G}
    (hx : x ∈ doubleCoset U g) : (f : G → R₀) x = (f : G → R₀) g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  rw [apply_mul_right f hv, apply_left_mul f hu]

theorem mem_doubleCoset_comm {g x : G} : x ∈ doubleCoset U g ↔ g ∈ doubleCoset U x := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp h
    exact mem_doubleCoset_iff.mpr ⟨u⁻¹, inv_mem hu, v⁻¹, inv_mem hv, by group⟩
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp h
    exact mem_doubleCoset_iff.mpr ⟨u⁻¹, inv_mem hu, v⁻¹, inv_mem hv, by group⟩

theorem mem_doubleCoset_trans {g x y : G} (hx : x ∈ doubleCoset U g)
    (hy : y ∈ doubleCoset U x) : y ∈ doubleCoset U g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  obtain ⟨u', hu', v', hv', rfl⟩ := mem_doubleCoset_iff.mp hy
  exact mem_doubleCoset_iff.mpr ⟨u' * u, mul_mem hu' hu, v * v', mul_mem hv hv', by group⟩

theorem mem_doubleCoset_iff_of_mem_center' {z x : G} (hz : z ∈ Subgroup.center G) :
    x ∈ doubleCoset U z ↔ z⁻¹ * x ∈ U := by
  rw [mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [(Subgroup.mem_center_iff.mp hz) u, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hu hv
  · intro h
    exact ⟨1, one_mem U, z⁻¹ * x, h, by group⟩

theorem heckeIndicator_mul_apply_eq_sum {ι : Type*} [Fintype ι] {t : G} {reps : ι → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U t reps)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {t}) : Set (G ⧸ U)).Finite)
    (f : HeckeAlgebra U R₀) (x : G) :
    ((heckeIndicator R₀ t hfin * f : HeckeAlgebra U R₀) : G → R₀) x
      = ∑ i, (f : G → R₀) ((reps i)⁻¹ * x) := by
  classical
  rw [mul_apply]
  have hsupp : QuotientGroup.mk '' (Function.support
      ((heckeIndicator R₀ t hfin : HeckeAlgebra U R₀) : G → R₀))
        ⊆ ((Finset.univ.image fun i => (QuotientGroup.mk (reps i) : G ⧸ U)) : Set (G ⧸ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyD : y ∈ doubleCoset U t := by
      by_contra hyD
      exact hy (heckeIndicator_apply_of_notMem hfin hyD)
    obtain ⟨i, hi⟩ := hsys.covers y hyD
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact ⟨i, hi.symm⟩
  rw [finsum_eq_sum_of_support_subset _ ((support_convTerm_subset _ f x).trans hsupp),
    Finset.sum_image (fun i _ j _ h => hsys.mk_injective h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [convTerm_mk, heckeIndicator_apply_of_mem hfin (hsys.mem_doubleCoset i), one_mul]

end

end HeckePair

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section Integral

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem entries_mem_range_mul {x y : GL (Fin 2) K}
    (hx : ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hy : ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) :
    ∀ i j, ((x * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨a, ha⟩ := hx i 0
  obtain ⟨b, hb⟩ := hy 0 j
  obtain ⟨c, hc⟩ := hx i 1
  obtain ⟨d, hd⟩ := hy 1 j
  exact ⟨a * b + c * d, by rw [map_add, map_mul, map_mul, ha, hb, hc, hd]⟩

theorem entries_mem_range_of_mem_integralSubgroup {u : GL (Fin 2) K}
    (hu : u ∈ integralSubgroup R K) :
    ∀ i j, (u : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
  fun i j => exists_entry_eq_of_mem_integralSubgroup hu i j

theorem entries_mem_range_of_mem_doubleCoset {g x : GL (Fin 2) K}
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) g) :
    ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact entries_mem_range_mul (entries_mem_range_mul
    (entries_mem_range_of_mem_integralSubgroup hu) hg) (entries_mem_range_of_mem_integralSubgroup hv)

theorem entries_mem_range_diagPi :
    ∀ i j, ((diagPi ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) := by
  intro i j
  rw [coe_diagPi]
  fin_cases i <;> fin_cases j
  · exact ⟨ϖ, rfl⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

theorem exists_det_eq_of_mem_integralSubgroup {u : GL (Fin 2) K}
    (hu : u ∈ integralSubgroup R K) :
    ∃ η : Rˣ, (u : Matrix (Fin 2) (Fin 2) K).det = algebraMap R K η := by
  obtain ⟨y, rfl⟩ := hu
  refine ⟨Matrix.GeneralLinearGroup.det y, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.GeneralLinearGroup.map_apply, map_sub, map_mul]

theorem exists_det_eq_of_mem_doubleCoset_diagPi {x : GL (Fin 2) K}
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0)) :
    ∃ η : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det = algebraMap R K η * algebraMap R K ϖ := by
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_integralSubgroup hu
  obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_integralSubgroup hv
  refine ⟨η₁ * η₂, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h₁, h₂, coe_diagPi,
    Matrix.det_fin_two_of, Units.val_mul, map_mul]
  ring

theorem coe_diagPi_mul_coe_localRepInf' :
    (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagPi_mul_localRepInf_mem_center' :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  simp only [Units.val_mul]
  rw [coe_diagPi_mul_coe_localRepInf', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem diagPi_mul_localRepInf_mul_apply (m : GL (Fin 2) K) (i j : Fin 2) :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      = algebraMap R K ϖ * (m : Matrix (Fin 2) (Fin 2) K) i j := by
  rw [Units.val_mul, Units.val_mul, coe_diagPi_mul_coe_localRepInf', Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]

theorem coe_localRepInf_sq :
    ((localRepInf ϖ hϖ0 ^ 2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![1, 0; 0, algebraMap R K ϖ ^ 2] := by
  rw [pow_two, Units.val_mul, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two]

theorem localRepInf_mem_doubleCoset_diagPi :
    localRepInf ϖ hϖ0 ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) :=
  HeckePair.mem_doubleCoset_iff.mpr ⟨weylInt R K, weylInt_mem, weylInt R K, weylInt_mem, rfl⟩

def localReps : Option (R ⧸ Ideal.span {ϖ}) → GL (Fin 2) K
  | some c => localRepSome ϖ hϖ0 (Quotient.out c)
  | none => localRepInf ϖ hϖ0

@[scoped simp] theorem localReps_some (c : R ⧸ Ideal.span {ϖ}) :
    localReps ϖ hϖ0 (some c) = localRepSome ϖ hϖ0 (Quotient.out c) := rfl

@[scoped simp] theorem localReps_none : localReps ϖ hϖ0 none = localRepInf ϖ hϖ0 := rfl

end Integral

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem algebraMap_mul_ne_one (hϖ : ¬ IsUnit ϖ) (r : R) :
    algebraMap R K ϖ * algebraMap R K r ≠ 1 := by
  intro h
  apply hϖ
  rw [← map_mul, ← map_one (algebraMap R K)] at h
  exact IsUnit.of_mul_eq_one r (IsFractionRing.injective R K h)

theorem dvd_of_not_isUnit (hϖ : Irreducible ϖ) {r : R} (hr : ¬ IsUnit r) : ϖ ∣ r := by
  rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal]
  exact hr

theorem isHeckeCosetSystem_localReps (hϖ : Irreducible ϖ) :
    HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup R K) (diagPi ϖ hϖ0)
      (localReps ϖ hϖ0) := by
  constructor
  · rintro (_ | c)
    · exact localRepInf_mem_doubleCoset_diagPi ϖ hϖ0
    · exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨unipotentInt K (Quotient.out c), unipotentInt_mem _, 1, one_mem _,
          by rw [mul_one]; rfl⟩
  · intro x hx
    obtain ⟨y, hy, u, hu, rfl⟩ := Set.mem_mul.mp hx
    have hu' : u ∈ integralSubgroup R K := hu
    have hy' : y ∈ heckeMulSet ϖ hϖ0 := hy
    have hmkx : (QuotientGroup.mk (y * u) : GL (Fin 2) K ⧸ integralSubgroup R K)
        = QuotientGroup.mk y := QuotientGroup.mk_mul_of_mem y hu'
    rcases exists_rep_of_mem_heckeMulSet ϖ hϖ0 hϖ hy' with ⟨b, hb⟩ | hbinf
    · refine ⟨some (Ideal.Quotient.mk _ b), ?_⟩
      rw [hmkx, ← hb, localReps_some]
      refine mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 ?_
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    · exact ⟨none, by rw [hmkx, ← hbinf, localReps_none]⟩
  · rintro (_ | c) (_ | c') h
    · rfl
    · simp only [localReps_some, localReps_none] at h
      exact absurd h.symm (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖ.not_isUnit _)
    · simp only [localReps_some, localReps_none] at h
      exact absurd h (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖ.not_isUnit _)
    · simp only [localReps_some] at h
      have hd := dvd_sub_of_mk_localRepSome_eq ϖ hϖ0 h
      rw [← Ideal.Quotient.mk_out c, ← Ideal.Quotient.mk_out c']
      exact congrArg some (Ideal.Quotient.eq.mpr (by rwa [Ideal.mem_span_singleton, dvd_sub_comm]))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem mem_doubleCoset_localRepInf_sq_of_isUnit {x : GL (Fin 2) K}
    (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdet : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ 2) (ha : IsUnit (e 0 0)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
  obtain ⟨au, hau⟩ := ha
  set a' : R := ↑au⁻¹ with ha'
  have h1 : e 0 0 * a' = 1 := by rw [← hau, ha', Units.mul_inv]
  have hdet1 : IsUnit (Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a']) := by
    have : Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a'] = ε := by
      rw [Matrix.det_fin_two_of]; linear_combination (ε : R) * h1
    rw [this]; exact ε.isUnit
  have hdet2 : IsUnit (Matrix.det !![(1 : R), e 0 1 * a'; 0, 1]) := by
    rw [Matrix.det_fin_two_of]; simp
  set y₁ := Matrix.GeneralLinearGroup.mk'' _ hdet1 with hy₁
  set y₂ := Matrix.GeneralLinearGroup.mk'' _ hdet2 with hy₂
  have hA : algebraMap R K (e 0 0) * algebraMap R K a' = 1 := by
    rw [← map_mul, h1, map_one]
  have hD : algebraMap R K (e 0 0) * algebraMap R K (e 1 1)
      - algebraMap R K (e 0 1) * algebraMap R K (e 1 0)
        = algebraMap R K ε * algebraMap R K ϖ ^ 2 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul, map_pow]
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨Matrix.GeneralLinearGroup.map (algebraMap R K) y₁, ⟨y₁, rfl⟩,
      Matrix.GeneralLinearGroup.map (algebraMap R K) y₂, ⟨y₂, rfl⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hy₁v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₁ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![e 0 0, 0; e 1 0, (ε : R) * a'] i j) :=
    fun i j => rfl
  have hy₂v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₂ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![(1 : R), e 0 1 * a'; 0, 1] i j) :=
    fun i j => rfl
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, coe_localRepInf_sq, ← he i j]
  simp only [hy₁v, hy₂v]
  fin_cases i <;> fin_cases j <;> simp [map_mul]
  · linear_combination (algebraMap R K (e 0 1)) * hA
  · linear_combination (algebraMap R K (e 1 1)) * hA - (algebraMap R K a') * hD

theorem mem_doubleCoset_sq_or_center (hϖ : Irreducible ϖ) {x : GL (Fin 2) K}
    (hint : ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
      = algebraMap R K ε * algebraMap R K ϖ ^ 2) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) ∨
      x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) := by
  have hint' : ∀ i j, ∃ r, algebraMap R K r = (x : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => hint i j
  choose e he using hint'
  obtain ⟨ε, hε⟩ := hdet
  have hinj := IsFractionRing.injective R K
  have hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ 2 := by
    apply hinj
    rw [map_sub, map_mul, map_mul, he, he, he, he, map_mul, map_pow, ← hε, Matrix.det_fin_two]
  have hwU : weylInt R K ∈ integralSubgroup R K := weylInt_mem

  by_cases ha : IsUnit (e 0 0)
  · exact Or.inl (mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0 e he ε hdetR ha)

  by_cases hb : IsUnit (e 0 1)
  · left
    have hmem : x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
      refine mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0
        (Matrix.of fun i j => e i (Equiv.swap 0 1 j)) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hb
    have := HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)
    rwa [mul_inv_cancel_right] at this

  by_cases hc : IsUnit (e 1 0)
  · left
    have hmem : weylInt R K * x
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
      refine mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) j) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hc
    have := HeckePair.mul_mem_doubleCoset hmem (inv_mem hwU)
    rwa [inv_mul_cancel_left] at this

  by_cases hd : IsUnit (e 1 1)
  · left
    have hmem : weylInt R K * x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
      refine mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) (Equiv.swap 0 1 j)) (fun i j => ?_) ε ?_ ?_
      · rw [Units.val_mul, Units.val_mul, coe_weylInt]
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i <;> fin_cases j <;> simp [he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
        linear_combination hdetR
      · simpa using hd
    have h' := HeckePair.mul_mem_doubleCoset
      (HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)) (inv_mem hwU)
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at h'

  right
  have hdvd : ∀ i j, ϖ ∣ e i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact dvd_of_not_isUnit ϖ hϖ ha
    · exact dvd_of_not_isUnit ϖ hϖ hb
    · exact dvd_of_not_isUnit ϖ hϖ hc
    · exact dvd_of_not_isUnit ϖ hϖ hd
  choose e₁ he₁ using hdvd
  have hdet₁ : e₁ 0 0 * e₁ 1 1 - e₁ 0 1 * e₁ 1 0 = ε := by
    have hϖ2 : ϖ ^ 2 ≠ 0 := pow_ne_zero 2 hϖ.ne_zero
    apply mul_left_cancel₀ hϖ2
    rw [← hdetR.trans (mul_comm _ _), he₁ 0 0, he₁ 1 1, he₁ 0 1, he₁ 1 0]
    ring
  have hdetu : IsUnit (Matrix.det (Matrix.of e₁)) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    rw [hdet₁]
    exact ε.isUnit
  set y := Matrix.GeneralLinearGroup.mk'' _ hdetu with hy
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨1, one_mem _, Matrix.GeneralLinearGroup.map (algebraMap R K) y, ⟨y, rfl⟩, ?_⟩
  rw [one_mul]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [diagPi_mul_localRepInf_mul_apply, ← he i j, he₁ i j, map_mul]
  rfl

theorem heckeIndicator_diagPi_mul_self_impl
    (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (h2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ 2}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
      = (HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ 2) h2 :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀)
        + ((Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) + 1)
          • HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hsys := isHeckeCosetSystem_localReps ϖ hϖ0 hϖ
  have hz := diagPi_mul_localRepInf_mem_center' ϖ hϖ0
  have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g := Subgroup.mem_center_iff.mp hz

  have hTint : ∀ {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) →
        ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
    fun hy => entries_mem_range_of_mem_doubleCoset (entries_mem_range_diagPi ϖ hϖ0) hy

  have hl2z : localRepInf ϖ hϖ0 ^ 2
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) := by
    intro h
    have hm := (HeckePair.mem_doubleCoset_iff_of_mem_center' hz).mp h
    obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup hm 0 0
    have key : ((localRepInf ϖ hϖ0 ^ 2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
        = algebraMap R K ϖ * algebraMap R K r := by
      rw [hr, ← diagPi_mul_localRepInf_mul_apply ϖ hϖ0, mul_inv_cancel_left]
    rw [coe_localRepInf_sq] at key
    exact algebraMap_mul_ne_one ϖ hϖ.not_isUnit r (by simpa using key.symm)
  have hzl2 : diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) :=
    fun h => hl2z (HeckePair.mem_doubleCoset_comm.mp h)
  ext x
  simp only [HeckePair.coe_apply_add, HeckePair.coe_apply_smul]
  by_cases hx2 : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2)
  ·
    have hxz : x ∉ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) :=
      fun h => hl2z (HeckePair.mem_doubleCoset_trans h (HeckePair.mem_doubleCoset_comm.mp hx2))
    rw [HeckePair.heckeIndicator_apply_of_mem h2 hx2,
      HeckePair.heckeIndicator_apply_of_notMem hS hxz, mul_zero, add_zero]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hx2]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys, Fintype.sum_option, localReps_none,
      pow_two, inv_mul_cancel_left,
      HeckePair.heckeIndicator_apply_of_mem _ (localRepInf_mem_doubleCoset_diagPi ϖ hϖ0)]
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [localReps_some]
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_

    obtain ⟨r, hr⟩ := hTint hmem 0 0
    rw [Units.val_mul, ← pow_two, coe_localRepSome_inv, coe_localRepInf_sq] at hr
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hr
    exact algebraMap_mul_ne_one ϖ hϖ.not_isUnit r (by rw [hr, mul_inv_cancel₀ hϖ0])
  by_cases hxz : x ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem h2 hx2,
      HeckePair.heckeIndicator_apply_of_mem hS hxz, zero_add, mul_one]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hxz]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys]
    have hterm : ∀ i, ((HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0)
        (finite_image_mul_diagPi ϖ hϖ0 hϖ) :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀)
            ((localReps ϖ hϖ0 i)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)) = 1 := by
      intro i
      refine HeckePair.heckeIndicator_apply_of_mem _ ?_
      obtain ⟨u, hu, v, hv, huv⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
      rw [← huv, _root_.mul_inv_rev, _root_.mul_inv_rev]
      simp only [mul_assoc]
      rw [hzc u⁻¹]
      simp only [mul_assoc]
      rw [inv_mul_cancel_left]

      exact HeckePair.mul_mem_doubleCoset
        (HeckePair.doubleCoset_mul_mem (localRepInf_mem_doubleCoset_diagPi ϖ hϖ0) (inv_mem hu))
        (inv_mem hv)
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul,
      mul_one, Nat.cast_add, Nat.cast_one, Nat.card_eq_fintype_card]
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem h2 hx2,
      HeckePair.heckeIndicator_apply_of_notMem hS hxz, mul_zero, add_zero,
      HeckePair.heckeIndicator_mul_apply_eq_sum hsys]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_
    have hri := hsys.mem_doubleCoset i

    have hx_eq : x = localReps ϖ hϖ0 i * ((localReps ϖ hϖ0 i)⁻¹ * x) := by
      rw [mul_inv_cancel_left]
    have hint : ∀ i' j', (x : Matrix (Fin 2) (Fin 2) K) i' j' ∈ Set.range (algebraMap R K) := by
      rw [hx_eq]
      exact entries_mem_range_mul (hTint hri) (hTint hmem)
    have hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
        = algebraMap R K ε * algebraMap R K ϖ ^ 2 := by
      obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_doubleCoset_diagPi ϖ hϖ0 hri
      obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_doubleCoset_diagPi ϖ hϖ0 hmem
      refine ⟨η₁ * η₂, ?_⟩
      rw [hx_eq, Units.val_mul, Matrix.det_mul, h₁, h₂, Units.val_mul, map_mul]
      ring
    rcases mem_doubleCoset_sq_or_center ϖ hϖ0 hϖ hint hdet with h | h
    · exact hx2 h
    · exact hxz h

end DVR

end

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section RecursionBasic

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem diag_two_pow' (x y : K) (n : ℕ) :
    (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) K) ^ n = !![x ^ n, 0; 0, y ^ n] := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem coe_localRepInf_pow (m : ℕ) :
    ((localRepInf ϖ hϖ0 ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![1, 0; 0, algebraMap R K ϖ ^ m] := by
  rw [Units.val_pow_eq_pow_val, coe_localRepInf, diag_two_pow', one_pow]

theorem entries_mem_range_localRepInf_pow (m : ℕ) :
    ∀ i j, ((localRepInf ϖ hϖ0 ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) := by
  intro i j
  rw [coe_localRepInf_pow]
  fin_cases i <;> fin_cases j
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨ϖ ^ m, by simp⟩

theorem exists_det_eq_of_mem_doubleCoset_localRepInf_pow (m : ℕ) {x : GL (Fin 2) K}
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m)) :
    ∃ η : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
      = algebraMap R K η * algebraMap R K ϖ ^ m := by
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_integralSubgroup hu
  obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_integralSubgroup hv
  refine ⟨η₁ * η₂, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h₁, h₂,
    coe_localRepInf_pow, Matrix.det_fin_two_of, Units.val_mul, map_mul]
  ring

theorem diagPi_mul_localRepInf_comm :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = localRepInf ϖ hϖ0 * diagPi ϖ hϖ0 := by
  apply Units.ext
  change (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
    = (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end RecursionBasic
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

section RecursionDVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem center_mul_not_mem_doubleCoset_localRepInf_pow (hϖu : ¬ IsUnit ϖ) (m : ℕ)
    {y : GL (Fin 2) K}
    (hy : ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * y
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
  intro h
  have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g :=
    Subgroup.mem_center_iff.mp (diagPi_mul_localRepInf_mem_center' ϖ hϖ0)
  obtain ⟨u, hu, v, hv, huv⟩ :=
    HeckePair.mem_doubleCoset_iff.mp (HeckePair.mem_doubleCoset_comm.mp h)

  have hint : ∀ i j, ((u * (y * v) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) :=
    entries_mem_range_mul (entries_mem_range_of_mem_integralSubgroup hu)
      (entries_mem_range_mul hy (entries_mem_range_of_mem_integralSubgroup hv))
  obtain ⟨r, hr⟩ := hint 0 0
  have key := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) huv
  rw [← mul_assoc, hzc u, mul_assoc, mul_assoc, diagPi_mul_localRepInf_mul_apply, ← hr,
    coe_localRepInf_pow] at key
  exact algebraMap_mul_ne_one ϖ hϖu r (by simpa using key)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem mem_doubleCoset_localRepInf_pow_of_isUnit (m : ℕ) {x : GL (Fin 2) K}
    (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdet : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ m) (ha : IsUnit (e 0 0)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
  obtain ⟨au, hau⟩ := ha
  set a' : R := ↑au⁻¹ with ha'
  have h1 : e 0 0 * a' = 1 := by rw [← hau, ha', Units.mul_inv]
  have hdet1 : IsUnit (Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a']) := by
    have : Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a'] = ε := by
      rw [Matrix.det_fin_two_of]; linear_combination (ε : R) * h1
    rw [this]; exact ε.isUnit
  have hdet2 : IsUnit (Matrix.det !![(1 : R), e 0 1 * a'; 0, 1]) := by
    rw [Matrix.det_fin_two_of]; simp
  set y₁ := Matrix.GeneralLinearGroup.mk'' _ hdet1 with hy₁
  set y₂ := Matrix.GeneralLinearGroup.mk'' _ hdet2 with hy₂
  have hA : algebraMap R K (e 0 0) * algebraMap R K a' = 1 := by
    rw [← map_mul, h1, map_one]
  have hD : algebraMap R K (e 0 0) * algebraMap R K (e 1 1)
      - algebraMap R K (e 0 1) * algebraMap R K (e 1 0)
        = algebraMap R K ε * algebraMap R K ϖ ^ m := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul, map_pow]
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨Matrix.GeneralLinearGroup.map (algebraMap R K) y₁, ⟨y₁, rfl⟩,
      Matrix.GeneralLinearGroup.map (algebraMap R K) y₂, ⟨y₂, rfl⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hy₁v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₁ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![e 0 0, 0; e 1 0, (ε : R) * a'] i j) :=
    fun i j => rfl
  have hy₂v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₂ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![(1 : R), e 0 1 * a'; 0, 1] i j) :=
    fun i j => rfl
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, coe_localRepInf_pow, ← he i j]
  simp only [hy₁v, hy₂v]
  fin_cases i <;> fin_cases j <;> simp [map_mul]
  · linear_combination (algebraMap R K (e 0 1)) * hA
  · linear_combination (algebraMap R K (e 1 1)) * hA - (algebraMap R K a') * hD

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem mem_doubleCoset_localRepInf_pow_of_exists_isUnit (m : ℕ) {x : GL (Fin 2) K}
    (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ m)
    (hunit : IsUnit (e 0 0) ∨ IsUnit (e 0 1) ∨ IsUnit (e 1 0) ∨ IsUnit (e 1 1)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
  have hwU : weylInt R K ∈ integralSubgroup R K := weylInt_mem
  rcases hunit with ha | hb | hc | hd
  · exact mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m e he ε hdetR ha
  · have hmem : x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
      refine mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m
        (Matrix.of fun i j => e i (Equiv.swap 0 1 j)) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hb
    have := HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)
    rwa [mul_inv_cancel_right] at this
  · have hmem : weylInt R K * x
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
      refine mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) j) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hc
    have := HeckePair.mul_mem_doubleCoset hmem (inv_mem hwU)
    rwa [inv_mul_cancel_left] at this
  · have hmem : weylInt R K * x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
      refine mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) (Equiv.swap 0 1 j)) (fun i j => ?_) ε ?_ ?_
      · rw [Units.val_mul, Units.val_mul, coe_weylInt]
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i <;> fin_cases j <;> simp [he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
        linear_combination hdetR
      · simpa using hd
    have h' := HeckePair.mul_mem_doubleCoset
      (HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)) (inv_mem hwU)
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at h'

omit [IsFractionRing R K] in

theorem exists_eq_center_mul_of_forall_not_isUnit (hϖ : Irreducible ϖ) (m : ℕ)
    {x : GL (Fin 2) K} (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ (m + 2))
    (hnot : ¬ (IsUnit (e 0 0) ∨ IsUnit (e 0 1) ∨ IsUnit (e 1 0) ∨ IsUnit (e 1 1))) :
    ∃ (x' : GL (Fin 2) K) (e' : Matrix (Fin 2) (Fin 2) R),
      x = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x' ∧
      (∀ i j, algebraMap R K (e' i j) = (x' : Matrix (Fin 2) (Fin 2) K) i j) ∧
      e' 0 0 * e' 1 1 - e' 0 1 * e' 1 0 = ε * ϖ ^ m := by
  simp only [not_or] at hnot
  obtain ⟨ha, hb, hc, hd⟩ := hnot
  have hdvd : ∀ i j, ϖ ∣ e i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact dvd_of_not_isUnit ϖ hϖ ha
    · exact dvd_of_not_isUnit ϖ hϖ hb
    · exact dvd_of_not_isUnit ϖ hϖ hc
    · exact dvd_of_not_isUnit ϖ hϖ hd
  choose e₁ he₁ using hdvd
  refine ⟨(diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x, Matrix.of e₁, by rw [mul_inv_cancel_left],
    fun i j => ?_, ?_⟩
  ·
    have h := diagPi_mul_localRepInf_mul_apply ϖ hϖ0
      ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x) i j
    rw [mul_inv_cancel_left, ← he i j, he₁ i j, map_mul] at h
    exact mul_left_cancel₀ hϖ0 h
  · have hϖ2 : ϖ ^ 2 ≠ 0 := pow_ne_zero 2 hϖ.ne_zero
    apply mul_left_cancel₀ hϖ2
    simp only [Matrix.of_apply]
    rw [show ϖ ^ 2 * (↑ε * ϖ ^ m) = ↑ε * ϖ ^ (m + 2) by ring, ← hdetR, he₁ 0 0, he₁ 1 1,
      he₁ 0 1, he₁ 1 0]
    ring

theorem mem_doubleCoset_or_of_det (hϖ : Irreducible ϖ) (k : ℕ) {x : GL (Fin 2) K}
    (hint : ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
      = algebraMap R K ε * algebraMap R K ϖ ^ (k + 3)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ (k + 3)) ∨
      x ∈ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) ∨
      ∃ x'' : GL (Fin 2) K,
        (∀ i j, (x'' : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) ∧
        x = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x'') := by
  have hint' : ∀ i j, ∃ r, algebraMap R K r = (x : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => hint i j
  choose e he using hint'
  obtain ⟨ε, hε⟩ := hdet
  have hinj := IsFractionRing.injective R K
  have hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ (k + 3) := by
    apply hinj
    rw [map_sub, map_mul, map_mul, he, he, he, he, map_mul, map_pow, ← hε, Matrix.det_fin_two]
  by_cases hunit : IsUnit (e 0 0) ∨ IsUnit (e 0 1) ∨ IsUnit (e 1 0) ∨ IsUnit (e 1 1)
  · exact Or.inl (mem_doubleCoset_localRepInf_pow_of_exists_isUnit ϖ hϖ0 (k + 3) e he ε hdetR hunit)
  obtain ⟨x', e', hx', he', hdet'⟩ :=
    exists_eq_center_mul_of_forall_not_isUnit ϖ hϖ0 hϖ (k + 1) e he ε hdetR hunit
  by_cases hunit' : IsUnit (e' 0 0) ∨ IsUnit (e' 0 1) ∨ IsUnit (e' 1 0) ∨ IsUnit (e' 1 1)
  · right; left
    have hm := mem_doubleCoset_localRepInf_pow_of_exists_isUnit ϖ hϖ0 (k + 1) e' he' ε hdet' hunit'
    obtain ⟨u, hu, v, hv, huv⟩ := HeckePair.mem_doubleCoset_iff.mp hm
    have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
        = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g :=
      Subgroup.mem_center_iff.mp (diagPi_mul_localRepInf_mem_center' ϖ hϖ0)
    refine HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, v, hv, ?_⟩
    have hl2 : localRepInf ϖ hϖ0 ^ (k + 2) = localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1) :=
      pow_succ' _ _
    rw [hx', ← huv, hl2, ← mul_assoc (diagPi ϖ hϖ0), ← mul_assoc u, hzc u]
    simp only [mul_assoc]
  · right; right

    simp only [not_or] at hunit'
    obtain ⟨ha, hb, hc, hd⟩ := hunit'
    have hdvd : ∀ i j, ϖ ∣ e' i j := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact dvd_of_not_isUnit ϖ hϖ ha
      · exact dvd_of_not_isUnit ϖ hϖ hb
      · exact dvd_of_not_isUnit ϖ hϖ hc
      · exact dvd_of_not_isUnit ϖ hϖ hd
    choose e₁ he₁ using hdvd
    refine ⟨(diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x', fun i j => ?_, ?_⟩
    · have h := diagPi_mul_localRepInf_mul_apply ϖ hϖ0
        ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x') i j
      rw [mul_inv_cancel_left, ← he' i j, he₁ i j, map_mul] at h
      exact ⟨e₁ i j, mul_left_cancel₀ hϖ0 h⟩
    · rw [mul_inv_cancel_left, hx']

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem localRepSome_inv_mul_diagPi_mul_localRepInf_pow (c : R) (k : ℕ) :
    (localRepSome ϖ hϖ0 c)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
      = localRepInf ϖ hϖ0 ^ (k + 2) * unipotentInt K (-(c * ϖ ^ (k + 1))) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_localRepSome_inv, coe_diagPi,
    coe_localRepInf_pow, coe_unipotentInt, map_neg, map_mul, map_pow]
  set π : K := algebraMap R K ϖ with hπdef
  set c' : K := algebraMap R K c with hc'def
  have hπ : π⁻¹ * π ^ (k + 2) = π ^ (k + 1) := by
    rw [pow_succ' _ (k + 1), inv_mul_cancel_left₀ hϖ0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hϖ0]
  rw [mul_assoc, hπ]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem diagPi_mul_localRepInf_pow_succ (k : ℕ) :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1) := by
  rw [mul_assoc]
  congr 1
  exact pow_succ' _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem localRepInf_inv_mul_diagPi_mul_localRepInf_pow (k : ℕ) :
    (localRepInf ϖ hϖ0)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ k := by
  have hl1 : localRepInf ϖ hϖ0 ^ (k + 1) = localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ k :=
    pow_succ' _ _
  calc (localRepInf ϖ hϖ0)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
      = (localRepInf ϖ hϖ0)⁻¹ * (localRepInf ϖ hϖ0 * diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1)) := by
        rw [diagPi_mul_localRepInf_pow_succ, diagPi_mul_localRepInf_comm]
    _ = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1) := by rw [mul_assoc, inv_mul_cancel_left]
    _ = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ k := by rw [hl1, ← mul_assoc]

theorem heckeIndicator_diagPi_mul_localRepInf_pow_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀] (k : ℕ)
    (hk2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 2)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hk3 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 3)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hSk : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)}) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) hk2
      = (HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 3)) hk3 :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀)
        + (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀)
          • HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) hSk := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hsys := isHeckeCosetSystem_localReps ϖ hϖ0 hϖ
  have hz := diagPi_mul_localRepInf_mem_center' ϖ hϖ0
  have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g := Subgroup.mem_center_iff.mp hz

  have hTint : ∀ {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) →
        ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
    fun hy => entries_mem_range_of_mem_doubleCoset (entries_mem_range_diagPi ϖ hϖ0) hy
  have hLint : ∀ (m : ℕ) {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) →
        ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
    fun m {_} hy => entries_mem_range_of_mem_doubleCoset (entries_mem_range_localRepInf_pow ϖ hϖ0 m) hy

  have hBz : ∀ {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) →
        ∃ y' : GL (Fin 2) K,
          (∀ i j, (y' : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) ∧
          y = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * y' := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
    refine ⟨u * (localRepInf ϖ hϖ0 ^ (k + 1) * v),
      entries_mem_range_mul (entries_mem_range_of_mem_integralSubgroup hu)
        (entries_mem_range_mul (entries_mem_range_localRepInf_pow ϖ hϖ0 (k + 1))
          (entries_mem_range_of_mem_integralSubgroup hv)), ?_⟩
    rw [diagPi_mul_localRepInf_pow_succ, ← mul_assoc (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0),
      ← hzc u]
    simp only [mul_assoc]

  have hAB : localRepInf ϖ hϖ0 ^ (k + 3)
      ∉ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) := by
    intro h
    obtain ⟨y', hy', hyy⟩ := hBz h
    exact center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 3) hy'
      (by rw [← hyy]; exact HeckePair.self_mem_doubleCoset _)
  have hBA : diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ (k + 3)) := by
    rw [diagPi_mul_localRepInf_pow_succ]
    exact center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 3)
      (entries_mem_range_localRepInf_pow ϖ hϖ0 (k + 1))
  ext x
  simp only [HeckePair.coe_apply_add, HeckePair.coe_apply_smul]
  by_cases hxA : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ (k + 3))
  ·
    have hxB : x ∉ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) :=
      fun h => hAB (HeckePair.mem_doubleCoset_trans h (HeckePair.mem_doubleCoset_comm.mp hxA))
    rw [HeckePair.heckeIndicator_apply_of_mem hk3 hxA,
      HeckePair.heckeIndicator_apply_of_notMem hSk hxB, mul_zero, add_zero]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hxA]
    have hnone : (localRepInf ϖ hϖ0)⁻¹ * localRepInf ϖ hϖ0 ^ (k + 3) = localRepInf ϖ hϖ0 ^ (k + 2) := by
      have hl3 : localRepInf ϖ hϖ0 ^ (k + 3) = localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2) :=
        pow_succ' _ _
      rw [hl3, inv_mul_cancel_left]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys, Fintype.sum_option, localReps_none, hnone,
      HeckePair.heckeIndicator_apply_of_mem _ (HeckePair.self_mem_doubleCoset _)]
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [localReps_some]
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_

    obtain ⟨r, hr⟩ := hLint (k + 2) hmem 0 0
    rw [Units.val_mul, coe_localRepSome_inv, coe_localRepInf_pow] at hr
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hr
    exact algebraMap_mul_ne_one ϖ hϖ.not_isUnit r (by rw [hr, mul_inv_cancel₀ hϖ0])
  by_cases hxB : x ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem hk3 hxA,
      HeckePair.heckeIndicator_apply_of_mem hSk hxB, zero_add, mul_one]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hxB]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys, Fintype.sum_option, localReps_none,
      localRepInf_inv_mul_diagPi_mul_localRepInf_pow,
      HeckePair.heckeIndicator_apply_of_notMem _
        (center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 2)
          (entries_mem_range_localRepInf_pow ϖ hϖ0 k)), zero_add]
    have hterm : ∀ c : R ⧸ Ideal.span {ϖ},
        ((HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) hk2 :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀)
            ((localReps ϖ hϖ0 (some c))⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))) = 1 := by
      intro c
      rw [localReps_some, localRepSome_inv_mul_diagPi_mul_localRepInf_pow]
      exact HeckePair.heckeIndicator_apply_of_mem _
        (HeckePair.doubleCoset_mul_mem (HeckePair.self_mem_doubleCoset _) (unipotentInt_mem _))
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem hk3 hxA,
      HeckePair.heckeIndicator_apply_of_notMem hSk hxB, mul_zero, add_zero,
      HeckePair.heckeIndicator_mul_apply_eq_sum hsys]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_
    have hri := hsys.mem_doubleCoset i

    have hx_eq : x = localReps ϖ hϖ0 i * ((localReps ϖ hϖ0 i)⁻¹ * x) := by
      rw [mul_inv_cancel_left]
    have hint : ∀ i' j', (x : Matrix (Fin 2) (Fin 2) K) i' j' ∈ Set.range (algebraMap R K) := by
      rw [hx_eq]
      exact entries_mem_range_mul (hTint hri) (hLint (k + 2) hmem)
    have hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
        = algebraMap R K ε * algebraMap R K ϖ ^ (k + 3) := by
      obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_doubleCoset_diagPi ϖ hϖ0 hri
      obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_doubleCoset_localRepInf_pow ϖ hϖ0 (k + 2) hmem
      refine ⟨η₁ * η₂, ?_⟩
      rw [hx_eq, Units.val_mul, Matrix.det_mul, h₁, h₂, Units.val_mul, map_mul]
      ring
    rcases mem_doubleCoset_or_of_det ϖ hϖ0 hϖ k hint hdet with h | h | ⟨x'', hx'', hxx⟩
    · exact hxA h
    · exact hxB h
    ·
      have hzr : ∀ i' j', ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (localReps ϖ hϖ0 i)⁻¹ * x'' :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i' j' ∈ Set.range (algebraMap R K) := by
        refine entries_mem_range_mul (fun i' j' => ?_) hx''
        cases i with
        | none =>
          rw [localReps_none, mul_inv_cancel_right]
          exact entries_mem_range_diagPi ϖ hϖ0 i' j'
        | some c =>
          rw [localReps_some, Units.val_mul, coe_localRepSome_inv, Units.val_mul, coe_diagPi,
            coe_localRepInf]
          set π : K := algebraMap R K ϖ with hπdef
          have h00 : π * π⁻¹ = 1 := mul_inv_cancel₀ hϖ0
          fin_cases i' <;> fin_cases j'
          · exact ⟨1, by simp [Matrix.mul_apply, Fin.sum_univ_two, h00]⟩
          · refine ⟨-Quotient.out c, ?_⟩
            simp [Matrix.mul_apply, Fin.sum_univ_two]
            rw [hπdef, mul_comm, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one]
          · exact ⟨0, by simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
          · exact ⟨ϖ, by simp [Matrix.mul_apply, Fin.sum_univ_two, hπdef]⟩
      refine center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 2) hzr ?_
      have : (localReps ϖ hϖ0 i)⁻¹ * x
          = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
            * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (localReps ϖ hϖ0 i)⁻¹ * x'') := by
        rw [hxx]
        calc (localReps ϖ hϖ0 i)⁻¹
              * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x''))
            = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
                * ((localReps ϖ hϖ0 i)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x'')) := by
              rw [← mul_assoc, hzc, mul_assoc]
          _ = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
                * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (localReps ϖ hϖ0 i)⁻¹ * x'') := by
              rw [← mul_assoc ((localReps ϖ hϖ0 i)⁻¹), hzc]
      rw [← this]
      exact hmem

end RecursionDVR
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section Basic

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem diag_two_pow (x y : K) (n : ℕ) :
    (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) K) ^ n = !![x ^ n, 0; 0, y ^ n] := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem commute_diagPi_localRepInf : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0) := by
  apply Units.ext
  change (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
    = (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_diagPi_zpow_mul_localRepInf_zpow (a b : ℕ) :
    ((diagPi ϖ hϖ0 ^ (a : ℤ) * localRepInf ϖ hϖ0 ^ (b : ℤ) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)
      = (cartanDiag ϖ a b).map (algebraMap R K) := by
  rw [zpow_natCast, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, coe_diagPi, coe_localRepInf, diag_two_pow, diag_two_pow,
    one_pow, one_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, cartanDiag, map_pow]

theorem coe_map_algebraMap (k : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map (algebraMap R K) k : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)
      = (k : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := rfl

theorem coe_diagPi_mul_coe_localRepInf'' :
    (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagPi_mul_localRepInf_mem_center'' :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  simp only [Units.val_mul]
  rw [coe_diagPi_mul_coe_localRepInf'', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem diagPi_mul_localRepInf_pow_mul_apply (N : ℕ) (m : GL (Fin 2) K) (i j : Fin 2) :
    (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      = algebraMap R K ϖ ^ N * (m : Matrix (Fin 2) (Fin 2) K) i j := by
  induction N generalizing m with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ N ih =>
    rw [pow_succ, mul_assoc, ih, Units.val_mul, Units.val_mul, coe_diagPi_mul_coe_localRepInf'',
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc]

theorem diagPi_mul_localRepInf_zpow_mul (N m n : ℤ) :
    (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n)
      = diagPi ϖ hϖ0 ^ (N + m) * localRepInf ϖ hϖ0 ^ (N + n) := by
  have htl := commute_diagPi_localRepInf ϖ hϖ0
  have hc : localRepInf ϖ hϖ0 ^ N * diagPi ϖ hϖ0 ^ m = diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ N :=
    (htl.symm.zpow_zpow N m).eq
  rw [htl.mul_zpow, mul_assoc, ← mul_assoc (localRepInf ϖ hϖ0 ^ N), hc, mul_assoc, ← _root_.zpow_add,
    ← mul_assoc, ← _root_.zpow_add]

end Basic
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

include hϖ0 in

theorem exists_pow_mul_mem_range (hϖ : Irreducible ϖ) (x : K) :
    ∃ n : ℕ, algebraMap R K ϖ ^ n * x ∈ Set.range (algebraMap R K) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hu : algebraMap R K u * algebraMap R K ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  rw [hbu, map_mul, map_mul, map_pow, mul_div_assoc', mul_comm (algebraMap R K ϖ ^ n),
    mul_div_mul_right _ _ (pow_ne_zero n hϖ0), div_eq_mul_inv, inv_eq_of_mul_eq_one_right hu]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem pow_mul_mem_range_of_le {x : K} {n N : ℕ} (hnN : n ≤ N)
    (hx : algebraMap R K ϖ ^ n * x ∈ Set.range (algebraMap R K)) :
    algebraMap R K ϖ ^ N * x ∈ Set.range (algebraMap R K) := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnN
  refine ⟨ϖ ^ k * r, ?_⟩
  rw [map_mul, map_pow, hr, pow_add]
  ring

theorem exists_mem_doubleCoset_zpow (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) :
    ∃ m n : ℤ, m ≤ n ∧ g ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) := by

  choose nf hnf using fun i j => exists_pow_mul_mem_range ϖ hϖ0 hϖ ((g : Matrix (Fin 2) (Fin 2) K) i j)
  set N : ℕ := ∑ p : Fin 2 × Fin 2, nf p.1 p.2
  have hle : ∀ i j, nf i j ≤ N := fun i j =>
    Finset.single_le_sum (f := fun p : Fin 2 × Fin 2 => nf p.1 p.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  have hint : ∀ i j, ∃ r : R, algebraMap R K r =
      (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    obtain ⟨r, hr⟩ := pow_mul_mem_range_of_le ϖ (hle i j) (hnf i j)
    exact ⟨r, by rw [diagPi_mul_localRepInf_pow_mul_apply, hr]⟩
  choose e he using hint
  have hinj := IsFractionRing.injective R K

  have hemap : (Matrix.of e : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K)
      = (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    exact he i j
  have hdet : (Matrix.of e : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g)
    rw [← hemap, det_map_algebraMap, h0, map_zero]

  obtain ⟨a, b, hab, k₁, k₂, hk⟩ := LocalGL2.exists_cartanRel_cartanDiag hϖ (Matrix.of e) hdet

  have hGL : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ N * g
      = Matrix.GeneralLinearGroup.map (algebraMap R K) k₁
          * (diagPi ϖ hϖ0 ^ (a : ℤ) * localRepInf ϖ hϖ0 ^ (b : ℤ))
          * Matrix.GeneralLinearGroup.map (algebraMap R K) k₂ := by
    apply Units.ext
    rw [← hemap, hk, Units.val_mul, Units.val_mul, coe_map_algebraMap, coe_map_algebraMap,
      coe_diagPi_zpow_mul_localRepInf_zpow, Matrix.map_mul, Matrix.map_mul]
  refine ⟨(a : ℤ) - N, (b : ℤ) - N, by omega, ?_⟩
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨Matrix.GeneralLinearGroup.map (algebraMap R K) k₁, ⟨k₁, rfl⟩,
      Matrix.GeneralLinearGroup.map (algebraMap R K) k₂, ⟨k₂, rfl⟩, ?_⟩

  have hzc : ∀ x : GL (Fin 2) K, x * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ)
      = (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ) * x := fun x =>
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center'' ϖ hϖ0) N) x
  have hGL' : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ) * g
      = Matrix.GeneralLinearGroup.map (algebraMap R K) k₁
          * (diagPi ϖ hϖ0 ^ (a : ℤ) * localRepInf ϖ hϖ0 ^ (b : ℤ))
          * Matrix.GeneralLinearGroup.map (algebraMap R K) k₂ := by
    rw [zpow_natCast]; exact hGL
  apply mul_left_cancel (a := (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ))
  rw [hGL', ← mul_assoc, ← mul_assoc, ← hzc,
    mul_assoc _ ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (N : ℤ)),
    diagPi_mul_localRepInf_zpow_mul, add_sub_cancel, add_sub_cancel]

theorem zpow_pair_unique (hϖ : Irreducible ϖ) {m n m' n' : ℤ} (hmn : m ≤ n) (hmn' : m' ≤ n')
    (h : diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 ^ m' * localRepInf ϖ hϖ0 ^ n')) :
    m = m' ∧ n = n' := by
  obtain ⟨u, hu, v, hv, huv⟩ := HeckePair.mem_doubleCoset_iff.mp h
  obtain ⟨k₁, rfl⟩ := hu
  obtain ⟨k₂, rfl⟩ := hv

  set M : ℕ := (-m).toNat + (-m').toNat with hM
  have hm0 : 0 ≤ m + M := by omega
  have hn0 : 0 ≤ n + M := by omega
  have hm0' : 0 ≤ m' + M := by omega
  have hn0' : 0 ≤ n' + M := by omega
  have hzc : ∀ x : GL (Fin 2) K, x * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ)
      = (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ) * x := fun x =>
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center'' ϖ hϖ0) M) x
  have huv' := congrArg ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ) * ·) huv
  rw [← mul_assoc, ← mul_assoc, ← hzc,
    mul_assoc _ ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (M : ℤ)),
    diagPi_mul_localRepInf_zpow_mul, diagPi_mul_localRepInf_zpow_mul, add_comm (M : ℤ) m',
    add_comm (M : ℤ) n', add_comm (M : ℤ) m, add_comm (M : ℤ) n,
    ← Int.toNat_of_nonneg hm0, ← Int.toNat_of_nonneg hn0, ← Int.toNat_of_nonneg hm0',
    ← Int.toNat_of_nonneg hn0'] at huv'

  have hmat := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) huv'
  rw [Units.val_mul, Units.val_mul, coe_map_algebraMap, coe_map_algebraMap,
    coe_diagPi_zpow_mul_localRepInf_zpow, coe_diagPi_zpow_mul_localRepInf_zpow,
    ← Matrix.map_mul, ← Matrix.map_mul] at hmat
  have hR : (k₁ : Matrix (Fin 2) (Fin 2) R) * cartanDiag ϖ (m' + ↑M).toNat (n' + ↑M).toNat
        * (k₂ : Matrix (Fin 2) (Fin 2) R)
      = cartanDiag ϖ (m + ↑M).toNat (n + ↑M).toNat :=
    Matrix.map_injective (f := algebraMap R K) (IsFractionRing.injective R K) hmat
  have hrel : CartanRel (cartanDiag ϖ (m + ↑M).toNat (n + ↑M).toNat)
      (cartanDiag ϖ (m' + ↑M).toNat (n' + ↑M).toNat) := ⟨k₁, k₂, hR.symm⟩
  have hiff := (LocalGL2.cartanDiag_cartanRel_iff hϖ (by omega) (by omega)).mp hrel
  omega

end DVR
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace HeckePair
p2m_export "HeckePair" "HeckeAlgebra apply_left_mul apply_mul_right finite_cosets ext coe_apply_add coe_apply_smul convTerm_mk support_convTerm_subset mul_apply one_mul mul_one mul_zero add_mul mul_add smul_mul mul_smul_comm mul_assoc doubleCoset mem_doubleCoset_iff self_mem_doubleCoset mul_mem_doubleCoset doubleCoset_mul_mem image_mk_doubleCoset heckeIndicator heckeIndicator_apply_of_mem heckeIndicator_apply_of_notMem heckeIndicator_of_mem"
p2m_open "HeckePair"

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

theorem apply_eq_of_mem_doubleCoset'' (f : HeckeAlgebra U R₀) {g x : G}
    (hx : x ∈ doubleCoset U g) : (f : G → R₀) x = (f : G → R₀) g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  rw [apply_mul_right f hv, apply_left_mul f hu]

theorem coe_apply_sum {ι : Type*} (s : Finset ι) (F : ι → HeckeAlgebra U R₀) (x : G) :
    ((∑ i ∈ s, F i : HeckeAlgebra U R₀) : G → R₀) x = ∑ i ∈ s, (F i : G → R₀) x := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, coe_apply_add, ih]

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end HeckePair
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section S2b

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem zpow_pair_eq_of_mem_of_mem (hϖ : Irreducible ϖ) {m n m' n' : ℤ} (hmn : m ≤ n)
    (hmn' : m' ≤ n') {x : GL (Fin 2) K}
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n))
    (hx' : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m' * localRepInf ϖ hϖ0 ^ n')) :
    m = m' ∧ n = n' := by
  refine zpow_pair_unique ϖ hϖ0 hϖ hmn hmn' ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨u', hu', v', hv', h'⟩ := HeckePair.mem_doubleCoset_iff.mp hx'
  refine HeckePair.mem_doubleCoset_iff.mpr ⟨u⁻¹ * u', mul_mem (inv_mem hu) hu', v' * v⁻¹,
    mul_mem hv' (inv_mem hv), ?_⟩
  have h'' : u⁻¹ * (u' * (diagPi ϖ hϖ0 ^ m' * localRepInf ϖ hϖ0 ^ n') * v') * v⁻¹
      = diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n := by
    rw [h']; group
  simpa only [mul_assoc] using h''

theorem exists_basis_heckeIndicator_zpow_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ)
    {R₀ : Type*} [CommRing R₀]
    (hfin : ∀ g : GL (Fin 2) K,
      (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
        Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ b : Module.Basis {p : ℤ × ℤ // p.1 ≤ p.2} R₀ (HeckePair.HeckeAlgebra (integralSubgroup R K) R₀),
      ∀ p, b p = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 ^ p.1.1 * localRepInf ϖ hϖ0 ^ p.1.2) (hfin _) := by
  classical

  set d : {p : ℤ × ℤ // p.1 ≤ p.2} → GL (Fin 2) K :=
    fun p => diagPi ϖ hϖ0 ^ p.1.1 * localRepInf ϖ hϖ0 ^ p.1.2 with hd
  set v : {p : ℤ × ℤ // p.1 ≤ p.2} → HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ :=
    fun p => HeckePair.heckeIndicator R₀ (d p) (hfin _) with hv

  choose κm κn hκle hκmem using fun x : GL (Fin 2) K => exists_mem_doubleCoset_zpow ϖ hϖ0 hϖ x
  let κ : GL (Fin 2) K → {p : ℤ × ℤ // p.1 ≤ p.2} := fun x => ⟨(κm x, κn x), hκle x⟩
  have hκ : ∀ x, x ∈ HeckePair.doubleCoset (integralSubgroup R K) (d (κ x)) := fun x => hκmem x

  have hmem_iff : ∀ (x : GL (Fin 2) K) (p : {p : ℤ × ℤ // p.1 ≤ p.2}),
      x ∈ HeckePair.doubleCoset (integralSubgroup R K) (d p) ↔ p = κ x := by
    intro x p
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := zpow_pair_eq_of_mem_of_mem ϖ hϖ0 hϖ p.2 (hκle x) hx (hκ x)
      exact Subtype.ext (Prod.ext h1 h2)
    · rintro rfl
      exact hκ x

  have hval : ∀ (p : {p : ℤ × ℤ // p.1 ≤ p.2}) (x : GL (Fin 2) K),
      (v p : GL (Fin 2) K → R₀) x = if p = κ x then 1 else 0 := by
    intro p x
    by_cases h : p = κ x
    · rw [if_pos h]
      exact HeckePair.heckeIndicator_apply_of_mem _ ((hmem_iff x p).mpr h)
    · rw [if_neg h]
      exact HeckePair.heckeIndicator_apply_of_notMem _ (fun hx => h ((hmem_iff x p).mp hx))

  have hli : LinearIndependent R₀ v := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h := congrArg
      (fun f : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ => (f : GL (Fin 2) K → R₀) (d i)) hsum
    rw [HeckePair.coe_apply_sum] at h
    simp only [HeckePair.coe_apply_smul, hval, mul_boole, Finset.sum_ite_eq'] at h
    have hκi : κ (d i) = i := ((hmem_iff (d i) i).mp (HeckePair.self_mem_doubleCoset _)).symm
    rw [hκi, if_pos hi] at h
    exact h

  have hsp : ⊤ ≤ Submodule.span R₀ (Set.range v) := by
    intro f _
    set P : Finset {p : ℤ × ℤ // p.1 ≤ p.2} :=
      f.2.finite_cosets.toFinset.image (fun q => κ q.out) with hP
    have hf : f = ∑ p ∈ P, ((f : GL (Fin 2) K → R₀) (d p)) • v p := by
      apply HeckePair.ext
      intro x
      rw [HeckePair.coe_apply_sum]
      simp only [HeckePair.coe_apply_smul, hval, mul_boole, Finset.sum_ite_eq']
      by_cases hxP : κ x ∈ P
      · rw [if_pos hxP]
        exact HeckePair.apply_eq_of_mem_doubleCoset'' f (hκ x)
      · rw [if_neg hxP]
        by_contra hfx
        apply hxP

        have hq : (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K)
            ∈ f.2.finite_cosets.toFinset :=
          (Set.Finite.mem_toFinset _).mpr ⟨x, hfx, rfl⟩
        refine Finset.mem_image.mpr ⟨QuotientGroup.mk x, hq, ?_⟩

        have hu : x⁻¹ * (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K).out
            ∈ integralSubgroup R K :=
          QuotientGroup.eq.mp ((QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K).out_eq').symm
        have hout : (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K).out
            ∈ HeckePair.doubleCoset (integralSubgroup R K) (d (κ x)) := by
          have := HeckePair.doubleCoset_mul_mem (hκ x) hu
          rwa [mul_inv_cancel_left] at this
        exact ((hmem_iff _ _).mp hout).symm
    rw [hf]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun p => Module.Basis.mk_apply hli hsp p⟩

end S2b
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

theorem existsUnique_mem_doubleCoset_zpow_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) :
    ∃! p : ℤ × ℤ, p.1 ≤ p.2 ∧
      g ∈ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 ^ p.1 * localRepInf ϖ hϖ0 ^ p.2) := by
  obtain ⟨m, n, hmn, hg⟩ := exists_mem_doubleCoset_zpow ϖ hϖ0 hϖ g
  refine ⟨(m, n), ⟨hmn, hg⟩, ?_⟩
  rintro ⟨m', n'⟩ ⟨hmn', hg'⟩

  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hg
  have h1 : diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (u * (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) * v) :=
    HeckePair.mem_doubleCoset_iff.mpr ⟨u⁻¹, inv_mem hu, v⁻¹, inv_mem hv, by group⟩
  have h2 : diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 ^ m' * localRepInf ϖ hϖ0 ^ n') := by
    obtain ⟨u', hu', v', hv', huv'⟩ := HeckePair.mem_doubleCoset_iff.mp hg'
    obtain ⟨u₁, hu₁, v₁, hv₁, h₁⟩ := HeckePair.mem_doubleCoset_iff.mp h1
    refine HeckePair.mem_doubleCoset_iff.mpr ⟨u₁ * u', mul_mem hu₁ hu', v' * v₁, mul_mem hv' hv₁, ?_⟩
    rw [← h₁, ← huv']
    group
  obtain ⟨rfl, rfl⟩ := zpow_pair_unique ϖ hϖ0 hϖ hmn hmn' h2
  rfl

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section Finite

variable {G : Type*} [Group G] {U : Subgroup G}

theorem finite_image_mk_mul {A B : Set G}
    (hA : (QuotientGroup.mk '' A : Set (G ⧸ U)).Finite)
    (hB : (QuotientGroup.mk '' B : Set (G ⧸ U)).Finite)
    (hUB : ∀ u ∈ U, ∀ b ∈ B, u * b ∈ B) :
    (QuotientGroup.mk '' (A * B) : Set (G ⧸ U)).Finite := by
  have hsub : (QuotientGroup.mk '' (A * B) : Set (G ⧸ U))
      ⊆ ⋃ q ∈ (QuotientGroup.mk '' A : Set (G ⧸ U)),
          (fun c : G ⧸ U => (q.out : G) • c) '' (QuotientGroup.mk '' B : Set (G ⧸ U)) := by
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨QuotientGroup.mk a, ⟨a, ha, rfl⟩, ?_⟩
    have hu : ((QuotientGroup.mk a : G ⧸ U).out)⁻¹ * a ∈ U :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk a : G ⧸ U))
    refine ⟨QuotientGroup.mk (((QuotientGroup.mk a : G ⧸ U).out)⁻¹ * a * b),
      ⟨_, hUB _ hu b hb, rfl⟩, ?_⟩
    show ((QuotientGroup.mk a : G ⧸ U).out : G) • (QuotientGroup.mk _ : G ⧸ U) = QuotientGroup.mk (a * b)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  exact Set.Finite.subset (Set.Finite.biUnion hA fun q _ => hB.image _) hsub

theorem finite_image_mk_coe : (QuotientGroup.mk '' (U : Set G) : Set (G ⧸ U)).Finite := by
  refine Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk 1)) ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [Set.mem_singleton_iff]
  refine QuotientGroup.eq.mpr ?_
  rw [mul_one]
  exact inv_mem hu

theorem image_mk_mul_singleton_subset_of_mem_doubleCoset {g d : G}
    (hg : g ∈ HeckePair.doubleCoset U d) :
    (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U))
      ⊆ QuotientGroup.mk '' ((U : Set G) * {d}) := by
  rw [← HeckePair.image_mk_doubleCoset, ← HeckePair.image_mk_doubleCoset]
  refine Set.image_mono fun x hx => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hg
  obtain ⟨u', hu', v', hv', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨u' * u, mul_mem hu' hu, v * v', mul_mem hv hv', by group⟩

theorem image_mk_mul_singleton_center_mul_subset {z h : G} (hz : z ∈ Subgroup.center G) :
    (QuotientGroup.mk '' ((U : Set G) * {z * h}) : Set (G ⧸ U))
      ⊆ (fun c : G ⧸ U => z • c) '' (QuotientGroup.mk '' ((U : Set G) * {h}) : Set (G ⧸ U)) := by
  rintro _ ⟨_, ⟨u, hu, _, rfl, rfl⟩, rfl⟩
  refine ⟨QuotientGroup.mk (u * h), ⟨u * h, ⟨u, hu, h, rfl, rfl⟩, rfl⟩, ?_⟩
  show z • (QuotientGroup.mk (u * h) : G ⧸ U) = QuotientGroup.mk (u * (z * h))
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    (Subgroup.mem_center_iff.mp hz) u]

end Finite
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

section S0

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

omit [IsFractionRing R K] in

theorem finite_image_mk_integralSubgroup_mul_doubleCoset_pow (hϖ : Irreducible ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})] (r : ℕ) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) ^ r) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by
  induction r with
  | zero =>
    rw [pow_zero, mul_one]
    exact finite_image_mk_coe
  | succ r ih =>
    rw [pow_succ, ← mul_assoc]
    refine finite_image_mk_mul ih ?_ fun u hu b hb => HeckePair.mul_mem_doubleCoset hb hu
    rw [HeckePair.image_mk_doubleCoset]
    exact finite_image_mul_diagPi ϖ hϖ0 hϖ

theorem finite_image_integralSubgroup_mul_singleton_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (g : GL (Fin 2) K) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by
  have hϖ0 : algebraMap R K ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))

  obtain ⟨m, n, hmn, hg⟩ := exists_mem_doubleCoset_zpow ϖ hϖ0 hϖ g
  refine Set.Finite.subset ?_ (image_mk_mul_singleton_subset_of_mem_doubleCoset hg)

  have htl := commute_diagPi_localRepInf ϖ hϖ0
  have hz : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ m ∈ Subgroup.center (GL (Fin 2) K) :=
    Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center'' ϖ hϖ0) m
  have hd : diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n
      = (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ m * localRepInf ϖ hϖ0 ^ (n - m).toNat := by
    rw [htl.mul_zpow, mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      ← _root_.zpow_add, add_sub_cancel]
  rw [hd]
  refine Set.Finite.subset (Set.Finite.image _ ?_) (image_mk_mul_singleton_center_mul_subset hz)

  have hl : localRepInf ϖ hϖ0 ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) :=
    HeckePair.mem_doubleCoset_iff.mpr ⟨weylInt R K, weylInt_mem, weylInt R K, weylInt_mem, rfl⟩
  refine Set.Finite.subset (finite_image_mk_integralSubgroup_mul_doubleCoset_pow ϖ hϖ0 hϖ _)
    (Set.image_mono (Set.mul_subset_mul_left (Set.singleton_subset_iff.mpr (Set.pow_mem_pow hl))))

end S0
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace HeckePair
p2m_export "HeckePair" "HeckeAlgebra apply_left_mul apply_mul_right finite_cosets ext coe_apply_add coe_apply_smul convTerm_mk support_convTerm_subset mul_apply one_mul mul_one mul_zero add_mul mul_add smul_mul mul_smul_comm mul_assoc doubleCoset mem_doubleCoset_iff self_mem_doubleCoset mul_mem_doubleCoset doubleCoset_mul_mem image_mk_doubleCoset heckeIndicator heckeIndicator_apply_of_mem heckeIndicator_apply_of_notMem heckeIndicator_of_mem"
p2m_open "HeckePair"

section IndicatorCongr

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

theorem heckeIndicator_congr {g g' : G} (h : g = g')
    (hg : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite)
    (hg' : (QuotientGroup.mk '' ((U : Set G) * {g'}) : Set (G ⧸ U)).Finite) :
    (heckeIndicator R₀ g hg : HeckeAlgebra U R₀) = heckeIndicator R₀ g' hg' := by
  subst h
  rfl

theorem heckeIndicator_eq_of_mem_doubleCoset {g g' : G} (h : g' ∈ doubleCoset U g)
    (hg : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite)
    (hg' : (QuotientGroup.mk '' ((U : Set G) * {g'}) : Set (G ⧸ U)).Finite) :
    (heckeIndicator R₀ g' hg' : HeckeAlgebra U R₀) = heckeIndicator R₀ g hg := by
  ext x
  by_cases hx : x ∈ doubleCoset U g
  · rw [heckeIndicator_apply_of_mem _ hx,
      heckeIndicator_apply_of_mem _ (mem_doubleCoset_trans (mem_doubleCoset_comm.mp h) hx)]
  · rw [heckeIndicator_apply_of_notMem _ hx,
      heckeIndicator_apply_of_notMem _ (fun hx' => hx (mem_doubleCoset_trans h hx'))]

end IndicatorCongr
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end HeckePair
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section RecursionPolynomials

variable {R₀ : Type*} [CommRing R₀]

def satakeP (q : R₀) : ℕ → Polynomial (LaurentPolynomial R₀)
  | 0 => 1
  | 1 => Polynomial.X
  | 2 => Polynomial.X ^ 2 - (q + 1) • Polynomial.C (LaurentPolynomial.T 1)
  | (k + 3) => Polynomial.X * satakeP q (k + 2)
      - q • (Polynomial.C (LaurentPolynomial.T 1) * satakeP q (k + 1))

theorem satakeP_zero (q : R₀) : satakeP q 0 = 1 := by
  rw [satakeP]

theorem satakeP_one (q : R₀) : satakeP q 1 = Polynomial.X := by
  rw [satakeP]

theorem satakeP_two (q : R₀) :
    satakeP q 2 = Polynomial.X ^ 2 - (q + 1) • Polynomial.C (LaurentPolynomial.T 1) := by
  rw [satakeP]

theorem satakeP_add_three (q : R₀) (k : ℕ) :
    satakeP q (k + 3) = Polynomial.X * satakeP q (k + 2)
      - q • (Polynomial.C (LaurentPolynomial.T 1) * satakeP q (k + 1)) := by
  rw [satakeP]

theorem X_mul_satakeP (q : R₀) : ∀ b : ℕ, ∃ c : R₀, ∃ b' : ℕ,
    Polynomial.X * satakeP q b
      = satakeP q (b + 1) + c • (Polynomial.C (LaurentPolynomial.T 1) * satakeP q b')
  | 0 => ⟨0, 0, by
      rw [zero_smul, add_zero, zero_add, satakeP_zero, satakeP_one, mul_one]⟩
  | 1 => ⟨q + 1, 0, by
      show Polynomial.X * satakeP q 1
        = satakeP q 2 + (q + 1) • (Polynomial.C (LaurentPolynomial.T 1) * satakeP q 0)
      rw [satakeP_one, satakeP_two, satakeP_zero, mul_one, sub_add_cancel, pow_two]⟩
  | (k + 2) => ⟨q, k + 1, by
      show Polynomial.X * satakeP q (k + 2)
        = satakeP q (k + 3) + q • (Polynomial.C (LaurentPolynomial.T 1) * satakeP q (k + 1))
      rw [satakeP_add_three, sub_add_cancel]⟩

theorem span_C_T_mul_satakeP (q : R₀) :
    Submodule.span R₀ (Set.range fun ab : ℤ × ℕ =>
      Polynomial.C (LaurentPolynomial.T ab.1) * satakeP q ab.2) = ⊤ := by
  set M := Submodule.span R₀ (Set.range fun ab : ℤ × ℕ =>
      Polynomial.C (LaurentPolynomial.T ab.1) * satakeP q ab.2) with hM
  have hgen : ∀ (a : ℤ) (b : ℕ), Polynomial.C (LaurentPolynomial.T a) * satakeP q b ∈ M :=
    fun a b => Submodule.subset_span ⟨(a, b), rfl⟩

  have hCT : ∀ (a : ℤ), ∀ m ∈ M, Polynomial.C (LaurentPolynomial.T a) * m ∈ M := by
    intro a m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a', b⟩, rfl⟩ := hx
      show Polynomial.C (LaurentPolynomial.T a)
        * (Polynomial.C (LaurentPolynomial.T a') * satakeP q b) ∈ M
      rw [← mul_assoc, ← map_mul, ← LaurentPolynomial.T_add]
      exact hgen _ _
    | zero => rw [mul_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact M.add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact M.smul_mem r hx

  have hX : ∀ m ∈ M, Polynomial.X * m ∈ M := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      obtain ⟨c, b', h⟩ := X_mul_satakeP q b
      show Polynomial.X * (Polynomial.C (LaurentPolynomial.T a) * satakeP q b) ∈ M
      rw [← mul_assoc, Polynomial.X_mul_C, mul_assoc, h, mul_add, mul_smul_comm, ← mul_assoc,
        ← map_mul, ← LaurentPolynomial.T_add]
      exact M.add_mem (hgen _ _) (M.smul_mem _ (hgen _ _))
    | zero => rw [mul_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact M.add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact M.smul_mem r hx

  have hXpow : ∀ n : ℕ, (Polynomial.X : Polynomial (LaurentPolynomial R₀)) ^ n ∈ M := by
    intro n
    induction n with
    | zero =>
      have h := hgen 0 0
      rw [LaurentPolynomial.T_zero, map_one, one_mul, satakeP_zero] at h
      rwa [pow_zero]
    | succ n ih =>
      rw [pow_succ']
      exact hX _ ih
  have hCX : ∀ (ℓ : LaurentPolynomial R₀) (n : ℕ), Polynomial.C ℓ * Polynomial.X ^ n ∈ M := by
    intro ℓ n
    induction ℓ using LaurentPolynomial.induction_on' with
    | add p p' hp hp' => rw [map_add, add_mul]; exact M.add_mem hp hp'
    | C_mul_T m a =>
      rw [map_mul, mul_assoc]
      have hC : (Polynomial.C (LaurentPolynomial.C a) : Polynomial (LaurentPolynomial R₀))
          = algebraMap R₀ (Polynomial (LaurentPolynomial R₀)) a := by
        rw [Polynomial.algebraMap_apply, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply]
      rw [hC, ← Algebra.smul_def]
      exact M.smul_mem a (hCT m _ (hXpow n))
  refine Submodule.eq_top_iff'.mpr fun p => ?_
  rw [Polynomial.as_sum_range_C_mul_X_pow p]
  exact M.sum_mem fun n _ => hCX _ _

end RecursionPolynomials
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

section Map

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)
variable (R₀ : Type*) [CommRing R₀]

def zInd (n : ℤ) : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ :=
  HeckePair.heckeIndicator R₀ ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ n)
    (HeckePair.finite_image_mk_mul_singleton_of_mem_center
      (Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center ϖ hϖ0) n))

theorem zInd_mul_comm (n : ℤ) (f : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) :
    zInd ϖ hϖ0 R₀ n * f = f * zInd ϖ hϖ0 R₀ n :=
  HeckePair.heckeIndicator_mul_comm_of_mem_center
    (Subgroup.zpow_mem _ (diagPi_mul_localRepInf_mem_center ϖ hϖ0) n) _ f

theorem zInd_zero : zInd ϖ hϖ0 R₀ 0 = 1 :=
  HeckePair.heckeIndicator_of_mem (by rw [zpow_zero]; exact one_mem _) _

theorem zInd_add (m n : ℤ) : zInd ϖ hϖ0 R₀ (m + n) = zInd ϖ hϖ0 R₀ m * zInd ϖ hϖ0 R₀ n := by
  have hz := diagPi_mul_localRepInf_mem_center ϖ hϖ0
  have hzg : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
      * {(diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ m * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ n}) :
        Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite :=
    HeckePair.finite_image_mk_mul_singleton_of_mem_center
      (mul_mem (Subgroup.zpow_mem _ hz m) (Subgroup.zpow_mem _ hz n))
  unfold zInd
  rw [HeckePair.heckeIndicator_center_mul_heckeIndicator (Subgroup.zpow_mem _ hz m) _ _ _ hzg]
  exact HeckePair.heckeIndicator_congr (_root_.zpow_add _ m n) _ _

theorem zInd_one (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
      * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    zInd ϖ hϖ0 R₀ 1 = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS :=
  HeckePair.heckeIndicator_congr (zpow_one _) _ _

def zMonoidHom : Multiplicative ℤ →* HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ where
  toFun n := zInd ϖ hϖ0 R₀ (Multiplicative.toAdd n)
  map_one' := by
    rw [toAdd_one]
    exact zInd_zero ϖ hϖ0 R₀
  map_mul' a b := by
    rw [toAdd_mul]
    exact zInd_add ϖ hϖ0 R₀ _ _

def phi0 : LaurentPolynomial R₀ →ₐ[R₀] HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ :=
  AddMonoidAlgebra.lift R₀ _ ℤ (zMonoidHom ϖ hϖ0 R₀)

theorem phi0_C_mul_T (a : R₀) (n : ℤ) :
    phi0 ϖ hϖ0 R₀ (LaurentPolynomial.C a * LaurentPolynomial.T n) = a • zInd ϖ hϖ0 R₀ n := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  show AddMonoidAlgebra.lift R₀ _ ℤ (zMonoidHom ϖ hϖ0 R₀) (AddMonoidAlgebra.single n a) = _
  rw [AddMonoidAlgebra.lift_single]
  rfl

theorem phi0_T (n : ℤ) : phi0 ϖ hϖ0 R₀ (LaurentPolynomial.T n) = zInd ϖ hϖ0 R₀ n := by
  rw [← one_mul (LaurentPolynomial.T n), ← LaurentPolynomial.C.map_one, phi0_C_mul_T, one_smul]

theorem phi0_mul_comm (p : LaurentPolynomial R₀)
    (f : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) :
    phi0 ϖ hϖ0 R₀ p * f = f * phi0 ϖ hϖ0 R₀ p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, add_mul, mul_add, hp, hp']
  | C_mul_T n a => rw [phi0_C_mul_T, smul_mul_assoc, mul_smul_comm, zInd_mul_comm]

def phi (hT : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
      * {diagPi ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    Polynomial (LaurentPolynomial R₀) →ₐ[R₀] HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ :=
  { Polynomial.eval₂RingHom' (phi0 ϖ hϖ0 R₀).toRingHom (HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) hT)
      (fun a => phi0_mul_comm ϖ hϖ0 R₀ a _) with
    commutes' := fun r => by
      show Polynomial.eval₂ (phi0 ϖ hϖ0 R₀).toRingHom (HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) hT)
          (algebraMap R₀ (Polynomial (LaurentPolynomial R₀)) r) = algebraMap R₀ _ r
      rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
      exact (phi0 ϖ hϖ0 R₀).commutes r }

theorem phi_X (hT : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
      * {diagPi ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    phi ϖ hϖ0 R₀ hT Polynomial.X = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) hT :=
  Polynomial.eval₂_X _ _

theorem phi_C (hT : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
      * {diagPi ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (x : LaurentPolynomial R₀) :
    phi ϖ hϖ0 R₀ hT (Polynomial.C x) = phi0 ϖ hϖ0 R₀ x :=
  Polynomial.eval₂_C _ _

end Map
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

section Assembly

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
variable (R₀ : Type*) [CommRing R₀]
variable (hfin : ∀ g : GL (Fin 2) K,
  (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
    Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in

theorem zInd_one_mul_heckeIndicator_localRepInf_pow (k : ℕ) :
    zInd ϖ hϖ0 R₀ 1 * HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 1)) (hfin _)
      = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) (hfin _) := by
  have hz := diagPi_mul_localRepInf_mem_center ϖ hϖ0
  have heq : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (1 : ℤ) * localRepInf ϖ hϖ0 ^ (k + 1)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2) := by
    rw [zpow_one, mul_assoc, ← pow_succ']
  unfold zInd
  rw [HeckePair.heckeIndicator_center_mul_heckeIndicator (Subgroup.zpow_mem _ hz 1) _ _ _ (hfin _)]
  exact HeckePair.heckeIndicator_congr heq _ _

include hϖ in

theorem phi_satakeP : ∀ b : ℕ,
    phi ϖ hϖ0 R₀ (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        (satakeP (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) b)
      = HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ b) (hfin _)
  | 0 => by
    rw [satakeP_zero, map_one]
    exact (HeckePair.heckeIndicator_of_mem (by rw [pow_zero]; exact one_mem _) _).symm
  | 1 => by
    rw [satakeP_one, phi_X]
    exact (HeckePair.heckeIndicator_eq_of_mem_doubleCoset
      (by rw [pow_one]; exact localRepInf_mem_doubleCoset_diagPi ϖ hϖ0) _ _).symm
  | 2 => by
    rw [satakeP_two, map_sub, map_pow, phi_X, map_smul, phi_C, phi0_T, pow_two,
      heckeIndicator_diagPi_mul_self_impl ϖ hϖ0 hϖ (hfin _) (hfin _), zInd_one ϖ hϖ0 R₀ (hfin _),
      add_sub_cancel_right]
  | (k + 3) => by
    rw [satakeP_add_three, map_sub, map_mul, phi_X, map_smul, map_mul, phi_C, phi0_T,
      phi_satakeP (k + 2), phi_satakeP (k + 1),
      heckeIndicator_diagPi_mul_localRepInf_pow_impl ϖ hϖ0 hϖ k (hfin _) (hfin _) (hfin _),
      zInd_one_mul_heckeIndicator_localRepInf_pow ϖ hϖ0 R₀ hfin k, add_sub_cancel_right]

def cartanReindex : {p : ℤ × ℤ // p.1 ≤ p.2} ≃ ℤ × ℕ where
  toFun p := (p.1.1, (p.1.2 - p.1.1).toNat)
  invFun ab := ⟨(ab.1, ab.1 + (ab.2 : ℤ)), by simp⟩
  left_inv p := by
    obtain ⟨⟨m, n⟩, hmn⟩ := p
    apply Subtype.ext
    simp only [Prod.mk.injEq, true_and]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hmn)]
    ring
  right_inv ab := by
    obtain ⟨a, b⟩ := ab
    simp

include hϖ in

theorem phi_C_T_mul_satakeP (a : ℤ) (b : ℕ) :
    phi ϖ hϖ0 R₀ (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        (Polynomial.C (LaurentPolynomial.T a) * satakeP (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) b)
      = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ (a + (b : ℤ))) (hfin _) := by
  have hz := diagPi_mul_localRepInf_mem_center ϖ hϖ0
  rw [map_mul, phi_C, phi0_T, phi_satakeP ϖ hϖ0 hϖ R₀ hfin b]
  unfold zInd
  rw [HeckePair.heckeIndicator_center_mul_heckeIndicator (Subgroup.zpow_mem _ hz a) _ _ _ (hfin _)]
  refine HeckePair.heckeIndicator_congr ?_ _ _
  rw [(commute_diagPi_localRepInf ϖ hϖ0).mul_zpow, mul_assoc, ← zpow_natCast, ← _root_.zpow_add]

theorem exists_algEquiv_polynomial_laurentPolynomial_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ e : Polynomial (LaurentPolynomial R₀) ≃ₐ[R₀] HeckePair.HeckeAlgebra (integralSubgroup R K) R₀,
      e Polynomial.X = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ) ∧
      e (Polynomial.C (LaurentPolynomial.T 1))
        = HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS := by
  have hfin : ∀ g : GL (Fin 2) K,
      (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
        Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite :=
    fun g => finite_image_integralSubgroup_mul_singleton_impl hϖ g
  set q : R₀ := (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) with hq
  set φ := phi ϖ hϖ0 R₀ (finite_image_mul_diagPi ϖ hϖ0 hϖ) with hφ

  obtain ⟨cB, hcB⟩ := exists_basis_heckeIndicator_zpow_impl ϖ hϖ0 hϖ (R₀ := R₀) hfin
  set u := cB.reindex cartanReindex with hu_def
  have hu : ∀ ab : ℤ × ℕ, u ab = HeckePair.heckeIndicator R₀
      (diagPi ϖ hϖ0 ^ ab.1 * localRepInf ϖ hϖ0 ^ (ab.1 + (ab.2 : ℤ))) (hfin _) := by
    intro ab
    rw [hu_def, Module.Basis.reindex_apply, hcB]
    rfl

  set w : ℤ × ℕ → Polynomial (LaurentPolynomial R₀) :=
    fun ab => Polynomial.C (LaurentPolynomial.T ab.1) * satakeP q ab.2 with hw
  have hF1 : ∀ ab : ℤ × ℕ, φ (w ab) = u ab := fun ab => by
    rw [hu, hw]
    exact phi_C_T_mul_satakeP ϖ hϖ0 hϖ R₀ hfin ab.1 ab.2
  have hF2 : Submodule.span R₀ (Set.range w) = ⊤ := span_C_T_mul_satakeP q

  set ψ : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ →ₗ[R₀] Polynomial (LaurentPolynomial R₀) :=
    u.constr R₀ w with hψ
  have hψu : ∀ ab, ψ (u ab) = w ab := fun ab => u.constr_basis R₀ w ab
  have hleft : ∀ x, ψ (φ x) = x := by
    have hcomp : ψ ∘ₗ φ.toLinearMap = LinearMap.id := by
      refine LinearMap.ext_on hF2 ?_
      rintro _ ⟨ab, rfl⟩
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hF1, hψu, LinearMap.id_apply]
    intro x
    have := congrArg (fun F : Polynomial (LaurentPolynomial R₀) →ₗ[R₀] _ => F x) hcomp
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply] using this
  have hright : ∀ y, φ (ψ y) = y := by
    have hcomp : φ.toLinearMap ∘ₗ ψ = LinearMap.id := by
      refine u.ext fun ab => ?_
      rw [LinearMap.comp_apply, hψu, AlgHom.toLinearMap_apply, hF1, LinearMap.id_apply]
    intro y
    have := congrArg (fun F : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ →ₗ[R₀] _ => F y) hcomp
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply] using this
  have hbij : Function.Bijective φ :=
    ⟨fun x y hxy => by rw [← hleft x, ← hleft y, hxy], fun y => ⟨ψ y, hright y⟩⟩
  refine ⟨AlgEquiv.ofBijective φ hbij, ?_, ?_⟩
  · rw [AlgEquiv.ofBijective_apply, hφ, phi_X]
  · rw [AlgEquiv.ofBijective_apply, hφ, phi_C, phi0_T]
    exact zInd_one ϖ hϖ0 R₀ hS

end Assembly
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup det_map_algebraMap cartanDiag CartanRel exists_entry_eq_of_mem_integralSubgroup exists_cartanRel_cartanDiag cartanDiag_cartanRel_iff"
p2m_open "LocalGL2"

noncomputable section

section S5

def laurentEvalUnit (R₀ : Type*) [CommRing R₀] {A : Type*} [CommRing A] [Algebra R₀ A] (b : Aˣ) :
    LaurentPolynomial R₀ →ₐ[R₀] A :=
  AddMonoidAlgebra.lift R₀ A ℤ ((Units.coeHom A).comp (zpowersHom Aˣ b))

theorem laurentEvalUnit_T (R₀ : Type*) [CommRing R₀] {A : Type*} [CommRing A] [Algebra R₀ A]
    (b : Aˣ) (n : ℤ) :
    laurentEvalUnit R₀ b (LaurentPolynomial.T n) = ((b ^ n : Aˣ) : A) := by
  show AddMonoidAlgebra.lift R₀ A ℤ _ (AddMonoidAlgebra.single n 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem laurent_algHom_T_eq {R₀ : Type*} [CommRing R₀] {A : Type*} [CommRing A] [Algebra R₀ A]
    (g : LaurentPolynomial R₀ →ₐ[R₀] A) (b : Aˣ) (h1 : g (LaurentPolynomial.T 1) = (b : A))
    (n : ℤ) : g (LaurentPolynomial.T n) = ((b ^ n : Aˣ) : A) := by
  have hneg : g (LaurentPolynomial.T (-1)) = ((b⁻¹ : Aˣ) : A) := by
    apply Units.eq_inv_of_mul_eq_one_left
    rw [← h1, ← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, map_one]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [show (LaurentPolynomial.T (k : ℤ) : LaurentPolynomial R₀) = LaurentPolynomial.T 1 ^ k by
        rw [LaurentPolynomial.T_pow, mul_one], map_pow, h1, zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [show (LaurentPolynomial.T (-(k : ℤ)) : LaurentPolynomial R₀) = LaurentPolynomial.T (-1) ^ k by
        rw [LaurentPolynomial.T_pow, mul_neg, mul_one], map_pow, hneg, _root_.zpow_neg, zpow_natCast, ← inv_pow,
      Units.val_pow_eq_pow_val]

theorem existsUnique_algHom_heckeIndicator_eq_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    {A : Type*} [CommRing A] [Algebra R₀ A] (a : A) (b : Aˣ) :
    ∃! χ : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] A,
      χ (HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) = a ∧
      χ (HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) = (b : A) := by
  obtain ⟨e, heX, heS⟩ :=
    exists_algEquiv_polynomial_laurentPolynomial_impl ϖ hϖ0 hϖ (R₀ := R₀) hS

  have hχ₀X : Polynomial.aevalTower (laurentEvalUnit R₀ b) a Polynomial.X = a :=
    Polynomial.aevalTower_X _ _
  have hχ₀C : ∀ x : LaurentPolynomial R₀,
      Polynomial.aevalTower (laurentEvalUnit R₀ b) a (Polynomial.C x) = laurentEvalUnit R₀ b x :=
    fun x => Polynomial.aevalTower_C _ _ x
  refine ⟨(Polynomial.aevalTower (laurentEvalUnit R₀ b) a).comp e.symm.toAlgHom, ⟨?_, ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, ← heX, AlgEquiv.symm_apply_apply, hχ₀X]
  · rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, ← heS, AlgEquiv.symm_apply_apply, hχ₀C,
      laurentEvalUnit_T, zpow_one]
  · rintro χ' ⟨hT', hS'⟩

    have hg : ∀ n : ℤ, χ' (e (Polynomial.C (LaurentPolynomial.T n))) = ((b ^ n : Aˣ) : A) := by
      intro n
      have key := laurent_algHom_T_eq ((χ'.comp e.toAlgHom).comp Polynomial.CAlgHom) b ?_ n
      · exact key
      · show χ' (e (Polynomial.C (LaurentPolynomial.T 1))) = (b : A)
        rw [heS, hS']
    have hcomp : χ'.comp e.toAlgHom = Polynomial.aevalTower (laurentEvalUnit R₀ b) a := by
      refine Polynomial.algHom_ext' ?_ ?_
      · refine AddMonoidAlgebra.algHom_ext (fun n => ?_) (Subsingleton.elim _ _)
        show χ' (e (Polynomial.C (LaurentPolynomial.T n)))
          = Polynomial.aevalTower (laurentEvalUnit R₀ b) a (Polynomial.C (LaurentPolynomial.T n))
        rw [hg, hχ₀C, laurentEvalUnit_T]
      · rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, heX, hT', hχ₀X]
    apply AlgHom.ext
    intro h
    rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, ← hcomp, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      AlgEquiv.apply_symm_apply]

end S5
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2"

open scoped Pointwise
p2m_open "LocalGL2 P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.LocalGL2 HeckePair P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.HeckePair"

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    {A : Type*} [CommRing A] [Algebra R₀ A] (a : A) (b : Aˣ) :
    ∃! χ : HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] A,
      χ (heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) = a ∧
      χ (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) = (b : A) := by
  exact LocalGL2.existsUnique_algHom_heckeIndicator_eq_impl ϖ hϖ0 hϖ hS a b

end S_LocalGL2_existsUnique_algHom_heckeIndicator_eq
end P2MW
export P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq (solution)
