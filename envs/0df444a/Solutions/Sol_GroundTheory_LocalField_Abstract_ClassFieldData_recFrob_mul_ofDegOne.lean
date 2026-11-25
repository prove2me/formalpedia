-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.recFrob_mul_ofDegOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:48.563675+00:00
-- url     : https://prove2.me/submissions/e37d84a2-58de-4d1c-b855-b2201c30a9c6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_relInertiaDegree_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm_prime
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_prod_pow_div
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_eq_of_inf_ker_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_coe_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_field_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_inf_ker_prod
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_norm_eq_norm_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mk_norm_eq_recFrob
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_norm_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_fixedModule_frobeniusClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s : D.FrobeniusLift K) {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) :
    D.recFrob L hLK (s.mul (FrobeniusLift.ofDegOne hφK hdφ)) =
      D.recFrob L hLK s * D.recFrob L hLK (FrobeniusLift.ofDegOne hφK hdφ) := by
  classical
  set t := FrobeniusLift.ofDegOne (D := D) hφK hdφ with htdef
  set u := s.mul t with hudef
  set n := s.deg with hndef
  obtain ⟨π1, hπ1⟩ := D.exists_prime (s.field L hLK)
  obtain ⟨π2, hπ2⟩ := D.exists_prime (t.field L hLK)
  obtain ⟨π3, hπ3⟩ := D.exists_prime (u.field L hLK)
  rw [← D.mk_norm_eq_recFrob hLK hax s hπ1, ← D.mk_norm_eq_recFrob hLK hax t hπ2,
    ← D.mk_norm_eq_recFrob hLK hax u hπ3, ← QuotientGroup.mk_mul, QuotientGroup.eq]

  have hJ : ∀ (v : D.FrobeniusLift K) (y : A),
      y ∈ fixedModule A ((v.field L hLK : OpenSubgroup G) : Subgroup G) →
        y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun v y hy => fixedModule_anti le_frobeniusClosure hy
  have hφνJ : ∀ (ν : ℕ) (y : A), y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) →
      φ ^ ν • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun ν y hy => smul_mem_fixedModule_inf_ker hLK (K.pow_mem hφK ν) hy
  have hσπ1 : s.elt • (π1 : A) = π1 := π1.2 _ (s.elt_mem_field hLK)
  have hφπ2 : φ • (π2 : A) = π2 := π2.2 _ (t.elt_mem_field hLK)
  have hσφπ3 : (s.elt * φ) • (π3 : A) = π3 := π3.2 _ (u.elt_mem_field hLK)
  set T1 : A := ∏ ν : Fin n, φ ^ (ν : ℕ) • (π1 : A) with hT1
  set T3 : A := ∏ ν : Fin (n + 1), φ ^ (ν : ℕ) • (π3 : A) with hT3
  set x : A := T1 * φ ^ n • (π2 : A) / T3 with hxdef
  set a : A := (π1 : A) / π3 with hadef
  have hT1J : T1 ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.prod_mem _ fun ν _ => hφνJ ν _ (hJ s _ π1.2)
  have hT3J : T3 ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.prod_mem _ fun ν _ => hφνJ ν _ (hJ u _ π3.2)
  have hπ2J : φ ^ n • (π2 : A) ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    hφνJ n _ (hJ t _ π2.2)
  have hxJ : x ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.div_mem _ (Subgroup.mul_mem _ hT1J hπ2J) hT3J

  have hNprod : ∀ (m : ℕ) (y : A) (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)),
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨∏ ν : Fin m, φ ^ (ν : ℕ) • y, Subgroup.prod_mem _ fun ν _ => hφνJ ν y hy⟩ : A) =
        ∏ ν : Fin m, φ ^ (ν : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) := by
    intro m y hy
    rw [coe_norm_inf_ker_prod Finset.univ _ (fun ν : Fin m => hφνJ (ν : ℕ) y hy)]
    refine Finset.prod_congr rfl fun ν _ => ?_
    rw [smul_norm_inf_ker hLK (K.pow_mem hφK ν)]
  have hN1 : (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨T1, hT1J⟩ : A) := by
    exact (coe_norm_field_eq hLK s hφK hdφ π1).trans (hNprod _ _ _).symm
  have hN3 : (norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨T3, hT3J⟩ : A) := by
    exact (coe_norm_field_eq hLK u hφK hdφ π3).trans (hNprod _ _ _).symm
  have hN2K := (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2).2
  have hN2 : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨φ ^ n • (π2 : A), hπ2J⟩ : A) := by
    have h0 : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨(π2 : A), hJ t _ π2.2⟩ : A) := by
      have h0' : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
          ∏ ν : Fin 1, φ ^ (ν : ℕ) • (norm A ((K : Subgroup G) ⊓ D.deg.ker)
            ((L : Subgroup G) ⊓ D.deg.ker) ⟨(π2 : A), hJ t _ π2.2⟩ : A) :=
        coe_norm_field_eq hLK t hφK hdφ π2
      rw [Fin.prod_univ_one] at h0'
      simpa using h0'
    calc (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A)
        = φ ^ n • (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) :=
          (hN2K _ (K.pow_mem hφK n)).symm
      _ = φ ^ n • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
            ⟨(π2 : A), hJ t _ π2.2⟩ : A) := by rw [h0]
      _ = _ := smul_norm_inf_ker hLK (K.pow_mem hφK n) _
  have hNx : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x, hxJ⟩ : A) =
      (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 : A) *
        norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 /
          norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 := by
    rw [hN1, hN2, hN3]
    have e : (⟨x, hxJ⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨T1, hT1J⟩ * ⟨φ ^ n • (π2 : A), hπ2J⟩ / ⟨T3, hT3J⟩ := rfl
    rw [e, map_div, map_mul]
    rfl

  have hst : ∀ y : A, IsOpen (MulAction.stabilizer G y : Set G) :=
    fun y => IsDiscreteModule.isOpen_stabilizer y
  have hopen : IsOpen ((L : Set G) ∩ (MulAction.stabilizer G (π1 : A) : Set G) ∩
      (MulAction.stabilizer G (π2 : A) : Set G) ∩ (MulAction.stabilizer G (π3 : A) : Set G)) :=
    ((L.isOpen.inter (hst _)).inter (hst _)).inter (hst _)
  have hone : (1 : G) ∈ (L : Set G) ∩ (MulAction.stabilizer G (π1 : A) : Set G) ∩
      (MulAction.stabilizer G (π2 : A) : Set G) ∩ (MulAction.stabilizer G (π3 : A) : Set G) :=
    ⟨⟨⟨L.one_mem, Subgroup.one_mem _⟩, Subgroup.one_mem _⟩, Subgroup.one_mem _⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  have : Finite (G ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  set D0 := orderOf (φ : G ⧸ U.toSubgroup) with hD0def
  have hD0 : 0 < D0 := orderOf_pos _
  have hφD0U : φ ^ D0 ∈ U.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hD0def, pow_orderOf_eq_one]
  obtain ⟨⟨⟨hψL, hψ1⟩, hψ2⟩, hψ3⟩ := hU hφD0U
  have hψπ1 : φ ^ D0 • (π1 : A) = π1 := MulAction.mem_stabilizer_iff.1 hψ1
  have hψπ2 : φ ^ D0 • (π2 : A) = π2 := MulAction.mem_stabilizer_iff.1 hψ2
  have hψπ3 : φ ^ D0 • (π3 : A) = π3 := MulAction.mem_stabilizer_iff.1 hψ3
  set g := (L : Subgroup G).relIndex K with hgdef
  have hg : 0 < g := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
    (H := (L : Subgroup G).subgroupOf K))
  set s1 := powLift hφK hdφ D0 hD0 with hs1
  set s2 := powLift hφK hdφ (g * D0) (Nat.mul_pos hg hD0) with hs2
  have hfix : ∀ (ν : ℕ) (y : A), φ ^ D0 • y = y → φ ^ D0 • φ ^ ν • y = φ ^ ν • y := by
    intro ν y hy
    rw [smul_smul, ← pow_add, add_comm, pow_add, mul_smul, hy]
  have hT1ψ : φ ^ D0 • T1 = T1 := by
    rw [hT1, Finset.smul_prod']
    exact Finset.prod_congr rfl fun ν _ => hfix ν _ hψπ1
  have hT3ψ : φ ^ D0 • T3 = T3 := by
    rw [hT3, Finset.smul_prod']
    exact Finset.prod_congr rfl fun ν _ => hfix ν _ hψπ3
  have hxP : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    refine ⟨hxJ, ?_⟩
    show φ ^ D0 • x = x
    rw [hxdef, smul_div', smul_mul', hT1ψ, hfix n _ hψπ2, hT3ψ]
  have hπ1P : (π1 : A) ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    exact ⟨hJ s _ π1.2, hψπ1⟩
  have hπ3P : (π3 : A) ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    exact ⟨hJ u _ π3.2, hψπ3⟩
  have haP : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.div_mem _ hπ1P hπ3P

  have hπP : ∀ (v : D.FrobeniusLift K) (y : A)
      (hy : y ∈ fixedModule A ((v.field L hLK : OpenSubgroup G) : Subgroup G))
      (hyP : y ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)),
      D.valuation (s1.field L hLK) ⟨y, hyP⟩ = D.valuation (v.field L hLK) ⟨y, hy⟩ :=
    fun v y hy hyP => valuation_eq_of_inf_ker_eq
      ((v.field_inf_ker hLK).trans (s1.field_inf_ker hLK).symm) hy hyP
  have hau : D.valuation (s1.field L hLK) ⟨a, haP⟩ = 1 := by
    have e : (⟨a, haP⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) =
        ⟨(π1 : A), hπ1P⟩ / ⟨(π3 : A), hπ3P⟩ := rfl
    rw [e, map_div, hπP s _ π1.2 hπ1P, hπP u _ π3.2 hπ3P]
    simp [hπ1, hπ3]
  set N : fixedModule A (K : Subgroup G) :=
    norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 *
      norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 /
        norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 with hNdef
  have hNcoe : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x, hxJ⟩ : A) =
      (N : A) := by
    rw [hNx]
    rfl
  have hvN : D.valuation K N = 1 := by
    rw [hNdef, map_div, map_mul, valuation_norm_prime hLK s hπ1, valuation_norm_prime hLK t hπ2,
      valuation_norm_prime hLK u hπ3, ← ofAdd_add, ← ofAdd_sub]
    show Multiplicative.ofAdd ((s.deg : ℤ̂) + ((1 : ℕ) : ℤ̂) - ((s.deg + 1 : ℕ) : ℤ̂)) = 1
    push_cast
    simp
  have hxu : D.valuation (s1.field L hLK) ⟨x, hxP⟩ = 1 := by
    have hNP : norm A (K : Subgroup G) ((s1.field L hLK : OpenSubgroup G) : Subgroup G) ⟨x, hxP⟩ =
        N ^ D0 := by
      apply Subtype.ext
      rw [coe_norm_field_eq hLK s1 hφK hdφ ⟨x, hxP⟩, SubmonoidClass.coe_pow]
      have h' : ∀ m : Fin s1.deg, φ ^ (m : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
            ⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ : A) = (N : A) := by
        intro m
        rw [show (⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ :
            fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ⟨x, hxJ⟩ from rfl, hNcoe]
        exact N.2 _ (K.pow_mem hφK _)
      rw [Finset.prod_congr rfl fun m _ => h' m, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rfl
    have hv := D.valuation_norm (s1.field_le hLK) ⟨x, hxP⟩
    rw [hNP, map_pow, hvN, one_pow, FrobeniusLift.relInertiaDegree_field] at hv
    exact (ProfiniteInteger.pow_left_inj (n := s1.deg) hD0.ne').1 (by rw [one_pow]; exact hv.symm)

  set δ : G := φ ^ n * s.elt⁻¹ with hδdef
  have hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine ⟨K.mul_mem (K.pow_mem hφK n) (K.inv_mem s.mem), ?_⟩
    show D.deg (φ ^ n * s.elt⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hdφ, s.deg_eq, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
    rw [hndef]
    push_cast
    rw [nsmul_eq_mul, add_neg_cancel, ofAdd_zero]
  have hδπ1 : δ • (π1 : A) = φ ^ n • (π1 : A) := by
    rw [hδdef, mul_smul, inv_smul_eq_iff.2 hσπ1.symm]
  have hφπ3 : φ • (π3 : A) = s.elt⁻¹ • (π3 : A) := by
    rw [eq_inv_smul_iff, ← mul_smul]
    exact hσφπ3
  have hδπ3 : δ • (π3 : A) = φ ^ (n + 1) • (π3 : A) := by
    rw [hδdef, mul_smul, ← hφπ3, ← mul_smul, ← pow_succ]
  have e2 : φ • φ ^ n • (π2 : A) = φ ^ n • (π2 : A) := by
    rw [smul_smul, ← pow_succ', pow_succ, mul_smul, hφπ2]
  have L1 : φ • x / x = (φ • T1 / T1) / (φ • T3 / T3) := by
    rw [hxdef, smul_div', smul_mul', e2, div_div_div_comm, mul_div_mul_comm, div_self', mul_one]
  have R1 : δ • a / a = (φ ^ n • (π1 : A) / π1) / (φ ^ (n + 1) • (π3 : A) / π3) := by
    rw [hadef, smul_div', hδπ1, hδπ3, div_div_div_comm]
  have hrel : φ • x / x = δ • a / a := by
    rw [L1, R1, hT1, hT3, smul_prod_pow_div, smul_prod_pow_div]

  obtain ⟨b, hb⟩ := exists_norm_eq_norm_inf_ker hLK hax hφK hdφ s1 s2 rfl hψL
    (by show φ ^ (g * D0) = (φ ^ D0) ^ g; rw [mul_comm, pow_mul]) rfl hxP haP hxu hau hδ hrel
  refine ⟨b, Subtype.ext ?_⟩
  rw [hb, show (⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ :
      fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ⟨x, hxJ⟩ from rfl, hNcoe, hNdef]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_div]
  rw [div_eq_inv_mul]
end GroundTheory.LocalField.Abstract.ClassFieldData
