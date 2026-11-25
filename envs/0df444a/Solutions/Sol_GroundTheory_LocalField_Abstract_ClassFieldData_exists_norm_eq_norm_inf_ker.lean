-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.exists_norm_eq_norm_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:04.35821+00:00
-- url     : https://prove2.me/submissions/cde291f3-1142-4a89-b114-38febdafe335

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_fixedModule_of_smul_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_norm_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_smul_comm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_mem_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_normal_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_prod_range_prod_range_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_field_le_field_of_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_field_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_inf_ker_prod
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_inf_ker_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_relDeg_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_field_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_units_eq_smul_div
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_units_eq_map_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_of_mem
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
import Theorems.Thm_GroundTheory_LocalField_Abstract_frobeniusClosure_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_smul
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
    {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (s1 s2 : D.FrobeniusLift K) (h1 : s1.elt = φ ^ s1.deg) (hψL : s1.elt ∈ (L : Subgroup G))
    (h2 : s2.elt = s1.elt ^ ((L : Subgroup G).relIndex K))
    (hdeg : s2.deg = (L : Subgroup G).relIndex K * s1.deg)
    {x a : A} (hx : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (ha : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (hxu : D.valuation (s1.field L hLK) ⟨x, hx⟩ = 1)
    (hau : D.valuation (s1.field L hLK) ⟨a, ha⟩ = 1)
    {δ : G} (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hrel : φ • x / x = δ • a / a) :
    ∃ b : fixedModule A (L : Subgroup G),
      (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ := by
  classical
  set g := (L : Subgroup G).relIndex K with hgdef
  have hg : 0 < g := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
    (H := (L : Subgroup G).subgroupOf K))
  have hP'P : s2.field L hLK ≤ s1.field L hLK := field_le_field_of_pow hLK s1 s2 g h2
  have hP'L : s2.field L hLK ≤ L := fun y hy =>
    frobeniusClosure_le L.isClosed (by rw [h2]; exact L.pow_mem hψL g) inf_le_left hy
  have hu : ((s1.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker ≤ s2.field L hLK :=
    fun y hy => le_frobeniusClosure ((s1.field_inf_ker hLK).le hy)
  have hT := coe_norm_field_field hLK s1 s2 g hg h2 hdeg
  have hrelψ := s1.relDeg_field hLK

  have hφJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hφK hy
  have hφjJ : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ ^ j • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun j y hy => smul_mem_fixedModule_inf_ker hLK (K.pow_mem hφK j) hy
  have hδJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      δ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hδ.1 hy
  have hcommφ : ∀ (i j : ℕ) (y : A), s1.elt ^ i • φ ^ j • y = φ ^ j • s1.elt ^ i • y := by
    intro i j y
    have hc : Commute (s1.elt ^ i) (φ ^ j) := by
      rw [h1]
      exact (((Commute.refl φ).pow_left _).pow_left _).pow_right _
    rw [smul_smul, smul_smul, hc.eq]
  have hcommδ : ∀ (i : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      s1.elt ^ i • δ • y = δ • s1.elt ^ i • y :=
    fun i y hy => (smul_smul_comm hLK hδ (L.pow_mem hψL i) hy).symm
  have hφP' : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      φ ^ j • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro j y hy
    refine smul_mem_field hLK s2 (hφjJ j) (fun z _ => ?_) hy
    rw [h2]
    exact hcommφ g j z
  have hδP' : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      δ • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro y hy
    refine smul_mem_field hLK s2 hδJ (fun z hz => ?_) hy
    rw [h2]
    exact hcommδ g z hz
  have hP'J : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => fixedModule_anti le_frobeniusClosure hy

  have hxU : (⟨x, hx⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hxu
  rw [D.units_eq_map_norm hax hP'P hu] at hxU
  obtain ⟨x'', -, hx''⟩ := hxU
  have haU : (⟨a, ha⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hau
  rw [D.units_eq_map_norm hax hP'P hu] at haU
  obtain ⟨c, -, hc⟩ := haU
  have hxN : x = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) := by
    rw [← hT, hx'']
  have haN : a = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (c : A) := by
    rw [← hT, hc]

  have hφx'' : φ • (x'' : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    simpa using hφP' 1 _ x''.2
  have hδc : δ • (c : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    hδP' _ c.2
  set y' : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    ⟨φ • (x'' : A), hφx''⟩ / x'' / (⟨δ • (c : A), hδc⟩ / c) with hy'def
  have hNy' : norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) y' = 1 := by
    apply Subtype.ext
    rw [hT]
    simp only [hy'def, Subgroup.coe_div, OneMemClass.coe_one, smul_div', Finset.prod_div_distrib]
    have e1 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • φ • (x'' : A) = φ • x := by
      rw [hxN, Finset.smul_prod']
      refine Finset.prod_congr rfl fun i _ => ?_
      simpa using hcommφ i 1 (x'' : A)
    have e2 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • δ • (c : A) = δ • a := by
      rw [haN, Finset.smul_prod']
      exact Finset.prod_congr rfl fun i _ => hcommδ i _ (hP'J _ c.2)
    rw [e1, e2, ← hxN, ← haN, hrel, div_self']
  obtain ⟨b, -, hb⟩ := D.exists_units_eq_smul_div hax hP'P hu hrelψ hNy'

  set Tb : A := ∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) with hTbdef
  have hTbP' : Tb ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.prod_mem _ fun j _ => hφP' j _ b.2
  have htele : φ • Tb / Tb = s1.elt • (b : A) / b := by
    rw [hTbdef, Finset.smul_prod', h1]
    simp only [Fin.prod_univ_eq_prod_range (fun j => φ • φ ^ j • (b : A)),
      Fin.prod_univ_eq_prod_range (fun j => φ ^ j • (b : A))]
    have hs := Finset.prod_range_succ (fun j => φ ^ j • (b : A)) s1.deg
    have hs' := Finset.prod_range_succ' (fun j => φ ^ j • (b : A)) s1.deg
    simp only [pow_zero, one_smul] at hs'
    have : ∏ j ∈ Finset.range s1.deg, φ • φ ^ j • (b : A) =
        ∏ j ∈ Finset.range s1.deg, φ ^ (j + 1) • (b : A) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [smul_smul, ← pow_succ']
    rw [this, div_eq_div_iff_mul_eq_mul, ← hs', hs, mul_comm]
  set x' : A := (x'' : A) / Tb with hx'def
  have hx'P' : x' ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.div_mem _ x''.2 hTbP'
  have hx'J := hP'J _ hx'P'
  have hrel' : φ • x' = x' * (δ • (c : A) / c) := by
    have hy'v : (y' : A) = φ • (x'' : A) / x'' / (δ • (c : A) / c) := by
      simp [hy'def]
    have e : φ • (x'' : A) / x'' = (s1.elt • (b : A) / b) * (δ • (c : A) / c) := by
      rw [← hb, hy'v, div_mul_cancel]
    have e2 : φ • Tb = Tb * (s1.elt • (b : A) / b) := by
      rw [← htele, mul_div_cancel]
    rw [hx'def, smul_div', e2]
    have e3 : φ • (x'' : A) = x'' * ((s1.elt • (b : A) / b) * (δ • (c : A) / c)) := by
      rw [← e, mul_div_cancel]
    rw [e3, mul_div_mul_comm, mul_div_cancel_left]

  set w : A := (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x', hx'J⟩ : A)
    with hwdef
  have := normal_inf_ker (D := D) hLK
  have hcJ := hP'J _ c.2
  have hwφ : φ • w = w := by
    rw [hwdef, smul_norm_inf_ker hLK hφK]
    have e : (⟨φ • x', smul_mem_fixedModule_inf_ker hLK hφK hx'J⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨x', hx'J⟩ * (⟨δ • (c : A), hδJ _ hcJ⟩ / ⟨c, hcJ⟩) := by
      ext
      simp [hrel']
    rw [e, map_mul, map_div, norm_smul (K := (K : Subgroup G) ⊓ D.deg.ker)
      (L := (L : Subgroup G) ⊓ D.deg.ker) ⟨δ, hδ⟩ ⟨(c : A), hcJ⟩ (hδJ _ hcJ), div_self', mul_one]
  have hwK : w ∈ fixedModule A (K : Subgroup G) :=
    mem_fixedModule_of_smul_eq K hφK hdφ (norm _ _ _ _).2 hwφ

  have hbJ := hP'J _ b.2
  have hNb := coe_norm_field_eq hLK s2 hφK hdφ b
  refine ⟨⟨w, fixedModule_anti hLK hwK⟩ * norm A (L : Subgroup G)
    ((s2.field L hLK : OpenSubgroup G) : Subgroup G) b, ?_⟩
  have hψK : ∀ i : ℕ, s1.elt ^ i ∈ (K : Subgroup G) := fun i => K.pow_mem s1.mem i
  have hx''eq : (x'' : A) = x' * Tb := by rw [hx'def, div_mul_cancel]
  have hTbJ := hP'J _ hTbP'
  have hNTb : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) =
      ∏ j : Fin s1.deg, φ ^ (j : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨b, hbJ⟩ : A) := by
    have hmemj : ∀ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun j => hφjJ j _ hbJ
    rw [show (⟨Tb, hTbJ⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A), Subgroup.prod_mem _ fun j _ => hmemj j⟩ from rfl,
      coe_norm_inf_ker_prod Finset.univ _ hmemj]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_norm_inf_ker hLK (K.pow_mem hφK j)]
  have hNx : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ : A) =
      w ^ g * ∏ i : Fin g, s1.elt ^ (i : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
    have hmemi : ∀ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) ∈
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun i => smul_mem_fixedModule_inf_ker hLK (hψK i) (hP'J _ x''.2)
    have e1 : (⟨x, fixedModule_anti le_frobeniusClosure hx⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A), Subgroup.prod_mem _ fun i _ => hmemi i⟩ :=
      Subtype.ext hxN
    rw [e1, coe_norm_inf_ker_prod Finset.univ _ hmemi]
    have e2 : ∀ i : Fin g, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨s1.elt ^ (i : ℕ) • (x'' : A), hmemi i⟩ : A) =
        w * s1.elt ^ (i : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
      intro i
      have h3 := smul_norm_inf_ker hLK (hψK i) ⟨(x'' : A), hP'J _ x''.2⟩
      rw [← h3]
      have e4 : (⟨(x'' : A), hP'J _ x''.2⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
          ⟨x' * Tb, Subgroup.mul_mem _ hx'J hTbJ⟩ := Subtype.ext hx''eq
      rw [e4, coe_norm_inf_ker_mul hx'J hTbJ, smul_mul', ← hwdef, hwK _ (hψK i)]
    rw [Finset.prod_congr rfl fun i _ => e2 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [map_mul, Subgroup.coe_mul, coe_norm_of_mem hLK hwK,
    norm_norm (fun y hy => hP'L hy) (fun y hy => hLK hy) b, hNb, hNx, hNTb]
  congr 1
  simp_rw [Finset.smul_prod', smul_smul, h1, ← pow_mul, ← pow_add]
  rw [Fin.prod_univ_eq_prod_range (fun m => φ ^ m • _) s2.deg, hdeg,
    ← prod_range_prod_range_eq _ g s1.deg]
  simp only [Finset.prod_range]
end GroundTheory.LocalField.Abstract.ClassFieldData
